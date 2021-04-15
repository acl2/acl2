(|(logand y x)| (134 2 (:DEFINITION BINARY-LOGAND))
                (36 4 (:REWRITE |(floor x 2)| . 1))
                (24 4 (:DEFINITION EVENP))
                (18 18
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (18 6 (:REWRITE |(+ y x)|))
                (16 16 (:REWRITE REDUCE-INTEGERP-+))
                (16 16 (:REWRITE INTEGERP-MINUS-X))
                (16 16 (:META META-INTEGERP-CORRECT))
                (8 4 (:REWRITE |(+ 0 x)|))
                (8 4 (:REWRITE |(* y x)|))
                (6 6
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (6 6 (:REWRITE NORMALIZE-ADDENDS))
                (4 4 (:REWRITE ZIP-OPEN))
                (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (4 4
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (4 4
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (4 4
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (4 4
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (4 4
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (4 4 (:REWRITE |(floor x 2)| . 2))
                (4 4 (:REWRITE |(equal c (/ x))|))
                (4 4 (:REWRITE |(equal (/ x) c)|))
                (4 4 (:REWRITE |(equal (/ x) (/ y))|))
                (4 4 (:REWRITE |(equal (- x) c)|))
                (4 4 (:REWRITE |(equal (- x) (- y))|)))
(|(logand (logand x y) z)|)
(|(logand y x z)|)
(|(logand c d x)|)
(LOGAND-0-X (2 2 (:REWRITE REDUCE-INTEGERP-+))
            (2 2 (:REWRITE INTEGERP-MINUS-X))
            (2 2 (:META META-INTEGERP-CORRECT))
            (1 1 (:REWRITE DEFAULT-LOGAND-1)))
(|(logand 1 x)| (5 5
                   (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (4 4 (:REWRITE REDUCE-INTEGERP-+))
                (4 4 (:REWRITE INTEGERP-MINUS-X))
                (4 4 (:META META-INTEGERP-CORRECT))
                (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (3 3
                   (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                (3 3
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (3 3
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                (3 3
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                (3 3
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (3 3 (:REWRITE |(equal c (/ x))|))
                (3 3 (:REWRITE |(equal (if a b c) x)|))
                (3 3 (:REWRITE |(equal (/ x) c)|))
                (3 3 (:REWRITE |(equal (/ x) (/ y))|))
                (3 3 (:REWRITE |(equal (- x) c)|))
                (3 3 (:REWRITE |(equal (- x) (- y))|))
                (1 1 (:REWRITE ZIP-OPEN))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (1 1
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (1 1 (:REWRITE NORMALIZE-ADDENDS))
                (1 1 (:REWRITE DEFAULT-LOGAND-2))
                (1 1 (:REWRITE DEFAULT-LOGAND-1))
                (1 1 (:REWRITE |(floor x 2)| . 2)))
(LOGAND--1-X (1 1 (:REWRITE ZIP-OPEN))
             (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (1 1
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (1 1
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1
                (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (1 1
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (1 1 (:REWRITE DEFAULT-LOGAND-2))
             (1 1 (:REWRITE DEFAULT-LOGAND-1))
             (1 1 (:REWRITE |(equal x (if a b c))|))
             (1 1 (:REWRITE |(equal c (/ x))|))
             (1 1 (:REWRITE |(equal (if a b c) x)|))
             (1 1 (:REWRITE |(equal (/ x) c)|))
             (1 1 (:REWRITE |(equal (/ x) (/ y))|))
             (1 1 (:REWRITE |(equal (- x) c)|))
             (1 1 (:REWRITE |(equal (- x) (- y))|))
             (1 1 (:META META-INTEGERP-CORRECT)))
(LOGAND-X-X (61 61
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (41 41 (:REWRITE REDUCE-INTEGERP-+))
            (41 41 (:REWRITE INTEGERP-MINUS-X))
            (41 41 (:META META-INTEGERP-CORRECT))
            (36 36
                (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
            (35 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (35 23
                (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (34 34
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (34 34 (:REWRITE NORMALIZE-ADDENDS))
            (23 23
                (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (23 23
                (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (23 23
                (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (23 23 (:REWRITE |(equal c (/ x))|))
            (23 23 (:REWRITE |(equal (/ x) c)|))
            (23 23 (:REWRITE |(equal (/ x) (/ y))|))
            (23 23 (:REWRITE |(equal (- x) c)|))
            (23 23 (:REWRITE |(equal (- x) (- y))|))
            (23 15
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (21 21 (:REWRITE |(floor x 2)| . 2))
            (12 12 (:REWRITE DEFAULT-LOGAND-2))
            (12 12 (:REWRITE DEFAULT-LOGAND-1))
            (12 8
                (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
            (12 8
                (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
            (11 11 (:REWRITE ZIP-OPEN))
            (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
            (1 1
               (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
            (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(LOGAND-BOUNDS-POS
     (946 946
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (610 562 (:REWRITE REDUCE-INTEGERP-+))
     (562 562 (:REWRITE INTEGERP-MINUS-X))
     (562 562 (:META META-INTEGERP-CORRECT))
     (557 385 (:REWRITE DEFAULT-LESS-THAN-2))
     (492 353 (:REWRITE SIMPLIFY-SUMS-<))
     (492 353
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (486 486
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (486 486 (:REWRITE NORMALIZE-ADDENDS))
     (411 195 (:REWRITE ZIP-OPEN))
     (385 385 (:REWRITE THE-FLOOR-ABOVE))
     (363 359
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (363 359
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (357 355 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (355 355
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (355 355 (:REWRITE INTEGERP-<-CONSTANT))
     (355 355 (:REWRITE CONSTANT-<-INTEGERP))
     (355 355
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (355 355
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (355 355
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (355 355
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (355 355 (:REWRITE |(< c (- x))|))
     (355 355
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (355 355
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (355 355
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (355 355
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (355 355 (:REWRITE |(< (/ x) (/ y))|))
     (355 355 (:REWRITE |(< (- x) c)|))
     (355 355 (:REWRITE |(< (- x) (- y))|))
     (252 252
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (220 160 (:REWRITE DEFAULT-LOGAND-2))
     (205 205 (:REWRITE |(floor x 2)| . 2))
     (192 96 (:REWRITE |(* c (* d x))|))
     (172 172 (:REWRITE |(< (* x y) 0)|))
     (168 168
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (168 168
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (168 168 (:REWRITE |(< (/ x) 0)|))
     (160 160 (:REWRITE DEFAULT-LOGAND-1))
     (117 117 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (117 117
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (117 117
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (117 117
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (117 117
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (117 117 (:REWRITE |(equal c (/ x))|))
     (117 117 (:REWRITE |(equal (/ x) c)|))
     (117 117 (:REWRITE |(equal (/ x) (/ y))|))
     (117 117 (:REWRITE |(equal (- x) c)|))
     (117 117 (:REWRITE |(equal (- x) (- y))|))
     (89 89
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (76 56
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (76 56
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (76 56
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (60 12 (:REWRITE |(* (* x y) z)|))
     (29 29 (:REWRITE |(< y (+ (- c) x))|))
     (29 29 (:REWRITE |(< x (+ c/d y))|))
     (28 28
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (28 28
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
     (15 15 (:REWRITE |(< (+ (- c) x) y)|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS)))
(LOGAND-BOUNDS-NEG
     (1573 313 (:REWRITE THE-FLOOR-ABOVE))
     (1481 75 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (1477 75 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (1085 273
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (752 752
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (556 112 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (541 493 (:REWRITE REDUCE-INTEGERP-+))
     (520 104
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (500 388 (:REWRITE NORMALIZE-ADDENDS))
     (493 493 (:REWRITE INTEGERP-MINUS-X))
     (493 493 (:META META-INTEGERP-CORRECT))
     (405 285 (:REWRITE DEFAULT-LESS-THAN-2))
     (360 360
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (344 241 (:REWRITE SIMPLIFY-SUMS-<))
     (344 241
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (316 56 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (316 56 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (287 243 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (256 128 (:REWRITE |arith (* y x)|))
     (245 245
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (245 245
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (243 243
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (243 243 (:REWRITE INTEGERP-<-CONSTANT))
     (243 243 (:REWRITE CONSTANT-<-INTEGERP))
     (243 243
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
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
     (207 207
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (192 96 (:REWRITE |(* c (* d x))|))
     (180 180
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (178 166
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (166 166
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (163 163 (:REWRITE |(< (* x y) 0)|))
     (162 162 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (162 162
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (162 162
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (162 162 (:REWRITE |(equal c (/ x))|))
     (162 162 (:REWRITE |(equal (/ x) c)|))
     (162 162 (:REWRITE |(equal (/ x) (/ y))|))
     (162 162 (:REWRITE |(equal (- x) c)|))
     (162 162 (:REWRITE |(equal (- x) (- y))|))
     (149 149 (:REWRITE |(floor x 2)| . 2))
     (148 88 (:REWRITE DEFAULT-LOGAND-2))
     (135 135
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (135 135
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (135 135 (:REWRITE |(< (/ x) 0)|))
     (122 122
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (112 56 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (101 101 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (100 12
          (:REWRITE |(not (equal (* (/ x) y) -1))|))
     (96 8 (:REWRITE |(equal (* (/ x) y) -1)|))
     (88 88 (:REWRITE DEFAULT-LOGAND-1))
     (72 12 (:REWRITE ZIP-OPEN))
     (64 44
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (64 44
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (64 44
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (60 12 (:REWRITE |(* (* x y) z)|))
     (56 28 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (46 26 (:REWRITE LOGAND-BOUNDS-POS . 2))
     (40 40 (:TYPE-PRESCRIPTION ABS))
     (40 40
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (40 40
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (36 12 (:REWRITE |(+ c (+ d x))|))
     (32 32 (:REWRITE LOGAND-BOUNDS-POS . 1))
     (28 28
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (28 28 (:REWRITE |(+ x (- x))|))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (9 9 (:REWRITE |(< y (+ (- c) x))|))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (9 9 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(|(< (logand x y) 0)|
     (20176 64 (:REWRITE |(* 1/2 (floor x y))| . 1))
     (11902 259 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (8835 259 (:REWRITE FLOOR-CANCEL-*-CONST))
     (8137 769 (:REWRITE |(< c (- x))|))
     (2240 16 (:REWRITE FLOOR-X-Y-=--1 . 1))
     (1938 259 (:REWRITE FLOOR-=-X/Y . 3))
     (1938 259 (:REWRITE FLOOR-=-X/Y . 2))
     (1489 1489
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1360 64 (:REWRITE UGLY-UNHIDE-HACK-THM-1))
     (1280 256 (:REWRITE |(* (* x y) z)|))
     (1036 769
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1036 769
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (890 890 (:REWRITE REDUCE-INTEGERP-+))
     (890 890 (:REWRITE INTEGERP-MINUS-X))
     (890 890 (:META META-INTEGERP-CORRECT))
     (777 777 (:REWRITE DEFAULT-LESS-THAN-2))
     (769 769
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (769 769
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (769 769
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (769 769
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (769 769
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (769 769
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (769 769
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (769 769
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (769 769
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (769 769 (:REWRITE |(< (/ x) (/ y))|))
     (769 769 (:REWRITE |(< (- x) (- y))|))
     (640 256 (:REWRITE |(- (* c x))|))
     (542 542 (:TYPE-PRESCRIPTION ABS))
     (512 256 (:REWRITE |(* c (* d x))|))
     (501 478
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (478 478 (:REWRITE SIMPLIFY-SUMS-<))
     (478 478
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (478 478 (:REWRITE INTEGERP-<-CONSTANT))
     (478 478 (:REWRITE CONSTANT-<-INTEGERP))
     (478 478 (:REWRITE |(< (- x) c)|))
     (453 438
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (448 448 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (369 89 (:REWRITE ZIP-OPEN))
     (273 234 (:REWRITE |(floor x 2)| . 2))
     (259 259 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (259 259 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (250 154
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (239 239
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (193 129 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (189 117
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (187 187
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (187 187
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (187 187 (:REWRITE |(< (/ x) 0)|))
     (187 187 (:REWRITE |(< (* x y) 0)|))
     (176 32 (:REWRITE FLOOR-=-X/Y . 4))
     (163 163 (:REWRITE |(- (- x))|))
     (161 129
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (146 146
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (146 146 (:REWRITE |(equal c (/ x))|))
     (146 146 (:REWRITE |(equal (/ x) c)|))
     (146 146 (:REWRITE |(equal (/ x) (/ y))|))
     (146 146 (:REWRITE |(equal (- x) c)|))
     (146 146 (:REWRITE |(equal (- x) (- y))|))
     (144 16 (:REWRITE |(+ x (if a b c))|))
     (131 131
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (131 131
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (131 131 (:REWRITE |(floor x (- y))| . 2))
     (131 131 (:REWRITE |(floor x (- y))| . 1))
     (131 131
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (131 131
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (131 131 (:REWRITE |(floor (- x) y)| . 2))
     (131 131 (:REWRITE |(floor (- x) y)| . 1))
     (131 131
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (131 131
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (128 128 (:REWRITE |(* (- x) y)|))
     (108 108
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (96 16 (:REWRITE |(+ y (+ x z))|))
     (79 10 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (64 64 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
     (64 64 (:REWRITE |(* 1/2 (floor x y))| . 3))
     (64 64 (:REWRITE |(* 1/2 (floor x y))| . 2))
     (48 40
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (48 40
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (48 40
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (48 16 (:REWRITE |(+ c (+ d x))|))
     (45 10 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (16 16
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (12 12
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (11 11
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|)))
(|(logand (* 2 x) (* 2 y))|
     (3391 251
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3264 80 (:REWRITE |(< (+ c/d x) y)|))
     (2779 191
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1590 32 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (1590 32 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (1008 36
           (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (852 852
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (838 838
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (476 476
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (476 476 (:REWRITE NORMALIZE-ADDENDS))
     (448 16
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (295 295 (:REWRITE THE-FLOOR-ABOVE))
     (295 295 (:REWRITE DEFAULT-LESS-THAN-2))
     (276 196 (:REWRITE REDUCE-INTEGERP-+))
     (266 162 (:REWRITE |(equal (- x) c)|))
     (243 191
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (242 154
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (242 154
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (218 154 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (196 196 (:REWRITE INTEGERP-MINUS-X))
     (196 196 (:META META-INTEGERP-CORRECT))
     (171 171 (:REWRITE |(< (* x y) 0)|))
     (162 162
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (162 162 (:REWRITE |(equal c (/ x))|))
     (162 162 (:REWRITE |(equal (/ x) c)|))
     (162 162 (:REWRITE |(equal (/ x) (/ y))|))
     (162 162 (:REWRITE |(equal (- x) (- y))|))
     (155 155 (:REWRITE SIMPLIFY-SUMS-<))
     (155 155
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (155 155
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (155 155
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (155 155 (:REWRITE INTEGERP-<-CONSTANT))
     (155 155 (:REWRITE CONSTANT-<-INTEGERP))
     (155 155
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (155 155
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (155 155
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (155 155
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (155 155 (:REWRITE |(< c (- x))|))
     (155 155
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (155 155
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (155 155
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (155 155
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (155 155 (:REWRITE |(< (/ x) (/ y))|))
     (155 155 (:REWRITE |(< (- x) c)|))
     (155 155 (:REWRITE |(< (- x) (- y))|))
     (154 154
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (108 4 (:REWRITE |(not (equal x (/ y)))|))
     (108 4 (:REWRITE |(equal x (/ y))|))
     (67 67
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (67 67
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (67 67 (:REWRITE |(< (/ x) 0)|))
     (66 66 (:REWRITE |(floor x 2)| . 2))
     (60 4
         (:REWRITE |(not (equal x (- (/ y))))|))
     (60 4 (:REWRITE |(equal x (- (/ y)))|))
     (55 55 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (43 43 (:REWRITE |(equal (+ (- c) x) y)|))
     (42 42
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (36 36
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (24 24
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (16 16 (:REWRITE REDUCE-RATIONALP-+))
     (16 16 (:REWRITE REDUCE-RATIONALP-*))
     (16 16 (:REWRITE RATIONALP-MINUS-X))
     (16 16
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (16 16 (:META META-RATIONALP-CORRECT))
     (16 8 (:REWRITE |(- (* c x))|))
     (8 8 (:REWRITE |(* x (- y))|))
     (8 8 (:REWRITE |(* (- x) y)|))
     (2 2 (:REWRITE EVEN-IS-NOT-ODD)))
(|(logand (floor x 2) (floor y 2))|
     (4555 113 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (4555 113 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (4535 642
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4528 4528
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (3851 190 (:REWRITE |(< (+ c/d x) y)|))
     (3144 48 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (2836 505
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2460 2460
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1805 761 (:REWRITE THE-FLOOR-ABOVE))
     (1726 1630 (:REWRITE NORMALIZE-ADDENDS))
     (1606 1606
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1344 48 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1233 913 (:REWRITE REDUCE-INTEGERP-+))
     (984 82
          (:REWRITE |(not (equal (* (/ x) y) -1))|))
     (984 82 (:REWRITE |(equal (* (/ x) y) -1)|))
     (913 913 (:REWRITE INTEGERP-MINUS-X))
     (913 913 (:META META-INTEGERP-CORRECT))
     (861 685 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (861 685
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (861 685
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (841 685
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (737 737 (:REWRITE DEFAULT-LESS-THAN-2))
     (685 685
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (685 685
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (685 685 (:REWRITE |(equal c (/ x))|))
     (685 685 (:REWRITE |(equal (/ x) c)|))
     (685 685 (:REWRITE |(equal (/ x) (/ y))|))
     (685 685 (:REWRITE |(equal (- x) c)|))
     (685 685 (:REWRITE |(equal (- x) (- y))|))
     (642 642 (:REWRITE |(< (* x y) 0)|))
     (607 415 (:REWRITE |(floor x 2)| . 2))
     (505 505
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (410 410 (:REWRITE SIMPLIFY-SUMS-<))
     (410 410
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (410 410
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (410 410
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (410 410 (:REWRITE INTEGERP-<-CONSTANT))
     (410 410 (:REWRITE CONSTANT-<-INTEGERP))
     (410 410
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (410 410
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (410 410
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (410 410
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (410 410 (:REWRITE |(< c (- x))|))
     (410 410
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (410 410
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (410 410
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (410 410
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (410 410 (:REWRITE |(< (/ x) (/ y))|))
     (410 410 (:REWRITE |(< (- x) c)|))
     (410 410 (:REWRITE |(< (- x) (- y))|))
     (315 315
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (315 315
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (315 315 (:REWRITE |(< (/ x) 0)|))
     (293 293 (:TYPE-PRESCRIPTION ABS))
     (288 48 (:REWRITE FLOOR-=-X/Y . 3))
     (288 48 (:REWRITE FLOOR-=-X/Y . 2))
     (200 200 (:REWRITE |(equal (+ (- c) x) y)|))
     (162 162 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (144 144
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (144 24 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (144 24 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (137 137
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (58 58 (:REWRITE |(equal (* x y) 0)|))
     (48 48 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (48 48 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (48 48
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (48 48
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (48 48 (:REWRITE FLOOR-CANCEL-*-CONST))
     (48 48 (:REWRITE |(floor x (- y))| . 2))
     (48 48 (:REWRITE |(floor x (- y))| . 1))
     (48 48
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (48 48
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (48 48 (:REWRITE |(floor (- x) y)| . 2))
     (48 48 (:REWRITE |(floor (- x) y)| . 1))
     (48 48
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (48 48
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (48 24 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (48 24 (:DEFINITION FIX))
     (24 24 (:REWRITE |(+ x (- x))|))
     (14 14 (:REWRITE |(floor (if a b c) x)|)))
(IND-FN (8 8 (:REWRITE THE-FLOOR-ABOVE))
        (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
        (7 7
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
        (7 7
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
        (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
        (7 7 (:REWRITE |(< (/ x) (/ y))|))
        (6 6
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
        (6 6
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
        (6 6
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
        (6 6
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
        (6 6
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
        (6 6
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
        (6 6
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
        (6 6
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
        (5 5
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
        (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
        (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
        (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
        (5 5 (:REWRITE INTEGERP-<-CONSTANT))
        (5 5 (:REWRITE CONSTANT-<-INTEGERP))
        (5 5 (:REWRITE |(< (- x) c)|))
        (4 4
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
        (4 4
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
        (4 4 (:REWRITE |(< (/ x) 0)|))
        (4 4 (:REWRITE |(< (* x y) 0)|))
        (3 3
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
        (2 2 (:REWRITE |(< (+ c/d x) y)|))
        (2 2 (:REWRITE |(< (+ (- c) x) y)|))
        (1 1 (:REWRITE REDUCE-INTEGERP-+))
        (1 1 (:REWRITE INTEGERP-MINUS-X))
        (1 1 (:REWRITE |(< y (+ (- c) x))|))
        (1 1 (:REWRITE |(< x (+ c/d y))|))
        (1 1 (:REWRITE |(< 0 (/ x))|))
        (1 1 (:REWRITE |(< 0 (* x y))|))
        (1 1 (:META META-INTEGERP-CORRECT)))
(LOGAND-FLOOR-EXPT-2-N
     (51240 16 (:REWRITE FLOOR-=-X/Y . 4))
     (30862 726 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (27030 218 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (27030 218 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (26962 218 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (26962 218 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (19201 1517 (:REWRITE THE-FLOOR-ABOVE))
     (15692 726 (:REWRITE FLOOR-=-X/Y . 2))
     (7616 312 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (6448 312 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (6288 726 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (6288 726 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5720 104 (:REWRITE |(< (logand x y) 0)|))
     (5499 5499
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (4094 726 (:REWRITE FLOOR-CANCEL-*-CONST))
     (3275 3275 (:REWRITE |(expt 1/c n)|))
     (3275 3275 (:REWRITE |(expt (- x) n)|))
     (2810 698
           (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2810 698
           (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2810 698
           (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (2281 2261 (:REWRITE INTEGERP-MINUS-X))
     (2271 2259 (:META META-INTEGERP-CORRECT))
     (2259 2259 (:REWRITE REDUCE-INTEGERP-+))
     (2237 1237
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2194 2194
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2179 1203
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1794 698
           (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (1794 698
           (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (1265 1237
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1265 1237
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1237 1237
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1237 1237
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1237 1237 (:REWRITE SIMPLIFY-SUMS-<))
     (1237 1237
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1237 1237
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1237 1237 (:REWRITE INTEGERP-<-CONSTANT))
     (1237 1237 (:REWRITE DEFAULT-LESS-THAN-2))
     (1237 1237 (:REWRITE CONSTANT-<-INTEGERP))
     (1237 1237
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1237 1237
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1237 1237
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1237 1237
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1237 1237 (:REWRITE |(< c (- x))|))
     (1237 1237
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1237 1237
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1237 1237
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1237 1237
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1237 1237 (:REWRITE |(< (/ x) 0)|))
     (1237 1237 (:REWRITE |(< (/ x) (/ y))|))
     (1237 1237 (:REWRITE |(< (- x) c)|))
     (1237 1237 (:REWRITE |(< (- x) (- y))|))
     (1237 1237 (:REWRITE |(< (* x y) 0)|))
     (996 225
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (897 225 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (698 698 (:REWRITE |(floor x (- y))| . 2))
     (698 698 (:REWRITE |(floor x (- y))| . 1))
     (698 698 (:REWRITE |(floor (- x) y)| . 2))
     (698 698 (:REWRITE |(floor (- x) y)| . 1))
     (340 340
          (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
     (340 340
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (254 234 (:REWRITE |(equal (- x) c)|))
     (252 234
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (237 234 (:REWRITE |(equal (- x) (- y))|))
     (234 234
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (234 234 (:REWRITE |(equal c (/ x))|))
     (234 234 (:REWRITE |(equal (/ x) c)|))
     (234 234 (:REWRITE |(equal (/ x) (/ y))|))
     (232 232
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (215 215 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (144 16
          (:REWRITE |(equal (floor (+ x y) z) x)|))
     (123 123 (:REWRITE |(* c (* d x))|))
     (74 74 (:TYPE-PRESCRIPTION ABS))
     (71 71
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (71 71 (:REWRITE |(floor x 2)| . 2))
     (58 34
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (58 34
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (58 34
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (48 19
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (17 17 (:REWRITE |(equal (+ (- c) x) y)|))
     (16 6 (:REWRITE |(- (* c x))|))
     (14 14 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
     (14 14 (:REWRITE |(* 1/2 (floor x y))| . 3))
     (14 14 (:REWRITE |(* 1/2 (floor x y))| . 2))
     (12 8 (:REWRITE |(* (- x) y)|))
     (4 1 (:REWRITE |(equal (expt 2 n) c)|))
     (4 1 (:REWRITE |(- (- x))|))
     (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
     (2 2 (:LINEAR EXPT-LINEAR-LOWER-<)))
(|(mod (logand x y) 2)|
     (1112 1112
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (546 46 (:REWRITE DEFAULT-MOD-RATIO))
     (333 333
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (282 282 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (260 46 (:REWRITE DEFAULT-MOD-1))
     (198 12 (:LINEAR MOD-BOUNDS-3))
     (178 178 (:REWRITE REDUCE-INTEGERP-+))
     (178 178 (:REWRITE INTEGERP-MINUS-X))
     (178 178 (:META META-INTEGERP-CORRECT))
     (130 13 (:REWRITE |(* (* x y) z)|))
     (84 84
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (66 66
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (66 66 (:REWRITE NORMALIZE-ADDENDS))
     (50 2 (:REWRITE |(* (if a b c) x)|))
     (49 49 (:REWRITE ZIP-OPEN))
     (46 46 (:REWRITE |(floor x 2)| . 2))
     (45 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (45 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (45 45
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (45 45
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (45 45 (:REWRITE |(equal c (/ x))|))
     (45 45 (:REWRITE |(equal (/ x) c)|))
     (45 45 (:REWRITE |(equal (/ x) (/ y))|))
     (45 45 (:REWRITE |(equal (- x) c)|))
     (45 45 (:REWRITE |(equal (- x) (- y))|))
     (44 44 (:REWRITE |(mod x 2)| . 2))
     (35 35 (:REWRITE DEFAULT-LOGAND-2))
     (35 35 (:REWRITE DEFAULT-LOGAND-1))
     (29 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL)))
(FLOOR-2-N-IND
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9 (:REWRITE |(< (- x) c)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE ZIP-OPEN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(BREAK-LOGAND-APART
     (1048 16 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (634 12 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (634 12 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (567 567
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (536 536
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (448 16 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (420 72 (:REWRITE THE-FLOOR-ABOVE))
     (338 338
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (292 64
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (232 44 (:REWRITE ZIP-OPEN))
     (165 165 (:REWRITE REDUCE-INTEGERP-+))
     (165 165 (:REWRITE INTEGERP-MINUS-X))
     (165 165 (:META META-INTEGERP-CORRECT))
     (154 154 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (128 64 (:REWRITE |(floor x 2)| . 2))
     (120 52
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (108 52
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (96 96
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (96 16 (:REWRITE FLOOR-=-X/Y . 3))
     (96 16 (:REWRITE FLOOR-=-X/Y . 2))
     (64 64 (:REWRITE DEFAULT-LESS-THAN-2))
     (64 64 (:REWRITE |(< (* x y) 0)|))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (56 56 (:REWRITE SIMPLIFY-SUMS-<))
     (56 56
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 56
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (56 56
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (56 56
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (56 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (56 56 (:REWRITE |(< (/ x) 0)|))
     (56 56 (:REWRITE |(< (/ x) (/ y))|))
     (56 56 (:REWRITE |(< (- x) c)|))
     (56 56 (:REWRITE |(< (- x) (- y))|))
     (52 52
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (52 52
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (52 52
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (52 52 (:REWRITE |(equal c (/ x))|))
     (52 52 (:REWRITE |(equal (/ x) c)|))
     (52 52 (:REWRITE |(equal (/ x) (/ y))|))
     (52 52 (:REWRITE |(equal (- x) c)|))
     (52 52 (:REWRITE |(equal (- x) (- y))|))
     (48 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (48 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (30 10 (:REWRITE DEFAULT-MOD-RATIO))
     (24 4 (:LINEAR MOD-BOUNDS-3))
     (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 16 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (16 16 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (16 16
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (16 16
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (16 16 (:REWRITE FLOOR-CANCEL-*-CONST))
     (16 16 (:REWRITE |(floor x (- y))| . 2))
     (16 16 (:REWRITE |(floor x (- y))| . 1))
     (16 16
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (16 16
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (16 16 (:REWRITE |(floor (- x) y)| . 2))
     (16 16 (:REWRITE |(floor (- x) y)| . 1))
     (16 16
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (16 16
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (8 8 (:TYPE-PRESCRIPTION ABS))
     (8 8
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (8 8
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(|(integerp (* 1/2 (mod x (expt 2 n))))|
     (1263 1263
           (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
     (814 407 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (814 407 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (751 21 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (693 21 (:REWRITE CANCEL-MOD-+))
     (441 21 (:REWRITE MOD-ZERO . 3))
     (407 407 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (365 21 (:REWRITE MOD-ZERO . 4))
     (335 335 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (335 335 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (330 330 (:REWRITE |(expt 1/c n)|))
     (330 330 (:REWRITE |(expt (- x) n)|))
     (273 21 (:REWRITE |(integerp (- x))|))
     (231 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (231 21
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (229 94
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (208 178 (:META META-INTEGERP-CORRECT))
     (208 8 (:LINEAR EXPT-X->=-X))
     (208 8 (:LINEAR EXPT-X->-X))
     (202 202
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (183 183 (:REWRITE INTEGERP-MINUS-X))
     (168 21 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (165 159 (:REWRITE |(< (- x) (- y))|))
     (161 161 (:REWRITE THE-FLOOR-ABOVE))
     (160 159
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (160 159
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (159 159
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (159 159 (:REWRITE INTEGERP-<-CONSTANT))
     (159 159 (:REWRITE CONSTANT-<-INTEGERP))
     (159 159
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (159 159
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (159 159
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (159 159
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (159 159 (:REWRITE |(< c (- x))|))
     (159 159
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (159 159
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (159 159
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (159 159
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (159 159 (:REWRITE |(< (/ x) (/ y))|))
     (159 159 (:REWRITE |(< (- x) c)|))
     (127 47 (:REWRITE ACL2-NUMBERP-X))
     (123 120 (:REWRITE RATIONALP-MINUS-X))
     (113 98 (:META META-RATIONALP-CORRECT))
     (105 21
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (105 21 (:REWRITE MOD-CANCEL-*-CONST))
     (105 21
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (105 21
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (97 57
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (72 47 (:REWRITE |(equal (/ x) c)|))
     (65 23 (:REWRITE |(* (- x) y)|))
     (63 63
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (63 63
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (63 63 (:REWRITE |(< 0 (/ x))|))
     (63 63 (:REWRITE |(< 0 (* x y))|))
     (61 61 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (47 47
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (47 47
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (47 47 (:REWRITE |(equal c (/ x))|))
     (47 47 (:REWRITE |(equal (/ x) (/ y))|))
     (47 47 (:REWRITE |(equal (- x) (- y))|))
     (47 44
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (45 45 (:REWRITE |(equal (- x) c)|))
     (44 44
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (44 44 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (42 42 (:REWRITE |(< (/ x) 0)|))
     (42 42 (:REWRITE |(< (* x y) 0)|))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (39 27 (:REWRITE ODD-EXPT-THM))
     (30 25
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (25 25 (:REWRITE |(+ c (+ d x))|))
     (25 19
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (25 2 (:REWRITE SUM-IS-EVEN . 2))
     (21 21
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (21 21 (:REWRITE |(mod x (- y))| . 3))
     (21 21 (:REWRITE |(mod x (- y))| . 2))
     (21 21 (:REWRITE |(mod x (- y))| . 1))
     (21 21
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (21 21 (:REWRITE |(mod (- x) y)| . 3))
     (21 21 (:REWRITE |(mod (- x) y)| . 2))
     (21 21 (:REWRITE |(mod (- x) y)| . 1))
     (21 21
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (21 21 (:REWRITE |(- (* c x))|))
     (21 19
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (20 20 (:REWRITE |(< (+ c/d x) y)|))
     (20 20 (:REWRITE |(< (+ (- c) x) y)|))
     (18 18 (:REWRITE |arith (expt x c)|))
     (18 18 (:REWRITE |arith (expt 1/c n)|))
     (16 16
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (16 16
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (16 16
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (14 14 (:REWRITE |(* c (* d x))|))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
     (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
     (8 8 (:LINEAR EXPT->=-1-TWO))
     (8 8 (:LINEAR EXPT->-1-TWO))
     (8 8 (:LINEAR EXPT-<=-1-TWO))
     (8 8 (:LINEAR EXPT-<=-1-ONE))
     (8 8 (:LINEAR EXPT-<-1-TWO))
     (8 8 (:LINEAR EXPT-<-1-ONE))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (3 3
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE |(not (equal x (/ y)))|))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2 (:REWRITE |(/ (/ x))|)))
(MOD-LOGAND
     (13385 534 (:REWRITE MOD-ZERO . 4))
     (12818 534 (:REWRITE MOD-ZERO . 3))
     (10838 10444
            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (6674 534
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (6674 534
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (6490 118 (:REWRITE |(< (logand x y) 0)|))
     (4768 549 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (4078 451 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (4078 451 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (3312 552
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2984 512
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (2976 512
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (2814 534 (:REWRITE MOD-CANCEL-*-CONST))
     (2767 113 (:LINEAR MOD-BOUNDS-3))
     (2230 2230
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2190 2190 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1887 602 (:REWRITE |(/ (expt x n))|))
     (1360 52 (:LINEAR EXPT-X->=-X))
     (1360 52 (:LINEAR EXPT-X->-X))
     (1249 813
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1225 813
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1207 575 (:REWRITE DEFAULT-MOD-1))
     (1169 1169 (:REWRITE |(expt 1/c n)|))
     (1169 1169 (:REWRITE |(expt (- x) n)|))
     (932 911 (:REWRITE DEFAULT-LESS-THAN-2))
     (911 911 (:REWRITE THE-FLOOR-ABOVE))
     (904 882
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (904 882
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (877 862 (:REWRITE INTEGERP-MINUS-X))
     (871 815 (:REWRITE |(< (- x) c)|))
     (841 841 (:META META-INTEGERP-CORRECT))
     (815 815
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (815 815
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (815 815
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (815 815
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (815 815 (:REWRITE |(< c (- x))|))
     (815 815
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (815 815
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (815 815
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (815 815
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (815 815 (:REWRITE |(< (/ x) (/ y))|))
     (815 815 (:REWRITE |(< (- x) (- y))|))
     (813 813
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (813 813 (:REWRITE INTEGERP-<-CONSTANT))
     (813 813 (:REWRITE CONSTANT-<-INTEGERP))
     (803 7 (:REWRITE ODD-EXPT-THM))
     (716 26 (:REWRITE |(* (* x y) z)|))
     (680 680 (:REWRITE |(< (* x y) 0)|))
     (640 640 (:REWRITE |(< (/ x) 0)|))
     (638 638
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (638 638
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (581 561
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (558 552 (:REWRITE |(equal (- x) (- y))|))
     (552 552
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (552 552 (:REWRITE |(equal c (/ x))|))
     (552 552 (:REWRITE |(equal (/ x) c)|))
     (552 552 (:REWRITE |(equal (/ x) (/ y))|))
     (552 552 (:REWRITE |(equal (- x) c)|))
     (550 550
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (516 54 (:LINEAR EXPT-<=-1-TWO))
     (512 512
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (512 512 (:REWRITE |(mod x (- y))| . 3))
     (512 512 (:REWRITE |(mod x (- y))| . 2))
     (512 512 (:REWRITE |(mod x (- y))| . 1))
     (512 512
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (512 512 (:REWRITE |(mod (- x) y)| . 3))
     (512 512 (:REWRITE |(mod (- x) y)| . 2))
     (512 512 (:REWRITE |(mod (- x) y)| . 1))
     (512 512
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (479 479
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (405 27 (:REWRITE |(* (/ c) (expt d n))|))
     (372 161 (:REWRITE |(* y x)|))
     (360 20 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
     (256 33
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (212 4 (:REWRITE |(* (+ x y) z)|))
     (139 27 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (104 104
          (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (104 104
          (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (104 104
          (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (98 2 (:REWRITE |(integerp (expt x n))|))
     (96 3 (:REWRITE MOD-ZERO . 1))
     (81 81 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (81 27 (:REWRITE |(- (+ x y))|))
     (78 78 (:REWRITE FOLD-CONSTS-IN-+))
     (75 5 (:REWRITE |(* (- (/ c)) (expt d n))|))
     (68 68 (:REWRITE |(floor x 2)| . 2))
     (64 64 (:TYPE-PRESCRIPTION ABS))
     (56 56 (:REWRITE |(< x (+ c/d y))|))
     (54 54 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (54 54 (:LINEAR EXPT-LINEAR-UPPER-<))
     (54 54 (:LINEAR EXPT-LINEAR-LOWER-<))
     (54 54 (:LINEAR EXPT->=-1-TWO))
     (54 54 (:LINEAR EXPT->-1-TWO))
     (54 54 (:LINEAR EXPT-<=-1-ONE))
     (54 54 (:LINEAR EXPT-<-1-TWO))
     (54 54 (:LINEAR EXPT-<-1-ONE))
     (53 53 (:REWRITE |(< 0 (* x y))|))
     (34 34 (:REWRITE |(< (+ (- c) x) y)|))
     (32 3 (:REWRITE MOD-ZERO . 2))
     (27 27 (:REWRITE |(* c (* d x))|))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (25 25
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (25 25 (:REWRITE |(< 0 (/ x))|))
     (25 1 (:REWRITE |(* y (* x z))|))
     (22 22
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (18 18 (:REWRITE |(mod x 2)| . 2))
     (9 9 (:REWRITE |(equal (* x y) 0)|))
     (5 5
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (5 5
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (5 5 (:REWRITE |(equal x (/ y))|))
     (5 5 (:REWRITE |(* (- x) y)|))
     (2 2 (:REWRITE |(- (- x))|))
     (1 1 (:REWRITE |(* x (- y))|)))
(|(integerp (* 1/2 (logand x y)))|
     (760 760
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (247 247
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (143 143 (:REWRITE REDUCE-INTEGERP-+))
     (143 143 (:REWRITE INTEGERP-MINUS-X))
     (143 143 (:META META-INTEGERP-CORRECT))
     (76 76
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (61 61
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (61 61 (:REWRITE NORMALIZE-ADDENDS))
     (49 49 (:REWRITE ZIP-OPEN))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (49 49
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (49 49 (:REWRITE |(equal c (/ x))|))
     (49 49 (:REWRITE |(equal (/ x) c)|))
     (49 49 (:REWRITE |(equal (/ x) (/ y))|))
     (49 49 (:REWRITE |(equal (- x) c)|))
     (49 49 (:REWRITE |(equal (- x) (- y))|))
     (47 47 (:REWRITE |(floor x 2)| . 2))
     (45 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (45 45
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (35 35 (:REWRITE DEFAULT-LOGAND-2))
     (35 35 (:REWRITE DEFAULT-LOGAND-1))
     (29 29
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (16 16
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL)))
(IND-HINT (4 4 (:REWRITE THE-FLOOR-ABOVE))
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
          (3 3 (:REWRITE |(< (/ x) 0)|))
          (3 3 (:REWRITE |(< (* x y) 0)|))
          (2 2 (:REWRITE |(< (+ c/d x) y)|))
          (2 2 (:REWRITE |(< (+ (- c) x) y)|))
          (1 1 (:REWRITE ZP-OPEN))
          (1 1 (:REWRITE ZIP-OPEN))
          (1 1 (:REWRITE REDUCE-INTEGERP-+))
          (1 1
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (1 1 (:REWRITE INTEGERP-MINUS-X))
          (1 1 (:META META-INTEGERP-CORRECT)))
(LOGAND-MASK
     (2117 21 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (2117 21 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (2017 20 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (1402 1402
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1328 1322
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (1156 65 (:REWRITE FLOOR-=-X/Y . 2))
     (987 679 (:REWRITE |(< (- x) c)|))
     (928 869 (:REWRITE DEFAULT-LESS-THAN-2))
     (869 869 (:REWRITE THE-FLOOR-ABOVE))
     (828 824
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (828 824
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (779 32 (:REWRITE |(integerp (- x))|))
     (727 727 (:REWRITE |(expt 1/c n)|))
     (727 727 (:REWRITE |(expt (- x) n)|))
     (710 19 (:REWRITE CANCEL-MOD-+))
     (698 668
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (684 681 (:REWRITE |(< (- x) (- y))|))
     (681 681
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (681 681
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (681 681
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (681 681
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (681 681
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (681 681
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (681 681
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (681 681
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (681 681 (:REWRITE |(< (/ x) (/ y))|))
     (668 668 (:REWRITE INTEGERP-<-CONSTANT))
     (668 668 (:REWRITE CONSTANT-<-INTEGERP))
     (626 626 (:REWRITE |(< (* x y) 0)|))
     (614 614 (:REWRITE |arith (expt x c)|))
     (598 598 (:REWRITE |arith (expt 1/c n)|))
     (592 553
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (548 400 (:META META-INTEGERP-CORRECT))
     (520 400 (:REWRITE REDUCE-INTEGERP-+))
     (500 264 (:REWRITE |(* c (* d x))|))
     (492 492 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (475 26 (:REWRITE DEFAULT-MOD-RATIO))
     (470 470 (:REWRITE |(< (/ x) 0)|))
     (432 432
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (432 432
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (409 400 (:REWRITE INTEGERP-MINUS-X))
     (390 65 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (360 60 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (328 310 (:REWRITE |(equal (- x) (- y))|))
     (310 310 (:REWRITE |(equal c (/ x))|))
     (310 310 (:REWRITE |(equal (/ x) c)|))
     (310 310 (:REWRITE |(equal (/ x) (/ y))|))
     (306 306
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (275 1 (:REWRITE ODD-EXPT-THM))
     (246 246 (:REWRITE |arith (* c (* d x))|))
     (244 55 (:REWRITE DEFAULT-LOGAND-1))
     (240 60
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (240 60 (:REWRITE FLOOR-CANCEL-*-CONST))
     (240 60
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (240 60
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (202 12 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
     (152 19 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (152 19
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (149 70
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (149 70
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (134 11
          (:REWRITE |(not (equal (* (/ x) y) -1))|))
     (134 11 (:REWRITE |(equal (* (/ x) y) -1)|))
     (132 22 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (130 10
          (:REWRITE |(* (- (/ c)) (expt d n))|))
     (123 123 (:REWRITE |arith (* (- x) y)|))
     (111 111 (:REWRITE |(floor x 2)| . 2))
     (110 110
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (105 88
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (105 88
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (103 88
          (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (94 2 (:REWRITE |(* (+ x y) z)|))
     (91 91 (:REWRITE |arith (- (* c x))|))
     (74 1 (:REWRITE |(* (if a b c) x)|))
     (72 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (68 68
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (68 68
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (68 68
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (68 40 (:REWRITE |(* (- x) y)|))
     (64 19 (:REWRITE MOD-CANCEL-*-CONST))
     (60 60
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (60 60 (:REWRITE |(floor x (- y))| . 2))
     (60 60 (:REWRITE |(floor x (- y))| . 1))
     (60 60
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (60 60 (:REWRITE |(floor (- x) y)| . 2))
     (60 60 (:REWRITE |(floor (- x) y)| . 1))
     (60 60
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (60 15
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (60 15
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (60 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (48 2 (:REWRITE EXPT-X->=-X))
     (46 46 (:LINEAR EXPT-LINEAR-UPPER-<))
     (46 46 (:LINEAR EXPT-LINEAR-LOWER-<))
     (46 46 (:LINEAR EXPT->=-1-TWO))
     (46 46 (:LINEAR EXPT->-1-TWO))
     (46 46 (:LINEAR EXPT-<=-1-ONE))
     (46 46 (:LINEAR EXPT-<-1-ONE))
     (39 39 (:REWRITE |(< x (+ c/d y))|))
     (35 35 (:REWRITE FOLD-CONSTS-IN-+))
     (29 29 (:REWRITE |(< 0 (* x y))|))
     (26 26 (:REWRITE DEFAULT-MOD-1))
     (15 15
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (15 15 (:REWRITE |(mod x (- y))| . 3))
     (15 15 (:REWRITE |(mod x (- y))| . 2))
     (15 15 (:REWRITE |(mod x (- y))| . 1))
     (15 15
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (15 15 (:REWRITE |(mod (- x) y)| . 3))
     (15 15 (:REWRITE |(mod (- x) y)| . 2))
     (15 15 (:REWRITE |(mod (- x) y)| . 1))
     (15 15
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< y (+ (- c) x))|))
     (11 11 (:REWRITE |(< 0 (/ x))|))
     (4 4
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (2 2 (:REWRITE |arith (+ c (+ d x))|))
     (1 1 (:REWRITE |(mod x 2)| . 2))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (1 1
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2)))
(L-C-M-FN)
(LOGAND-CONSTANT-MASK
     (792 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (730 50
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (376 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (324 12 (:REWRITE CANCEL-MOD-+))
     (184 2 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (184 2 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (136 2 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (120 12 (:REWRITE |(integerp (- x))|))
     (116 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (116 12
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (76 76
         (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
     (76 12 (:REWRITE DEFAULT-MOD-RATIO))
     (70 14 (:LINEAR EXPT-<=-1-TWO))
     (68 14 (:LINEAR EXPT->-1-ONE))
     (65 65 (:REWRITE |(expt 1/c n)|))
     (65 65 (:REWRITE |(expt (- x) n)|))
     (62 4 (:LINEAR MOD-BOUNDS-3))
     (61 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (61 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (60 14 (:LINEAR EXPT-X->=-X))
     (60 14 (:LINEAR EXPT-X->-X))
     (54 38
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (54 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (54 18 (:REWRITE |(/ (expt x n))|))
     (50 50 (:REWRITE THE-FLOOR-ABOVE))
     (50 50
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (50 50 (:REWRITE DEFAULT-LESS-THAN-2))
     (44 12
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (44 12
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (44 12
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (41 12 (:REWRITE MOD-CANCEL-*-CONST))
     (38 38 (:REWRITE SIMPLIFY-SUMS-<))
     (38 38
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (36 12 (:REWRITE |(* (- x) y)|))
     (34 34 (:REWRITE |(< (* x y) 0)|))
     (33 25
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (33 25
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (28 28
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (28 28
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (28 28
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (28 4 (:REWRITE |(+ y (+ x z))|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (26 26 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE REDUCE-INTEGERP-+))
     (18 18 (:REWRITE INTEGERP-MINUS-X))
     (18 18 (:META META-INTEGERP-CORRECT))
     (14 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
     (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
     (14 14 (:LINEAR EXPT->=-1-TWO))
     (14 14 (:LINEAR EXPT->-1-TWO))
     (14 14 (:LINEAR EXPT-<=-1-ONE))
     (14 14 (:LINEAR EXPT-<-1-TWO))
     (14 14 (:LINEAR EXPT-<-1-ONE))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (12 12
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (12 12 (:REWRITE DEFAULT-MOD-1))
     (12 12 (:REWRITE |(mod x (- y))| . 3))
     (12 12 (:REWRITE |(mod x (- y))| . 2))
     (12 12 (:REWRITE |(mod x (- y))| . 1))
     (12 12
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(mod (- x) y)| . 3))
     (12 12 (:REWRITE |(mod (- x) y)| . 2))
     (12 12 (:REWRITE |(mod (- x) y)| . 1))
     (12 12
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (12 12 (:REWRITE |(< (+ c/d x) y)|))
     (12 12 (:REWRITE |(- (* c x))|))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|)))
(LEMMA (2486 29 (:REWRITE MOD-ZERO . 3))
       (1866 19 (:LINEAR MOD-BOUNDS-3))
       (1082 29 (:REWRITE MOD-X-Y-=-X+Y . 2))
       (981 320 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
       (880 35 (:LINEAR EXPT-X->=-X))
       (880 35 (:LINEAR EXPT-X->-X))
       (675 9 (:REWRITE MOD-X-I*J))
       (648 9 (:REWRITE MOD-X-I*J-V2))
       (522 29 (:REWRITE MOD-ZERO . 4))
       (507 320 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
       (391 29 (:REWRITE |(mod (+ x (mod a b)) y)|))
       (391 29
            (:REWRITE |(mod (+ x (- (mod a b))) y)|))
       (367 319 (:REWRITE DEFAULT-LESS-THAN-2))
       (356 356 (:REWRITE DEFAULT-EXPT-1))
       (350 350 (:REWRITE |(expt 1/c n)|))
       (350 350 (:REWRITE |(expt (- x) n)|))
       (331 35 (:LINEAR EXPT-<=-1-TWO))
       (328 319
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
       (321 35 (:LINEAR EXPT-<-1-TWO))
       (320 320 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
       (320 320 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
       (320 50
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
       (319 319 (:REWRITE THE-FLOOR-ABOVE))
       (319 319
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
       (319 319
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
       (319 319
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
       (319 319 (:REWRITE |(< (- x) (- y))|))
       (277 29 (:REWRITE MOD-X-Y-=-X+Y . 3))
       (275 275 (:REWRITE INTEGERP-<-CONSTANT))
       (275 275 (:REWRITE CONSTANT-<-INTEGERP))
       (198 33
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
       (195 165
            (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
       (188 188
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
       (187 187 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
       (163 29
            (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
       (163 29 (:REWRITE MOD-CANCEL-*-CONST))
       (163 29
            (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
       (163 29
            (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
       (161 131 (:REWRITE INTEGERP-MINUS-X))
       (152 152 (:REWRITE REMOVE-WEAK-INEQUALITIES))
       (135 135 (:REWRITE |(< (/ x) 0)|))
       (135 135 (:REWRITE |(< (* x y) 0)|))
       (122 17
            (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
       (120 102
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
       (107 107 (:REWRITE |arith (expt x c)|))
       (104 104 (:REWRITE |arith (expt 1/c n)|))
       (95 95 (:REWRITE |(< 0 (/ x))|))
       (95 95 (:REWRITE |(< 0 (* x y))|))
       (91 91
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
       (91 91
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
       (91 91
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
       (91 91
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
       (85 17 (:REWRITE ACL2-NUMBERP-X))
       (71 14
           (:REWRITE |(equal (mod (+ x y) z) x)|))
       (70 70
           (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
       (70 70
           (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
       (70 70
           (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
       (70 1
           (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
       (68 1
           (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
       (63 63 (:REWRITE |(* c (* d x))|))
       (51 51
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
       (51 51
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
       (51 51
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
       (51 51 (:REWRITE |(equal c (/ x))|))
       (51 51 (:REWRITE |(equal (/ x) c)|))
       (51 51 (:REWRITE |(equal (/ x) (/ y))|))
       (51 51 (:REWRITE |(equal (- x) c)|))
       (51 51 (:REWRITE |(equal (- x) (- y))|))
       (45 45 (:REWRITE RATIONALP-MINUS-X))
       (41 41 (:REWRITE REDUCE-RATIONALP-+))
       (41 41 (:META META-RATIONALP-CORRECT))
       (38 38 (:TYPE-PRESCRIPTION RATIONALP-MOD))
       (36 6 (:REWRITE |(integerp (- x))|))
       (35 35
           (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
       (35 35 (:LINEAR EXPT-LINEAR-UPPER-<=))
       (35 35 (:LINEAR EXPT-LINEAR-UPPER-<))
       (35 35 (:LINEAR EXPT-LINEAR-LOWER-<))
       (35 35 (:LINEAR EXPT->=-1-TWO))
       (35 35 (:LINEAR EXPT->-1-TWO))
       (35 35 (:LINEAR EXPT-<=-1-ONE))
       (35 35 (:LINEAR EXPT-<-1-ONE))
       (33 33
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
       (30 30 (:REWRITE |arith (* c (* d x))|))
       (30 30 (:REWRITE |(+ c (+ d x))|))
       (29 29
           (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
       (29 29 (:REWRITE |(mod x (- y))| . 3))
       (29 29 (:REWRITE |(mod x (- y))| . 2))
       (29 29 (:REWRITE |(mod x (- y))| . 1))
       (29 29
           (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
       (29 29 (:REWRITE |(mod (- x) y)| . 3))
       (29 29 (:REWRITE |(mod (- x) y)| . 2))
       (29 29 (:REWRITE |(mod (- x) y)| . 1))
       (29 29
           (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
       (25 25 (:REWRITE |(< y (+ (- c) x))|))
       (25 25 (:REWRITE |(< x (+ c/d y))|))
       (20 20 (:REWRITE |(< (+ c/d x) y)|))
       (20 20 (:REWRITE |(< (+ (- c) x) y)|))
       (20 1 (:REWRITE SUM-IS-EVEN . 2))
       (19 19 (:REWRITE ZP-OPEN))
       (15 15 (:REWRITE |(equal (expt 2 n) c)|))
       (9 3 (:REWRITE |(- (* c x))|))
       (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
       (4 4 (:REWRITE FOLD-CONSTS-IN-+))
       (4 4 (:REWRITE |(* (- x) y)|))
       (3 3 (:TYPE-PRESCRIPTION FIX))
       (3 3 (:REWRITE ARITH-NORMALIZE-ADDENDS))
       (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
       (1 1
          (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
       (1 1
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(LEMMA2 (23970 23 (:DEFINITION BINARY-LOGAND))
        (21810 28 (:LINEAR LOGAND-BOUNDS-POS . 2))
        (17033 1553
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
        (13242 699 (:META META-INTEGERP-CORRECT))
        (10454 997
               (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
        (8008 46 (:REWRITE |(floor x 2)| . 1))
        (7894 243
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
        (6446 46 (:REWRITE ZIP-OPEN))
        (5667 46 (:DEFINITION EVENP))
        (5337 28 (:LINEAR LOGAND-BOUNDS-POS . 1))
        (4440 28 (:LINEAR LOGAND-BOUNDS-NEG . 2))
        (4440 28 (:LINEAR LOGAND-BOUNDS-NEG . 1))
        (4387 149
              (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
        (3554 168 (:LINEAR EXPT-X->=-X))
        (3554 168 (:LINEAR EXPT-X->-X))
        (2738 1343 (:REWRITE |(< (- x) c)|))
        (2532 300 (:REWRITE |(< (+ c/d x) y)|))
        (2121 1596 (:REWRITE DEFAULT-LESS-THAN-2))
        (2103 34 (:REWRITE MOD-ZERO . 3))
        (1781 269 (:REWRITE |(< 0 (/ x))|))
        (1707 721 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
        (1707 168 (:LINEAR EXPT-<-1-TWO))
        (1603 997
              (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
        (1596 1596 (:REWRITE THE-FLOOR-ABOVE))
        (1525 1525
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
        (1456 755 (:REWRITE INTEGERP-MINUS-X))
        (1447 1297
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
        (1395 1371 (:REWRITE |(< (- x) (- y))|))
        (1371 1371
              (:REWRITE |(< c (/ x)) positive c --- present in goal|))
        (1371 1371
              (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
        (1371 1371
              (:REWRITE |(< c (/ x)) negative c --- present in goal|))
        (1371 1371
              (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
        (1371 1371
              (:REWRITE |(< (/ x) c) positive c --- present in goal|))
        (1371 1371
              (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
        (1371 1371
              (:REWRITE |(< (/ x) c) negative c --- present in goal|))
        (1371 1371
              (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
        (1371 1371 (:REWRITE |(< (/ x) (/ y))|))
        (1343 1343 (:REWRITE |(< c (- x))|))
        (1336 16 (:REWRITE |(equal x (/ y))|))
        (1297 1297 (:REWRITE INTEGERP-<-CONSTANT))
        (1297 1297 (:REWRITE CONSTANT-<-INTEGERP))
        (1294 197 (:REWRITE SIMPLIFY-SUMS-EQUAL))
        (1264 1264
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
        (1260 1041
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
        (1248 18 (:REWRITE |(integerp (- x))|))
        (1236 34 (:REWRITE MOD-X-Y-=-X+Y . 2))
        (1233 721 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
        (1128 16 (:REWRITE |(not (equal x (/ y)))|))
        (1041 1041
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
        (901 71 (:REWRITE ODD-EXPT-THM))
        (821 149
             (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
        (807 807 (:REWRITE DEFAULT-EXPT-1))
        (790 790 (:REWRITE |(expt 1/c n)|))
        (790 790 (:REWRITE |(expt (- x) n)|))
        (744 480 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
        (744 480 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
        (713 24 (:REWRITE SUM-IS-EVEN . 2))
        (713 24 (:REWRITE SUM-IS-EVEN . 1))
        (695 695 (:REWRITE |(< (* x y) 0)|))
        (608 608 (:REWRITE |(< (/ x) 0)|))
        (528 528
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
        (528 528
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
        (475 34 (:REWRITE MOD-ZERO . 4))
        (469 469 (:REWRITE |arith (expt x c)|))
        (454 454 (:REWRITE |arith (expt 1/c n)|))
        (450 6 (:REWRITE MOD-X-I*J))
        (432 6 (:REWRITE MOD-X-I*J-V2))
        (422 34 (:REWRITE |(mod (+ x (mod a b)) y)|))
        (422 34
             (:REWRITE |(mod (+ x (- (mod a b))) y)|))
        (409 5
             (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
        (409 5
             (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
        (409 5
             (:REWRITE |(< (expt x n) (expt x m))|))
        (399 5
             (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
        (399 5
             (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
        (396 9
             (:REWRITE |(equal (expt x m) (expt x n))|))
        (348 8 (:LINEAR MOD-BOUNDS-3))
        (343 288
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
        (336 336
             (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
        (336 336
             (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
        (336 336
             (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
        (336 336
             (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
        (329 275 (:REWRITE |(equal (- x) (- y))|))
        (327 273 (:REWRITE |(equal (- x) c)|))
        (314 314 (:REWRITE |(< 0 (* x y))|))
        (306 275
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (302 34 (:REWRITE MOD-X-Y-=-X+Y . 3))
        (300 275 (:REWRITE |(equal (/ x) c)|))
        (294 294
             (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
        (275 275
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (275 275 (:REWRITE |(equal c (/ x))|))
        (275 275 (:REWRITE |(equal (/ x) (/ y))|))
        (264 264
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (241 241
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
        (241 241
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
        (240 240 (:REWRITE FOLD-CONSTS-IN-+))
        (188 188 (:REWRITE |(< (+ (- c) x) y)|))
        (185 185 (:REWRITE |(< x (+ c/d y))|))
        (182 34
             (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
        (182 34 (:REWRITE MOD-CANCEL-*-CONST))
        (182 34
             (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
        (182 34
             (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
        (170 170 (:LINEAR EXPT-LINEAR-UPPER-<=))
        (170 170 (:LINEAR EXPT-LINEAR-UPPER-<))
        (170 170 (:LINEAR EXPT-LINEAR-LOWER-<=))
        (170 170 (:LINEAR EXPT-LINEAR-LOWER-<))
        (168 168 (:LINEAR EXPT->=-1-TWO))
        (168 168 (:LINEAR EXPT->-1-TWO))
        (168 168 (:LINEAR EXPT-<=-1-ONE))
        (168 168 (:LINEAR EXPT-<-1-ONE))
        (154 154 (:REWRITE |(equal (+ (- c) x) y)|))
        (140 56 (:REWRITE |(equal (expt 2 n) c)|))
        (139 139 (:REWRITE |arith (* c (* d x))|))
        (123 123 (:REWRITE ARITH-NORMALIZE-ADDENDS))
        (112 56 (:REWRITE |(+ (* c x) (* d x))|))
        (91 91 (:REWRITE |(* (- x) y)|))
        (75 75 (:REWRITE |(< y (+ (- c) x))|))
        (74 74 (:REWRITE |(- (- x))|))
        (66 22 (:REWRITE ACL2-NUMBERP-X))
        (61 61 (:REWRITE LOGAND-CONSTANT-MASK))
        (59 59 (:TYPE-PRESCRIPTION ABS))
        (58 58 (:TYPE-PRESCRIPTION RATIONALP-MOD))
        (57 57
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
        (56 56 (:REWRITE |(* 0 x)|))
        (47 11
            (:REWRITE |(equal (mod (+ x y) z) x)|))
        (46 46 (:REWRITE |(floor x 2)| . 2))
        (43 43 (:REWRITE RATIONALP-MINUS-X))
        (39 39 (:REWRITE ZP-OPEN))
        (39 39 (:REWRITE REDUCE-RATIONALP-+))
        (39 39 (:META META-RATIONALP-CORRECT))
        (34 34
            (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
        (34 34 (:REWRITE |(mod x (- y))| . 3))
        (34 34 (:REWRITE |(mod x (- y))| . 2))
        (34 34 (:REWRITE |(mod x (- y))| . 1))
        (34 34
            (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
        (34 34 (:REWRITE |(mod (- x) y)| . 3))
        (34 34 (:REWRITE |(mod (- x) y)| . 2))
        (34 34 (:REWRITE |(mod (- x) y)| . 1))
        (34 34
            (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
        (28 28 (:REWRITE |(equal (expt x n) 1)|))
        (23 23 (:REWRITE |arith (* (- x) y)|))
        (19 19 (:REWRITE |arith (+ c (+ d x))|))
        (4 4
           (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
        (2 2 (:REWRITE |(/ (/ x))|))
        (1 1
           (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(LEMMA3 (15968 321 (:REWRITE |(< (+ c/d x) y)|))
        (13213 1501
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
        (10438 162 (:REWRITE |(integerp (expt x n))|))
        (9380 737 (:REWRITE REDUCE-INTEGERP-+))
        (7907 29 (:LINEAR LOGAND-BOUNDS-POS . 1))
        (7887 29 (:LINEAR LOGAND-BOUNDS-NEG . 2))
        (7887 29 (:LINEAR LOGAND-BOUNDS-NEG . 1))
        (7231 737 (:META META-INTEGERP-CORRECT))
        (6526 286 (:LINEAR EXPT-X->=-X))
        (6526 286 (:LINEAR EXPT-X->-X))
        (4732 64 (:REWRITE MOD-ZERO . 3))
        (3880 286 (:LINEAR EXPT-<=-1-TWO))
        (3554 1313 (:REWRITE |(< (- x) c)|))
        (3042 44 (:REWRITE |(integerp (- x))|))
        (2944 35 (:LINEAR MOD-BOUNDS-3))
        (2392 64 (:REWRITE MOD-X-Y-=-X+Y . 2))
        (2310 25 (:REWRITE |(not (equal x (/ y)))|))
        (2218 25 (:REWRITE |(equal x (/ y))|))
        (1801 802 (:REWRITE INTEGERP-MINUS-X))
        (1717 1570 (:REWRITE DEFAULT-LESS-THAN-2))
        (1709 465 (:REWRITE |(equal (- x) c)|))
        (1620 1620
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
        (1570 1570 (:REWRITE THE-FLOOR-ABOVE))
        (1501 1501
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
        (1378 834 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
        (1378 834 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
        (1343 1322 (:REWRITE |(< (- x) (- y))|))
        (1322 1322
              (:REWRITE |(< c (/ x)) positive c --- present in goal|))
        (1322 1322
              (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
        (1322 1322
              (:REWRITE |(< c (/ x)) negative c --- present in goal|))
        (1322 1322
              (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
        (1322 1322
              (:REWRITE |(< (/ x) c) positive c --- present in goal|))
        (1322 1322
              (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
        (1322 1322
              (:REWRITE |(< (/ x) c) negative c --- present in goal|))
        (1322 1322
              (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
        (1322 1322 (:REWRITE |(< (/ x) (/ y))|))
        (1313 1313 (:REWRITE |(< c (- x))|))
        (1312 18 (:REWRITE MOD-ZERO . 1))
        (1308 247
              (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
        (1239 1239
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
        (1239 1239 (:REWRITE INTEGERP-<-CONSTANT))
        (1239 1239 (:REWRITE CONSTANT-<-INTEGERP))
        (1160 1160 (:REWRITE DEFAULT-EXPT-2))
        (1160 1160 (:REWRITE DEFAULT-EXPT-1))
        (1131 1131 (:REWRITE |(expt 1/c n)|))
        (1131 1131 (:REWRITE |(expt (- x) n)|))
        (1078 811
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
        (1072 838
              (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
        (1072 838
              (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
        (859 811
             (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
        (832 64 (:REWRITE |(mod (+ x (mod a b)) y)|))
        (832 64
             (:REWRITE |(mod (+ x (- (mod a b))) y)|))
        (749 749 (:REWRITE |arith (expt x c)|))
        (747 64 (:REWRITE MOD-ZERO . 4))
        (728 728 (:REWRITE |arith (expt 1/c n)|))
        (671 671 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
        (599 467 (:REWRITE |(equal (- x) (- y))|))
        (592 64 (:REWRITE MOD-X-Y-=-X+Y . 3))
        (592 16 (:REWRITE FLOOR-X-Y-=--1 . 2))
        (572 572
             (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
        (572 572
             (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
        (572 572
             (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
        (571 7
             (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
        (519 519 (:REWRITE REMOVE-WEAK-INEQUALITIES))
        (512 467
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
        (499 499 (:REWRITE |(< (* x y) 0)|))
        (492 467 (:REWRITE |(equal (/ x) c)|))
        (467 467
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
        (467 467 (:REWRITE |(equal c (/ x))|))
        (467 467 (:REWRITE |(equal (/ x) (/ y))|))
        (455 394
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
        (434 434
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
        (379 379 (:REWRITE |(< (/ x) 0)|))
        (372 372 (:REWRITE |(< 0 (* x y))|))
        (352 64
             (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
        (352 64 (:REWRITE MOD-CANCEL-*-CONST))
        (352 64
             (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
        (352 64
             (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
        (320 16 (:REWRITE FLOOR-=-X/Y . 3))
        (307 307
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
        (307 307
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
        (304 16 (:REWRITE FLOOR-=-X/Y . 2))
        (298 298 (:REWRITE |(equal (+ (- c) x) y)|))
        (289 289
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
        (289 289
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
        (286 286 (:LINEAR EXPT-LINEAR-UPPER-<=))
        (286 286 (:LINEAR EXPT-LINEAR-UPPER-<))
        (286 286 (:LINEAR EXPT-LINEAR-LOWER-<))
        (286 286 (:LINEAR EXPT->=-1-TWO))
        (286 286 (:LINEAR EXPT->-1-TWO))
        (286 286 (:LINEAR EXPT-<=-1-ONE))
        (286 286 (:LINEAR EXPT-<-1-TWO))
        (286 286 (:LINEAR EXPT-<-1-ONE))
        (237 237
             (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
        (236 236 (:REWRITE FOLD-CONSTS-IN-+))
        (202 202 (:REWRITE |(< x (+ c/d y))|))
        (194 194 (:REWRITE |(< (+ (- c) x) y)|))
        (172 172 (:TYPE-PRESCRIPTION RATIONALP-MOD))
        (169 18 (:REWRITE MOD-ZERO . 2))
        (168 18 (:REWRITE MOD-X-I*J-V2))
        (132 132 (:REWRITE |(* (- x) y)|))
        (128 16 (:REWRITE FLOOR-X-Y-=-1 . 3))
        (128 16 (:REWRITE FLOOR-X-Y-=--1 . 3))
        (117 117 (:REWRITE ARITH-NORMALIZE-ADDENDS))
        (116 116 (:REWRITE |arith (* c (* d x))|))
        (99 99
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
        (96 96 (:REWRITE LOGAND-CONSTANT-MASK))
        (87 18
            (:REWRITE |(equal (mod (+ x y) z) x)|))
        (83 83 (:REWRITE |(< y (+ (- c) x))|))
        (82 82 (:REWRITE |(floor x 2)| . 2))
        (80 16
            (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
        (80 16 (:REWRITE FLOOR-CANCEL-*-CONST))
        (80 16
            (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
        (80 16
            (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
        (74 20 (:REWRITE ODD-EXPT-THM))
        (72 72 (:REWRITE LEMMA2))
        (72 72 (:REWRITE LEMMA))
        (70 70 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
        (64 64
            (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
        (64 64 (:REWRITE |(mod x (- y))| . 3))
        (64 64 (:REWRITE |(mod x (- y))| . 2))
        (64 64 (:REWRITE |(mod x (- y))| . 1))
        (64 64
            (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
        (64 64 (:REWRITE |(mod (- x) y)| . 3))
        (64 64 (:REWRITE |(mod (- x) y)| . 2))
        (64 64 (:REWRITE |(mod (- x) y)| . 1))
        (64 64
            (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
        (60 20 (:REWRITE ACL2-NUMBERP-X))
        (52 2 (:REWRITE EXPT-2-N-IS-EVEN))
        (46 46 (:REWRITE |(equal (expt x n) 1)|))
        (39 39 (:REWRITE ZP-OPEN))
        (28 28 (:REWRITE RATIONALP-MINUS-X))
        (26 26 (:REWRITE REDUCE-RATIONALP-+))
        (26 26 (:META META-RATIONALP-CORRECT))
        (16 16
            (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
        (16 16 (:REWRITE |(floor x (- y))| . 2))
        (16 16 (:REWRITE |(floor x (- y))| . 1))
        (16 16
            (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
        (16 16 (:REWRITE |(floor (- x) y)| . 2))
        (16 16 (:REWRITE |(floor (- x) y)| . 1))
        (16 16
            (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
        (15 15 (:REWRITE |arith (* (- x) y)|))
        (12 12 (:REWRITE |arith (+ c (+ d x))|))
        (2 2
           (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
        (2 2 (:REWRITE |(/ (/ x))|)))
(LOGAND-MASK-SHIFTED
     (34804 186 (:REWRITE |(floor (- x) y)| . 1))
     (21429 75 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (21429 75 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (18658 75 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (14442 1528 (:META META-INTEGERP-CORRECT))
     (8903 4373
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (8713 5440
           (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (8419 6298 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (8413 11
           (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (8004 319 (:REWRITE MOD-ZERO . 4))
     (7300 7300 (:REWRITE |arith (expt x c)|))
     (7258 7258 (:REWRITE |arith (expt 1/c n)|))
     (7203 11
           (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (6312 5534 (:REWRITE DEFAULT-LESS-THAN-2))
     (6227 217 (:REWRITE FLOOR-=-X/Y . 2))
     (5329 5317
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5298 5298
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4773 359 (:REWRITE DEFAULT-MOD-RATIO))
     (4526 4291 (:REWRITE |(< (- x) (- y))|))
     (4312 4270 (:REWRITE |(< c (- x))|))
     (4291 4291
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4291 4291
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4291 4291
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4291 4291
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4291 4291
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4291 4291
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4291 4291
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4291 4291
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4291 4291 (:REWRITE |(< (/ x) (/ y))|))
     (4253 2320
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4177 27 (:REWRITE MOD-X-I*J))
     (4160 1769 (:REWRITE INTEGERP-MINUS-X))
     (4069 4063 (:REWRITE INTEGERP-<-CONSTANT))
     (4063 4063
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4063 4063 (:REWRITE CONSTANT-<-INTEGERP))
     (3789 3789 (:REWRITE DEFAULT-EXPT-2))
     (3789 3789 (:REWRITE DEFAULT-EXPT-1))
     (3679 3679 (:REWRITE |(expt 1/c n)|))
     (3679 3679 (:REWRITE |(expt (- x) n)|))
     (3483 3483 (:REWRITE |arith (* c (* d x))|))
     (3477 3375
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (3190 264 (:REWRITE |(mod (- x) y)| . 1))
     (3185 293
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (3185 293
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (3108 293 (:REWRITE MOD-CANCEL-*-CONST))
     (2786 1668
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (2664 344 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (2336 1381 (:REWRITE |(< (/ x) 0)|))
     (2249 475 (:REWRITE |(< y (+ (- c) x))|))
     (2232 35
           (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (2120 1994
           (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (2089 1369
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2028 1309 (:REWRITE |(equal (- x) (- y))|))
     (1994 1994
           (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (1994 1994
           (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (1980 1980 (:REWRITE |(< (* x y) 0)|))
     (1586 217 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (1493 340
           (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (1394 193 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (1334 1309 (:REWRITE |(equal (/ x) c)|))
     (1309 1309 (:REWRITE |(equal c (/ x))|))
     (1309 1309 (:REWRITE |(equal (/ x) (/ y))|))
     (1185 1185
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1130 10
           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 1))
     (1089 219
           (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-1))
     (1080 1080
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1080 1080
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1042 997 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (1016 1016 (:REWRITE |(< x (+ c/d y))|))
     (1016 22 (:REWRITE FLOOR-=-X/Y . 4))
     (997 997 (:LINEAR EXPT-LINEAR-UPPER-<))
     (997 997 (:LINEAR EXPT-LINEAR-LOWER-<))
     (997 997 (:LINEAR EXPT->=-1-TWO))
     (997 997 (:LINEAR EXPT->-1-TWO))
     (997 997 (:LINEAR EXPT-<=-1-ONE))
     (997 997 (:LINEAR EXPT-<-1-ONE))
     (997 359 (:REWRITE DEFAULT-MOD-1))
     (970 14 (:REWRITE |(- (if a b c))|))
     (951 429 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (905 193 (:REWRITE FLOOR-CANCEL-*-CONST))
     (884 254
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (870 174
          (:REWRITE |arith (* (expt x m) (expt x (- n)))|))
     (822 822 (:REWRITE FOLD-CONSTS-IN-+))
     (796 486 (:REWRITE |(* (- x) y)|))
     (749 100 (:REWRITE ODD-EXPT-THM))
     (690 690 (:REWRITE |arith (* (- x) y)|))
     (574 274
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (572 176
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (544 244
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (536 536 (:REWRITE |(< 0 (* x y))|))
     (495 45
          (:REWRITE ARITH-BUBBLE-DOWN-*-BUBBLE-DOWN))
     (488 176
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (486 18
          (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
     (486 18
          (:REWRITE |(< (expt x n) (expt x m))|))
     (466 186
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (456 176
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (456 176
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (453 291 (:REWRITE |(floor x 2)| . 2))
     (348 174
          (:REWRITE ARITH-BUBBLE-DOWN-+-MATCH-1))
     (348 87 (:REWRITE |arith (* x 1)|))
     (321 46 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (317 317 (:REWRITE LOGAND-CONSTANT-MASK))
     (270 27 (:REWRITE MOD-X-I*J-V2))
     (266 266
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (266 266
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (264 264 (:REWRITE |(mod x (- y))| . 3))
     (264 264 (:REWRITE |(mod x (- y))| . 2))
     (264 264 (:REWRITE |(mod x (- y))| . 1))
     (264 264 (:REWRITE |(mod (- x) y)| . 3))
     (264 264 (:REWRITE |(mod (- x) y)| . 2))
     (254 254
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (234 234
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (194 16
          (:REWRITE |(not (equal (* (/ x) y) -1))|))
     (194 16 (:REWRITE |(equal (* (/ x) y) -1)|))
     (186 186 (:REWRITE |(floor x (- y))| . 2))
     (186 186 (:REWRITE |(floor x (- y))| . 1))
     (186 186 (:REWRITE |(floor (- x) y)| . 2))
     (174 174 (:REWRITE |arith (+ x (- x))|))
     (170 19 (:REWRITE MOD-ZERO . 2))
     (168 8 (:REWRITE |(* x (expt x n))|))
     (147 9 (:REWRITE |(* (- (/ c)) (expt d n))|))
     (131 125 (:REWRITE |(equal (expt 2 n) c)|))
     (123 123 (:REWRITE LEMMA3))
     (122 14 (:REWRITE |(mod x 2)| . 2))
     (110 22
          (:REWRITE |(equal (floor (+ x y) z) x)|))
     (108 12 (:REWRITE |(* (/ x) (expt x n))|))
     (106 106
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (103 22
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (69 3 (:REWRITE |(* (if a b c) x)|))
     (64 14 (:REWRITE |(mod x 2)| . 1))
     (56 56 (:REWRITE ZP-OPEN))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (45 45
         (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-3))
     (45 9
         (:REWRITE |(* (expt x m) (expt x n))|))
     (24 24 (:REWRITE |arith (+ c (+ d x))|))
     (22 4
         (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
     (22 4
         (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
     (20 20
         (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
     (18 18
         (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (14 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (10 10 (:REWRITE |(mod (floor x y) z)| . 5))
     (10 10 (:REWRITE |(mod (floor x y) z)| . 4))
     (10 10 (:REWRITE |(mod (floor x y) z)| . 3))
     (10 10 (:REWRITE |(mod (floor x y) z)| . 2))
     (10 10
         (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (10 10
         (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (10 10
         (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
     (8 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (5 5 (:REWRITE |(logand c d x)|))
     (5 5 (:REWRITE |(equal (logand x y) -1)|))
     (4 4
        (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
     (3 3
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (3 3
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2 (:REWRITE |(equal x (/ y))|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:REWRITE |(/ (/ x))|))
     (1 1 (:REWRITE FLOOR-X-Y-=-1 . 1)))
(|(logior y x)| (19 19 (:REWRITE LOGAND-CONSTANT-MASK))
                (14 14
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (14 14 (:REWRITE NORMALIZE-ADDENDS))
                (6 6 (:REWRITE DEFAULT-LOGAND-2))
                (6 6 (:REWRITE DEFAULT-LOGAND-1))
                (4 4 (:REWRITE REDUCE-INTEGERP-+))
                (4 4 (:REWRITE INTEGERP-MINUS-X))
                (4 4 (:META META-INTEGERP-CORRECT))
                (2 2
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                (2 2
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1)))
(|(logior (logior x y) z)|
     (86 86
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (86 86
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (74 74 (:REWRITE LOGAND-CONSTANT-MASK))
     (63 31 (:REWRITE DEFAULT-LOGAND-2))
     (44 44
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (44 44 (:REWRITE NORMALIZE-ADDENDS))
     (31 31 (:REWRITE DEFAULT-LOGAND-1))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE |(logand c d x)|)))
(|(logior y x z)| (86 86
                      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                  (86 86
                      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                  (75 75 (:REWRITE LOGAND-CONSTANT-MASK))
                  (63 31 (:REWRITE DEFAULT-LOGAND-2))
                  (44 44
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (44 44 (:REWRITE NORMALIZE-ADDENDS))
                  (31 31 (:REWRITE DEFAULT-LOGAND-1))
                  (6 6 (:REWRITE REDUCE-INTEGERP-+))
                  (6 6 (:REWRITE INTEGERP-MINUS-X))
                  (6 6 (:META META-INTEGERP-CORRECT))
                  (5 5 (:REWRITE |(logand c d x)|)))
(|(logior c d x)| (86 86
                      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                  (86 86
                      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                  (74 74 (:REWRITE LOGAND-CONSTANT-MASK))
                  (63 31 (:REWRITE DEFAULT-LOGAND-2))
                  (44 44
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (44 44 (:REWRITE NORMALIZE-ADDENDS))
                  (31 31 (:REWRITE DEFAULT-LOGAND-1))
                  (6 6 (:REWRITE REDUCE-INTEGERP-+))
                  (6 6 (:REWRITE INTEGERP-MINUS-X))
                  (6 6 (:META META-INTEGERP-CORRECT))
                  (5 5 (:REWRITE |(logand c d x)|)))
(LOGIOR-0-X (3 3
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (3 3 (:REWRITE NORMALIZE-ADDENDS))
            (1 1 (:REWRITE REDUCE-INTEGERP-+))
            (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
            (1 1 (:REWRITE INTEGERP-MINUS-X))
            (1 1 (:META META-INTEGERP-CORRECT)))
(|(logior 1 x)| (532 36
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
                (304 24 (:REWRITE |(< (- x) c)|))
                (208 4 (:LINEAR LOGAND-BOUNDS-POS . 2))
                (204 4 (:LINEAR LOGAND-BOUNDS-NEG . 2))
                (204 4 (:LINEAR LOGAND-BOUNDS-NEG . 1))
                (51 51
                    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                (51 51
                    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                (36 36 (:REWRITE THE-FLOOR-ABOVE))
                (36 36
                    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                (36 36
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                (36 36
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (36 36 (:REWRITE DEFAULT-LESS-THAN-2))
                (31 31
                    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                (30 14
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
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
                (24 24 (:REWRITE |(< (- x) (- y))|))
                (21 21
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                (20 20 (:REWRITE |(equal c (/ x))|))
                (20 20 (:REWRITE |(equal (/ x) c)|))
                (20 20 (:REWRITE |(equal (/ x) (/ y))|))
                (20 20 (:REWRITE |(equal (- x) (- y))|))
                (18 18 (:REWRITE |(equal (+ (- c) x) y)|))
                (14 14
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                (12 12 (:REWRITE SIMPLIFY-SUMS-<))
                (12 12
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (12 12
                    (:REWRITE REMOVE-STRICT-INEQUALITIES))
                (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (12 12 (:REWRITE INTEGERP-<-CONSTANT))
                (12 12 (:REWRITE CONSTANT-<-INTEGERP))
                (12 12 (:REWRITE |(< (+ c/d x) y)|))
                (12 12 (:REWRITE |(< (* x y) 0)|))
                (12 12 (:REWRITE |(* (- x) y)|))
                (11 11 (:REWRITE REDUCE-INTEGERP-+))
                (11 11 (:META META-INTEGERP-CORRECT))
                (6 6 (:REWRITE LOGAND-CONSTANT-MASK))
                (4 4
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                (4 4 (:LINEAR LOGAND-BOUNDS-POS . 1))
                (3 3 (:REWRITE DEFAULT-LOGAND-2))
                (3 3 (:REWRITE DEFAULT-LOGAND-1))
                (3 3 (:REWRITE |(floor x 2)| . 2))
                (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(LOGIOR--1-X)
(LOGIOR-X-X (4 4
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (4 4 (:REWRITE NORMALIZE-ADDENDS))
            (1 1 (:REWRITE REDUCE-INTEGERP-+))
            (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
            (1 1 (:REWRITE INTEGERP-MINUS-X))
            (1 1 (:META META-INTEGERP-CORRECT)))
(LOGIOR-BOUNDS-POS
     (182 182
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (53 20
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (44 26 (:REWRITE DEFAULT-LESS-THAN-2))
     (41 26 (:REWRITE |(< (- x) (- y))|))
     (30 30
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (26 26 (:REWRITE THE-FLOOR-ABOVE))
     (26 26
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 26
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
     (24 24 (:REWRITE CONSTANT-<-INTEGERP))
     (14 14 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:REWRITE LOGAND-CONSTANT-MASK))
     (8 8 (:REWRITE DEFAULT-LOGAND-2))
     (8 8 (:REWRITE DEFAULT-LOGAND-1))
     (8 8 (:REWRITE |(< y (+ (- c) x))|))
     (8 8 (:REWRITE |(< x (+ c/d y))|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE LOGAND-BOUNDS-POS . 1)))
(LOGIOR-BOUNDS-NEG
     (67 34
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 56
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (54 36 (:REWRITE DEFAULT-LESS-THAN-2))
     (51 36 (:REWRITE |(< (- x) (- y))|))
     (38 38
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (36 36 (:REWRITE THE-FLOOR-ABOVE))
     (36 36
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (36 36
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (36 36
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (34 34 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (34 34 (:REWRITE INTEGERP-<-CONSTANT))
     (34 34 (:REWRITE CONSTANT-<-INTEGERP))
     (26 26 (:REWRITE SIMPLIFY-SUMS-<))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (14 14 (:REWRITE LOGAND-CONSTANT-MASK))
     (14 14 (:REWRITE INTEGERP-MINUS-X))
     (14 14 (:REWRITE DEFAULT-LOGAND-2))
     (14 14 (:REWRITE DEFAULT-LOGAND-1))
     (14 14 (:REWRITE |(< (/ x) 0)|))
     (14 14 (:REWRITE |(< (* x y) 0)|))
     (14 14 (:META META-INTEGERP-CORRECT))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (6 6 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (1 1 (:REWRITE LOGAND-BOUNDS-POS . 1)))
(|(equal (logior x y) 0)|
     (356 24
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (204 16 (:REWRITE |(< (- x) c)|))
     (104 2 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (104 2 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (102 2 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (102 2 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (42 42
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (42 42
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (24 24 (:REWRITE THE-FLOOR-ABOVE))
     (24 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (15 15 (:REWRITE NORMALIZE-ADDENDS))
     (12 8 (:REWRITE |(equal (- x) (- y))|))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
     (3 3 (:REWRITE DEFAULT-LOGAND-2))
     (3 3 (:REWRITE DEFAULT-LOGAND-1)))
(|(< (logior x y) 0)|
     (9 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 5 (:REWRITE |(< (- x) (- y))|))
     (8 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
     (1 1 (:REWRITE DEFAULT-LOGAND-2))
     (1 1 (:REWRITE DEFAULT-LOGAND-1))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(< 0 (logior x y))|
     (279 31
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (104 2 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (35 31 (:REWRITE DEFAULT-LESS-THAN-2))
     (31 31 (:REWRITE THE-FLOOR-ABOVE))
     (31 31
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (26 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 25
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (25 25
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (25 25
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (25 25
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (25 25
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (25 25
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (25 25
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (25 25
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (25 25 (:REWRITE |(< (/ x) (/ y))|))
     (25 25 (:REWRITE |(< (- x) (- y))|))
     (20 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (17 17
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (17 17 (:REWRITE INTEGERP-<-CONSTANT))
     (17 17 (:REWRITE CONSTANT-<-INTEGERP))
     (16 16 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (13 13
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (9 9 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE LOGAND-CONSTANT-MASK))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE DEFAULT-LOGAND-2))
     (4 4 (:REWRITE DEFAULT-LOGAND-1))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(|(logior (* 2 x) (* 2 y))|
     (6955 367
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5365 145 (:REWRITE |(< (+ c/d x) y)|))
     (4501 410
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3084 269 (:REWRITE |(< (- x) c)|))
     (2428 42 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (2428 42 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (2107 43
           (:REWRITE |(< (/ x) y) with (< x 0)|))
     (848 848
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (780 15
          (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (723 723
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (483 367
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (457 457 (:REWRITE THE-FLOOR-ABOVE))
     (457 457 (:REWRITE DEFAULT-LESS-THAN-2))
     (420 420
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (368 368 (:REWRITE |(* (- x) y)|))
     (269 269
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (269 269
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (269 269
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (269 269
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (269 269 (:REWRITE |(< c (- x))|))
     (269 269
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (269 269
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (269 269
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (269 269
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (269 269 (:REWRITE |(< (/ x) (/ y))|))
     (269 269 (:REWRITE |(< (- x) (- y))|))
     (217 82
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (156 156 (:REWRITE SIMPLIFY-SUMS-<))
     (156 156
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (156 156
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (156 156
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (156 156 (:REWRITE INTEGERP-<-CONSTANT))
     (156 156 (:REWRITE CONSTANT-<-INTEGERP))
     (145 145 (:REWRITE |(< (* x y) 0)|))
     (104 104 (:REWRITE |(equal (/ x) (/ y))|))
     (103 103 (:REWRITE |(equal c (/ x))|))
     (103 103 (:REWRITE |(equal (/ x) c)|))
     (82 82
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (79 79
         (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (79 79
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (79 79
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (79 74 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (64 64 (:REWRITE LOGAND-CONSTANT-MASK))
     (61 61 (:REWRITE REDUCE-INTEGERP-+))
     (61 61 (:REWRITE INTEGERP-MINUS-X))
     (61 61 (:META META-INTEGERP-CORRECT))
     (60 60 (:REWRITE |(equal (+ (- c) x) y)|))
     (57 57 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (55 55 (:REWRITE |(- (- x))|))
     (54 2 (:REWRITE |(not (equal x (/ y)))|))
     (54 2 (:REWRITE |(equal x (/ y))|))
     (43 43
         (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (30 2
         (:REWRITE |(not (equal x (- (/ y))))|))
     (30 2 (:REWRITE |(equal x (- (/ y)))|))
     (22 22 (:REWRITE REDUCE-RATIONALP-+))
     (22 22 (:REWRITE REDUCE-RATIONALP-*))
     (22 22 (:REWRITE RATIONALP-MINUS-X))
     (22 22 (:META META-RATIONALP-CORRECT))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (15 15
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (2 2 (:REWRITE |(floor x 2)| . 2)))
(|(logior (floor x 2) (floor y 2))|
     (8510 520
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4254 274 (:REWRITE |(< (+ c/d x) y)|))
     (3700 98 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (3178 314 (:REWRITE |(< (- x) c)|))
     (3110 618
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3102 98 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (3102 98 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (3082 98 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (1791 1790
           (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (1678 1678
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1588 1588
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (879 879 (:REWRITE |(* (- x) y)|))
     (726 686 (:REWRITE DEFAULT-LESS-THAN-2))
     (686 686 (:REWRITE THE-FLOOR-ABOVE))
     (584 4 (:REWRITE |(equal x (/ y))|))
     (520 520
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (504 4 (:REWRITE |(not (equal x (/ y)))|))
     (463 190
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (379 84 (:REWRITE DEFAULT-LOGAND-2))
     (354 314 (:REWRITE |(< (- x) (- y))|))
     (354 184 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (346 344
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (331 283 (:REWRITE REDUCE-INTEGERP-+))
     (320 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
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
     (312 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (306 306 (:REWRITE |(equal (/ x) (/ y))|))
     (284 284 (:REWRITE |(equal (+ (- c) x) y)|))
     (283 283 (:META META-INTEGERP-CORRECT))
     (282 282 (:REWRITE |(equal c (/ x))|))
     (282 282 (:REWRITE |(equal (/ x) c)|))
     (274 274 (:REWRITE |(< (* x y) 0)|))
     (270 80
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (246 206
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (246 206
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (215 84 (:REWRITE DEFAULT-LOGAND-1))
     (206 206 (:REWRITE SIMPLIFY-SUMS-<))
     (206 206
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (206 206 (:REWRITE INTEGERP-<-CONSTANT))
     (206 206 (:REWRITE CONSTANT-<-INTEGERP))
     (190 190
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (130 130 (:REWRITE LOGAND-CONSTANT-MASK))
     (107 107 (:REWRITE |(floor x 2)| . 2))
     (102 102 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (100 100 (:TYPE-PRESCRIPTION ABS))
     (35 35
         (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (35 35
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (35 35
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (9 9
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (9 9
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (9 9
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(LOGIOR-FLOOR-EXPT-2-N
     (155068 28 (:REWRITE FLOOR-=-X/Y . 4))
     (51066 1366 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (49988 268 (:LINEAR LOGIOR-BOUNDS-POS . 2))
     (49988 268 (:LINEAR LOGIOR-BOUNDS-POS . 1))
     (49840 268 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (45692 268 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (44554 26 (:REWRITE |(equal (+ (- c) x) y)|))
     (28134 2518 (:REWRITE THE-FLOOR-ABOVE))
     (26044 1366 (:REWRITE FLOOR-=-X/Y . 3))
     (24682 1366 (:REWRITE FLOOR-=-X/Y . 2))
     (23220 94
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (22743 110
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (13208 624 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (11224 624 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (8796 1366 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (8796 1366 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (7321 5545 (:REWRITE NORMALIZE-ADDENDS))
     (6052 1366 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5832 5832 (:REWRITE |(expt 1/c n)|))
     (5832 5832 (:REWRITE |(expt (- x) n)|))
     (5720 104 (:REWRITE |(< (logior x y) 0)|))
     (5101 5101
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4842 1338
           (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4842 1338
           (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (4842 1338
           (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (4375 4375
           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (4375 4375
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (4375 4375
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (4006 4006 (:REWRITE REDUCE-INTEGERP-+))
     (4006 4006 (:REWRITE INTEGERP-MINUS-X))
     (4006 4006 (:META META-INTEGERP-CORRECT))
     (3178 2074
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3178 2074
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2368 1338
           (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2368 1338
           (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (2222 2074 (:REWRITE DEFAULT-LESS-THAN-2))
     (2102 2074
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2102 2074
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2074 2074 (:REWRITE SIMPLIFY-SUMS-<))
     (2074 2074
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2074 2074
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2074 2074 (:REWRITE INTEGERP-<-CONSTANT))
     (2074 2074 (:REWRITE CONSTANT-<-INTEGERP))
     (2074 2074
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2074 2074
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2074 2074
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2074 2074
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2074 2074 (:REWRITE |(< c (- x))|))
     (2074 2074
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2074 2074
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2074 2074
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2074 2074
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2074 2074 (:REWRITE |(< (/ x) (/ y))|))
     (2074 2074 (:REWRITE |(< (- x) c)|))
     (2074 2074 (:REWRITE |(< (- x) (- y))|))
     (1926 1926
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1926 1926
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1926 1926 (:REWRITE |(< (/ x) 0)|))
     (1926 1926 (:REWRITE |(< (* x y) 0)|))
     (1338 1338 (:REWRITE |(floor x (- y))| . 2))
     (1338 1338 (:REWRITE |(floor x (- y))| . 1))
     (1338 1338 (:REWRITE |(floor (- x) y)| . 2))
     (1338 1338 (:REWRITE |(floor (- x) y)| . 1))
     (1336 56 (:REWRITE |(* (* x y) z)|))
     (888 444 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (728 56 (:REWRITE |(* (/ c) (expt d n))|))
     (700 86 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (684 86
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (608 40 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
     (520 72 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (466 466
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (444 444 (:REWRITE |(+ x (- x))|))
     (312 312
          (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
     (312 312 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (192 28
          (:REWRITE |(equal (floor (+ x y) z) x)|))
     (192 8 (:REWRITE |(* x (+ y z))|))
     (148 148
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (148 148
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (148 148 (:REWRITE |(< 0 (/ x))|))
     (148 148 (:REWRITE |(< 0 (* x y))|))
     (102 102
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (94 94
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (94 94 (:REWRITE |(equal c (/ x))|))
     (94 94 (:REWRITE |(equal (/ x) c)|))
     (94 94 (:REWRITE |(equal (/ x) (/ y))|))
     (94 94 (:REWRITE |(equal (- x) c)|))
     (94 94 (:REWRITE |(equal (- x) (- y))|))
     (72 72 (:REWRITE |(* c (* d x))|))
     (65 65 (:TYPE-PRESCRIPTION ABS))
     (32 16 (:REWRITE |(* x (- y))|))
     (14 14 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
     (14 14 (:REWRITE |(* 1/2 (floor x y))| . 3))
     (14 14 (:REWRITE |(* 1/2 (floor x y))| . 2))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (8 8 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(|(mod (logior x y) 2)| (78 2 (:LINEAR MOD-BOUNDS-3))
                        (76 7 (:REWRITE |(* y x)|))
                        (67 5 (:REWRITE DEFAULT-MOD-RATIO))
                        (57 57
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (43 43 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                        (28 28
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (28 28 (:REWRITE NORMALIZE-ADDENDS))
                        (25 25 (:REWRITE |(* (- x) y)|))
                        (19 19
                            (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
                        (19 19
                            (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
                        (19 19
                            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
                        (19 19
                            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
                        (14 14 (:REWRITE REDUCE-INTEGERP-+))
                        (14 14 (:META META-INTEGERP-CORRECT))
                        (13 5 (:REWRITE DEFAULT-MOD-1))
                        (11 11
                            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                        (11 11
                            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                        (5 5 (:REWRITE |(mod x 2)| . 2))
                        (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
                        (1 1 (:REWRITE DEFAULT-LOGAND-2))
                        (1 1 (:REWRITE DEFAULT-LOGAND-1))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(FLOOR-2-N-IND
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (11 11
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (11 11
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (11 11 (:REWRITE |(< (/ x) (/ y))|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9 (:REWRITE |(< (- x) c)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE ZIP-OPEN))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|)))
(|(integerp (* 1/2 (logior x y)))|
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (8 8 (:REWRITE |(* (- x) y)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:META META-INTEGERP-CORRECT))
     (3 3
        (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
     (3 3
        (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
     (1 1 (:REWRITE DEFAULT-LOGAND-2))
     (1 1 (:REWRITE DEFAULT-LOGAND-1))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(BREAK-LOGIOR-APART
     (1346 21 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (835 21 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (667 125
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (524 8 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (498 106
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (488 24 (:REWRITE |(< (+ c/d x) y)|))
     (471 471
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (471 471
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (376 4 (:LINEAR MOD-BOUNDS-1))
     (275 144 (:REWRITE THE-FLOOR-ABOVE))
     (224 8 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (160 8 (:REWRITE |(< x (+ c/d y))|))
     (156 141 (:REWRITE DEFAULT-LESS-THAN-2))
     (148 148
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (126 126 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (126 126 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (112 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (107 91 (:REWRITE INTEGERP-MINUS-X))
     (106 106
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (105 90
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (105 90 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (102 51 (:REWRITE |(* y x)|))
     (96 96 (:REWRITE |(< (* x y) 0)|))
     (92 80 (:REWRITE NORMALIZE-ADDENDS))
     (90 90 (:REWRITE SIMPLIFY-SUMS-<))
     (90 90
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (90 90 (:REWRITE INTEGERP-<-CONSTANT))
     (90 90 (:REWRITE CONSTANT-<-INTEGERP))
     (90 90
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (90 90
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (90 90
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (90 90
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (90 90 (:REWRITE |(< c (- x))|))
     (90 90
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (90 90
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (90 90
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (90 90
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (90 90 (:REWRITE |(< (/ x) (/ y))|))
     (90 90 (:REWRITE |(< (- x) c)|))
     (90 90 (:REWRITE |(< (- x) (- y))|))
     (87 87 (:REWRITE REDUCE-INTEGERP-+))
     (87 87 (:META META-INTEGERP-CORRECT))
     (77 77
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (74 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (74 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (74 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (57 57
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (57 57
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (57 57 (:REWRITE |(< (/ x) 0)|))
     (52 4 (:REWRITE MOD-ZERO . 4))
     (52 4 (:REWRITE CANCEL-MOD-+))
     (48 8 (:REWRITE FLOOR-=-X/Y . 3))
     (48 8 (:REWRITE FLOOR-=-X/Y . 2))
     (46 14 (:REWRITE |(floor x 2)| . 2))
     (38 38 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (29 29 (:REWRITE |(< 0 (* x y))|))
     (24 8 (:REWRITE |(* (- x) y)|))
     (24 4 (:REWRITE MOD-ZERO . 3))
     (24 4 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (24 4 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (22 6 (:REWRITE |(mod x 2)| . 2))
     (20 8 (:REWRITE |(- (* c x))|))
     (19 19 (:TYPE-PRESCRIPTION ABS))
     (18 6 (:REWRITE DEFAULT-MOD-RATIO))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (17 17
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (17 17 (:REWRITE |(< 0 (/ x))|))
     (15 15
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (12 2 (:LINEAR MOD-BOUNDS-3))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (8 8 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (8 8
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (8 8
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (8 8 (:REWRITE FLOOR-CANCEL-*-CONST))
     (8 8 (:REWRITE |(floor x (- y))| . 2))
     (8 8 (:REWRITE |(floor x (- y))| . 1))
     (8 8
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (8 8
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (8 8 (:REWRITE |(floor (- x) y)| . 2))
     (8 8 (:REWRITE |(floor (- x) y)| . 1))
     (8 8
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (8 8
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (6 6 (:REWRITE DEFAULT-MOD-1))
     (6 3 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (6 3 (:DEFINITION FIX))
     (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (4 4
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE MOD-CANCEL-*-CONST))
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
     (4 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (4 4
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (3 3 (:REWRITE |(+ x (- x))|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(CROCK-0 (639 639
              (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
         (364 182 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (364 182 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
         (358 10 (:REWRITE MOD-X-Y-=-X+Y . 2))
         (330 10 (:REWRITE CANCEL-MOD-+))
         (210 10 (:REWRITE MOD-ZERO . 3))
         (182 182 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
         (174 10 (:REWRITE MOD-ZERO . 4))
         (160 160 (:REWRITE |(expt 1/c n)|))
         (160 160 (:REWRITE |(expt (- x) n)|))
         (130 10 (:REWRITE |(integerp (- x))|))
         (129 72 (:REWRITE DEFAULT-LESS-THAN-2))
         (119 42
              (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
         (110 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
         (110 10
              (:REWRITE |(mod (+ x (- (mod a b))) y)|))
         (102 42
              (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
         (97 85 (:META META-INTEGERP-CORRECT))
         (87 87 (:REWRITE INTEGERP-MINUS-X))
         (84 72
             (:REWRITE REMOVE-STRICT-INEQUALITIES))
         (80 10 (:REWRITE MOD-X-Y-=-X+Y . 3))
         (80 10 (:REWRITE DEFAULT-MOD-RATIO))
         (78 3 (:LINEAR EXPT-X->=-X))
         (78 3 (:LINEAR EXPT-X->-X))
         (75 75
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (75 72 (:REWRITE |(< (- x) (- y))|))
         (72 72 (:REWRITE THE-FLOOR-ABOVE))
         (72 72
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
         (72 72
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
         (72 72
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
         (72 72 (:REWRITE INTEGERP-<-CONSTANT))
         (72 72 (:REWRITE CONSTANT-<-INTEGERP))
         (72 72
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
         (72 72
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
         (72 72
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
         (72 72
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
         (72 72 (:REWRITE |(< c (- x))|))
         (72 72
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
         (72 72
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
         (72 72
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
         (72 72
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
         (72 72 (:REWRITE |(< (/ x) (/ y))|))
         (72 72 (:REWRITE |(< (- x) c)|))
         (58 27
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
         (56 56 (:REWRITE REMOVE-WEAK-INEQUALITIES))
         (50 10
             (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
         (50 10 (:REWRITE MOD-CANCEL-*-CONST))
         (50 10
             (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
         (50 10
             (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
         (41 16 (:REWRITE |(equal (/ x) c)|))
         (31 11 (:REWRITE |(* (- x) y)|))
         (27 27
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
         (27 27
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
         (27 27 (:REWRITE |(< 0 (/ x))|))
         (27 27 (:REWRITE |(< 0 (* x y))|))
         (20 20 (:TYPE-PRESCRIPTION RATIONALP-MOD))
         (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
         (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
         (20 20 (:REWRITE |(< (/ x) 0)|))
         (20 20 (:REWRITE |(< (* x y) 0)|))
         (16 16
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (16 16
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (16 16 (:REWRITE |(equal c (/ x))|))
         (16 16 (:REWRITE |(equal (/ x) (/ y))|))
         (16 16 (:REWRITE |(equal (- x) (- y))|))
         (14 14
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
         (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (14 14
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (14 14 (:REWRITE ODD-EXPT-THM))
         (14 14
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (14 14 (:REWRITE |(equal (- x) c)|))
         (11 11 (:REWRITE |(< (+ c/d x) y)|))
         (11 11 (:REWRITE |(< (+ (- c) x) y)|))
         (10 10
             (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
         (10 10 (:REWRITE DEFAULT-MOD-1))
         (10 10 (:REWRITE |(mod x (- y))| . 3))
         (10 10 (:REWRITE |(mod x (- y))| . 2))
         (10 10 (:REWRITE |(mod x (- y))| . 1))
         (10 10
             (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
         (10 10 (:REWRITE |(mod (- x) y)| . 3))
         (10 10 (:REWRITE |(mod (- x) y)| . 2))
         (10 10 (:REWRITE |(mod (- x) y)| . 1))
         (10 10
             (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
         (10 10 (:REWRITE |(- (* c x))|))
         (9 9 (:REWRITE |arith (expt x c)|))
         (9 9 (:REWRITE |arith (expt 1/c n)|))
         (9 9 (:REWRITE |(+ c (+ d x))|))
         (8 8
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (7 7 (:REWRITE |(* c (* d x))|))
         (6 6
            (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
         (6 6
            (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
         (6 6
            (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
         (6 6
            (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
         (6 6
            (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
         (4 4 (:REWRITE |(< y (+ (- c) x))|))
         (4 4 (:REWRITE |(< x (+ c/d y))|))
         (4 1 (:REWRITE SUM-IS-EVEN . 2))
         (3 3 (:REWRITE FOLD-CONSTS-IN-+))
         (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
         (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
         (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
         (3 3 (:LINEAR EXPT->=-1-TWO))
         (3 3 (:LINEAR EXPT->-1-TWO))
         (3 3 (:LINEAR EXPT-<=-1-TWO))
         (3 3 (:LINEAR EXPT-<=-1-ONE))
         (3 3 (:LINEAR EXPT-<-1-TWO))
         (3 3 (:LINEAR EXPT-<-1-ONE))
         (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
         (2 2 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
         (2 2 (:REWRITE |(not (equal x (/ y)))|))
         (2 2 (:REWRITE |(equal x (/ y))|))
         (2 2 (:REWRITE |(/ (/ x))|))
         (1 1
            (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
         (1 1
            (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(CROCK-1 (643 643
              (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
         (368 184 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (368 184 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
         (358 10 (:REWRITE MOD-X-Y-=-X+Y . 2))
         (330 10 (:REWRITE CANCEL-MOD-+))
         (210 10 (:REWRITE MOD-ZERO . 3))
         (184 184 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
         (174 10 (:REWRITE MOD-ZERO . 4))
         (130 10 (:REWRITE |(integerp (- x))|))
         (110 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
         (110 10
              (:REWRITE |(mod (+ x (- (mod a b))) y)|))
         (109 109 (:REWRITE |(expt 1/c n)|))
         (109 109 (:REWRITE |(expt (- x) n)|))
         (108 63 (:REWRITE DEFAULT-LESS-THAN-2))
         (96 84 (:META META-INTEGERP-CORRECT))
         (91 37
             (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
         (88 37
             (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
         (86 86 (:REWRITE INTEGERP-MINUS-X))
         (80 10 (:REWRITE MOD-X-Y-=-X+Y . 3))
         (80 10 (:REWRITE DEFAULT-MOD-RATIO))
         (78 3 (:LINEAR EXPT-X->=-X))
         (78 3 (:LINEAR EXPT-X->-X))
         (75 63
             (:REWRITE REMOVE-STRICT-INEQUALITIES))
         (72 72
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (66 63 (:REWRITE |(< (- x) (- y))|))
         (63 63 (:REWRITE THE-FLOOR-ABOVE))
         (63 63
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
         (63 63
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
         (63 63
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
         (63 63 (:REWRITE INTEGERP-<-CONSTANT))
         (63 63 (:REWRITE CONSTANT-<-INTEGERP))
         (63 63
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
         (63 63
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
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
         (63 63
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
         (63 63 (:REWRITE |(< (/ x) (/ y))|))
         (63 63 (:REWRITE |(< (- x) c)|))
         (50 10
             (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
         (50 10 (:REWRITE MOD-CANCEL-*-CONST))
         (50 10
             (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
         (50 10
             (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
         (47 47 (:REWRITE REMOVE-WEAK-INEQUALITIES))
         (31 11 (:REWRITE |(* (- x) y)|))
         (29 23
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
         (22 22 (:TYPE-PRESCRIPTION RATIONALP-MOD))
         (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
         (22 22 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
         (22 22
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
         (22 22
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
         (22 22 (:REWRITE |(< 0 (/ x))|))
         (22 22 (:REWRITE |(< 0 (* x y))|))
         (21 1 (:REWRITE SUM-IS-EVEN . 2))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
         (20 20 (:REWRITE |(< (/ x) 0)|))
         (20 20 (:REWRITE |(< (* x y) 0)|))
         (12 12
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
         (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (12 12
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (12 12
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (12 12
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (12 12
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (12 12 (:REWRITE |(equal c (/ x))|))
         (12 12 (:REWRITE |(equal (/ x) c)|))
         (12 12 (:REWRITE |(equal (/ x) (/ y))|))
         (12 12 (:REWRITE |(equal (- x) c)|))
         (12 12 (:REWRITE |(equal (- x) (- y))|))
         (10 10 (:REWRITE ODD-EXPT-THM))
         (10 10
             (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
         (10 10 (:REWRITE DEFAULT-MOD-1))
         (10 10 (:REWRITE CROCK-0))
         (10 10 (:REWRITE |(mod x (- y))| . 3))
         (10 10 (:REWRITE |(mod x (- y))| . 2))
         (10 10 (:REWRITE |(mod x (- y))| . 1))
         (10 10
             (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
         (10 10 (:REWRITE |(mod (- x) y)| . 3))
         (10 10 (:REWRITE |(mod (- x) y)| . 2))
         (10 10 (:REWRITE |(mod (- x) y)| . 1))
         (10 10
             (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
         (10 10 (:REWRITE |(- (* c x))|))
         (9 9 (:REWRITE |arith (expt x c)|))
         (9 9 (:REWRITE |arith (expt 1/c n)|))
         (9 9 (:REWRITE |(< (+ c/d x) y)|))
         (9 9 (:REWRITE |(< (+ (- c) x) y)|))
         (9 9 (:REWRITE |(+ c (+ d x))|))
         (7 7
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (6 6 (:REWRITE |(* c (* d x))|))
         (6 6
            (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
         (6 6
            (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
         (6 6
            (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
         (5 5
            (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
         (5 5
            (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
         (4 4 (:REWRITE |(< y (+ (- c) x))|))
         (4 4 (:REWRITE |(< x (+ c/d y))|))
         (3 3 (:REWRITE FOLD-CONSTS-IN-+))
         (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
         (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
         (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
         (3 3 (:LINEAR EXPT->=-1-TWO))
         (3 3 (:LINEAR EXPT->-1-TWO))
         (3 3 (:LINEAR EXPT-<=-1-TWO))
         (3 3 (:LINEAR EXPT-<=-1-ONE))
         (3 3 (:LINEAR EXPT-<-1-TWO))
         (3 3 (:LINEAR EXPT-<-1-ONE))
         (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
         (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
         (1 1
            (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
         (1 1
            (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(CROCK-2 (828 828
              (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
         (716 20 (:REWRITE MOD-X-Y-=-X+Y . 2))
         (660 20 (:REWRITE CANCEL-MOD-+))
         (420 20 (:REWRITE MOD-ZERO . 3))
         (404 202 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (348 20 (:REWRITE MOD-ZERO . 4))
         (315 15 (:LINEAR MOD-BOUNDS-3))
         (260 20 (:REWRITE |(integerp (- x))|))
         (250 10 (:REWRITE MOD-ZERO . 1))
         (248 10 (:LINEAR EXPT-X->=-X))
         (248 10 (:LINEAR EXPT-X->-X))
         (220 20 (:REWRITE |(mod (+ x (mod a b)) y)|))
         (220 20
              (:REWRITE |(mod (+ x (- (mod a b))) y)|))
         (202 202 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
         (176 176 (:REWRITE |(expt 1/c n)|))
         (176 176 (:REWRITE |(expt (- x) n)|))
         (160 20 (:REWRITE MOD-X-Y-=-X+Y . 3))
         (160 20 (:REWRITE DEFAULT-MOD-RATIO))
         (142 32
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (115 106 (:META META-INTEGERP-CORRECT))
         (106 106 (:REWRITE REDUCE-INTEGERP-+))
         (106 106 (:REWRITE INTEGERP-MINUS-X))
         (100 20
              (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
         (100 20 (:REWRITE MOD-CANCEL-*-CONST))
         (100 20
              (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
         (100 20
              (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
         (85 19
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (80 10 (:REWRITE MOD-ZERO . 2))
         (79 79 (:TYPE-PRESCRIPTION RATIONALP-MOD))
         (79 79 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
         (79 79 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
         (74 62 (:REWRITE DEFAULT-LESS-THAN-2))
         (68 62 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
         (62 62 (:REWRITE THE-FLOOR-ABOVE))
         (62 62
             (:REWRITE REMOVE-STRICT-INEQUALITIES))
         (62 62
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
         (62 62
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
         (62 62
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
         (62 62 (:REWRITE INTEGERP-<-CONSTANT))
         (62 62 (:REWRITE CONSTANT-<-INTEGERP))
         (62 62
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
         (62 62
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
         (62 62
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
         (62 62
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
         (62 62 (:REWRITE |(< c (- x))|))
         (62 62
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
         (62 62
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
         (62 62
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
         (62 62
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
         (62 62 (:REWRITE |(< (/ x) (/ y))|))
         (62 62 (:REWRITE |(< (- x) c)|))
         (62 62 (:REWRITE |(< (- x) (- y))|))
         (60 35
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
         (60 20 (:REWRITE |(* (- x) y)|))
         (59 34 (:REWRITE |(equal (/ x) c)|))
         (57 13
             (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
         (57 13
             (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
         (53 27
             (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
         (40 10
             (:REWRITE |(equal (mod (+ x y) z) x)|))
         (34 34
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (34 34
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (34 34 (:REWRITE |(equal c (/ x))|))
         (34 34 (:REWRITE |(equal (/ x) (/ y))|))
         (34 34 (:REWRITE |(equal (- x) (- y))|))
         (33 27
             (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
         (33 27
             (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
         (32 32
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
         (32 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (32 32
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (32 32 (:REWRITE |(equal (- x) c)|))
         (25 25 (:REWRITE |arith (expt x c)|))
         (25 25 (:REWRITE |arith (expt 1/c n)|))
         (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
         (20 20
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
         (20 20
             (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
         (20 20 (:REWRITE DEFAULT-MOD-1))
         (20 20 (:REWRITE |(mod x (- y))| . 3))
         (20 20 (:REWRITE |(mod x (- y))| . 2))
         (20 20 (:REWRITE |(mod x (- y))| . 1))
         (20 20
             (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
         (20 20 (:REWRITE |(mod (- x) y)| . 3))
         (20 20 (:REWRITE |(mod (- x) y)| . 2))
         (20 20 (:REWRITE |(mod (- x) y)| . 1))
         (20 20
             (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
         (20 20 (:REWRITE |(< (/ x) 0)|))
         (20 20 (:REWRITE |(< (* x y) 0)|))
         (20 20 (:REWRITE |(- (* c x))|))
         (20 20
             (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
         (20 20
             (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
         (20 20
             (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
         (18 18
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
         (18 18
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
         (18 18 (:REWRITE |(< 0 (/ x))|))
         (18 18 (:REWRITE |(< 0 (* x y))|))
         (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
         (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
         (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
         (10 10 (:LINEAR EXPT->=-1-TWO))
         (10 10 (:LINEAR EXPT->-1-TWO))
         (10 10 (:LINEAR EXPT-<=-1-TWO))
         (10 10 (:LINEAR EXPT-<=-1-ONE))
         (10 10 (:LINEAR EXPT-<-1-TWO))
         (10 10 (:LINEAR EXPT-<-1-ONE))
         (4 4 (:REWRITE ODD-EXPT-THM))
         (4 4 (:REWRITE |(* c (* d x))|))
         (3 3
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (2 2 (:REWRITE |(not (equal x (/ y)))|))
         (2 2 (:REWRITE |(equal x (/ y))|))
         (2 2 (:REWRITE |(< (+ c/d x) y)|))
         (2 2 (:REWRITE |(< (+ (- c) x) y)|))
         (2 2 (:REWRITE |(/ (/ x))|))
         (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3)))
(MOD-LOGIOR-EXPT-2-N (15631 1228 (:REWRITE MOD-ZERO . 4))
                     (6311 277 (:LINEAR MOD-BOUNDS-3))
                     (6092 1139
                           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
                     (6031 1002 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
                     (4843 1854
                           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                     (4220 1358 (:REWRITE |(/ (expt x n))|))
                     (2474 1927 (:REWRITE |(< (- x) c)|))
                     (2447 2447 (:REWRITE |(expt 1/c n)|))
                     (2447 2447 (:REWRITE |(expt (- x) n)|))
                     (1927 1927 (:REWRITE |(< c (- x))|))
                     (1927 1927 (:REWRITE |(< (- x) (- y))|))
                     (1716 1701 (:REWRITE INTEGERP-MINUS-X))
                     (1506 91 (:REWRITE |(< y (+ (- c) x))|))
                     (1340 65 (:REWRITE ODD-EXPT-THM))
                     (1139 1139 (:REWRITE |(mod x (- y))| . 1))
                     (1032 73 (:REWRITE |(integerp (expt x n))|))
                     (982 38 (:REWRITE |(* (* x y) z)|))
                     (794 310 (:REWRITE |(* y x)|))
                     (700 44
                          (:REWRITE |(< (/ x) y) with (< 0 x)|))
                     (550 41 (:REWRITE |(* (/ c) (expt d n))|))
                     (452 28 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
                     (429 429 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                     (384 12 (:REWRITE |(integerp (- x))|))
                     (294 294 (:REWRITE |(< 0 (/ x))|))
                     (236 41 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
                     (186 15
                          (:REWRITE |(* (- (/ c)) (expt d n))|))
                     (171 171 (:REWRITE FOLD-CONSTS-IN-+))
                     (130 130 (:REWRITE |(floor x 2)| . 2))
                     (100 44
                          (:REWRITE |(< (/ x) y) with (< x 0)|))
                     (84 12
                         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
                     (84 12
                         (:REWRITE |(< x (/ y)) with (< 0 y)|))
                     (72 3 (:REWRITE |(* y (* x z))|))
                     (69 69
                         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
                     (48 12
                         (:REWRITE |(<= (/ x) y) with (< x 0)|))
                     (48 12
                         (:REWRITE |(< x (/ y)) with (< y 0)|))
                     (41 41 (:REWRITE |(* c (* d x))|))
                     (21 21
                         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
                     (21 21
                         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
                     (20 20 (:REWRITE |(mod x 2)| . 2))
                     (20 20 (:REWRITE |(equal (* x y) 0)|))
                     (17 17
                         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
                     (12 12 (:REWRITE |(equal (expt 2 n) c)|))
                     (2 2 (:REWRITE ZIP-OPEN))
                     (2 2 (:REWRITE |(* -1 x)|)))
(|(integerp (* 1/2 (logior x y)))|
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (8 8 (:REWRITE |(* (- x) y)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:META META-INTEGERP-CORRECT))
     (3 3
        (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
     (3 3
        (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (3 3
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
     (1 1 (:REWRITE DEFAULT-LOGAND-2))
     (1 1 (:REWRITE DEFAULT-LOGAND-1))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(|(logxor y x)| (88 18 (:REWRITE DEFAULT-LOGAND-2))
                (48 18 (:REWRITE DEFAULT-LOGAND-1))
                (31 31 (:REWRITE LOGAND-CONSTANT-MASK))
                (30 30
                    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
                (16 16
                    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
                (16 16 (:REWRITE REDUCE-INTEGERP-+))
                (16 16 (:REWRITE INTEGERP-MINUS-X))
                (16 16 (:META META-INTEGERP-CORRECT))
                (10 10
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (10 10 (:REWRITE NORMALIZE-ADDENDS))
                (8 8 (:REWRITE DEFAULT-LOGIOR-2))
                (6 6
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                (6 6
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1)))
(LOGXOR-0-X (3 3
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (3 3 (:REWRITE NORMALIZE-ADDENDS))
            (1 1 (:REWRITE REDUCE-INTEGERP-+))
            (1 1 (:REWRITE LOGAND-CONSTANT-MASK))
            (1 1 (:REWRITE INTEGERP-MINUS-X))
            (1 1 (:REWRITE DEFAULT-LOGNOT))
            (1 1 (:META META-INTEGERP-CORRECT)))
(LOGXOR-1-X (21 21
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
            (21 21 (:REWRITE NORMALIZE-ADDENDS))
            (19 19
                (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
            (11 1 (:REWRITE DEFAULT-MOD-RATIO))
            (8 8 (:REWRITE |(* (- x) y)|))
            (5 5 (:REWRITE REDUCE-INTEGERP-+))
            (5 5 (:META META-INTEGERP-CORRECT))
            (4 4
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
            (4 4
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
            (4 4 (:REWRITE DEFAULT-LOGAND-2))
            (4 4 (:REWRITE DEFAULT-LOGAND-1))
            (4 4 (:REWRITE |(equal c (/ x))|))
            (4 4 (:REWRITE |(equal (/ x) c)|))
            (4 4 (:REWRITE |(equal (/ x) (/ y))|))
            (4 4 (:REWRITE |(equal (- x) (- y))|))
            (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
            (3 3 (:REWRITE DEFAULT-LOGNOT))
            (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
            (2 2
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
            (2 2
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
            (2 2
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
            (1 1
               (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
            (1 1 (:REWRITE DEFAULT-MOD-1))
            (1 1 (:REWRITE DEFAULT-LOGIOR-2))
            (1 1 (:REWRITE DEFAULT-LOGIOR-1))
            (1 1 (:REWRITE |(mod x 2)| . 2))
            (1 1 (:REWRITE |(floor x 2)| . 2)))
(LOGXOR--1-X (3 3
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (3 3 (:REWRITE NORMALIZE-ADDENDS))
             (2 2 (:REWRITE LOGAND-CONSTANT-MASK))
             (1 1 (:REWRITE REDUCE-INTEGERP-+))
             (1 1 (:REWRITE INTEGERP-MINUS-X))
             (1 1 (:REWRITE DEFAULT-LOGNOT))
             (1 1 (:META META-INTEGERP-CORRECT)))
(LOGXOR-X-X
     (2994 280
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1880 48 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (1880 48 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (1510 224 (:REWRITE |(< (- x) c)|))
     (1268 314
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1146 348 (:REWRITE THE-FLOOR-ABOVE))
     (784 72 (:REWRITE |(< (+ c/d x) y)|))
     (708 144 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (480 480
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (384 384
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (384 192 (:REWRITE |arith (* y x)|))
     (372 72 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (372 72 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (371 299 (:REWRITE NORMALIZE-ADDENDS))
     (336 330 (:REWRITE DEFAULT-LESS-THAN-2))
     (281 281
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (280 280
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (253 253
          (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (230 230 (:REWRITE |(< (* x y) 0)|))
     (230 224 (:REWRITE |(< (- x) (- y))|))
     (224 224
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (224 224
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (224 224
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (224 224
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (224 224 (:REWRITE |(< c (- x))|))
     (224 224
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (224 224
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (224 224
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (224 224
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (224 224 (:REWRITE |(< (/ x) (/ y))|))
     (190 184
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (184 184 (:REWRITE SIMPLIFY-SUMS-<))
     (184 184
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (184 184 (:REWRITE INTEGERP-<-CONSTANT))
     (184 184 (:REWRITE CONSTANT-<-INTEGERP))
     (153 153 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (143 127 (:REWRITE REDUCE-INTEGERP-+))
     (142 136
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (128 128
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (128 128
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (128 128 (:REWRITE |(< (/ x) 0)|))
     (127 127 (:META META-INTEGERP-CORRECT))
     (126 60
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (118 118 (:REWRITE |(* (- x) y)|))
     (106 102
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (98 48
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (95 95 (:REWRITE |(equal c (/ x))|))
     (95 95 (:REWRITE |(equal (/ x) c)|))
     (95 95 (:REWRITE |(equal (/ x) (/ y))|))
     (95 95 (:REWRITE |(equal (- x) (- y))|))
     (88 88 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (80 80
         (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (60 60 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (60 60
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (57 57 (:REWRITE |(equal (+ (- c) x) y)|))
     (57 35
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (49 49 (:REWRITE |(* a (/ a) b)|))
     (48 48
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (48 48
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (48 48
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (46 46 (:REWRITE LOGAND-CONSTANT-MASK))
     (40 40 (:REWRITE |(floor x 2)| . 2))
     (38 38 (:TYPE-PRESCRIPTION ABS))
     (36 18 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (36 18 (:DEFINITION FIX))
     (30 30
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (28 12
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (28 12
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (24 2
         (:REWRITE |(not (equal (* (/ x) y) -1))|))
     (24 2 (:REWRITE |(equal (* (/ x) y) -1)|))
     (18 18 (:REWRITE |(+ x (- x))|))
     (16 8 (:REWRITE DEFAULT-LOGNOT))
     (14 14 (:REWRITE |arith (* (- x) y)|))
     (10 2 (:REWRITE |(* (* x y) z)|))
     (2 2 (:REWRITE DEFAULT-LOGIOR-2))
     (2 2 (:REWRITE DEFAULT-LOGIOR-1))
     (2 2 (:REWRITE |(equal (* x y) 0)|)))
(|(logxor (floor x 2) (floor y 2))|
     (298 144 (:REWRITE DEFAULT-LOGNOT))
     (212 146 (:REWRITE DEFAULT-LOGIOR-1))
     (208 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (200 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (115 115
          (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (115 115
          (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (115 115
          (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
     (24 24 (:REWRITE |(- (if a b c))|)))
(|(mod (logxor x y) 2)| (78 2 (:LINEAR MOD-BOUNDS-3))
                        (77 5 (:REWRITE DEFAULT-MOD-RATIO))
                        (76 7 (:REWRITE |(* y x)|))
                        (59 59
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                        (47 47 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                        (28 28
                            (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
                        (28 28
                            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
                        (28 28
                            (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
                        (26 26
                            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                        (26 26 (:REWRITE NORMALIZE-ADDENDS))
                        (23 23 (:REWRITE |(* (- x) y)|))
                        (23 5 (:REWRITE DEFAULT-MOD-1))
                        (18 18 (:REWRITE REDUCE-INTEGERP-+))
                        (18 18 (:META META-INTEGERP-CORRECT))
                        (11 11
                            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
                        (11 11
                            (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
                        (6 1 (:REWRITE DEFAULT-LOGAND-2))
                        (6 1 (:REWRITE DEFAULT-LOGAND-1))
                        (5 5 (:REWRITE |(mod x 2)| . 2))
                        (2 2 (:REWRITE LOGAND-CONSTANT-MASK))
                        (2 2 (:REWRITE DEFAULT-LOGNOT))
                        (2 2 (:REWRITE DEFAULT-LOGIOR-2))
                        (2 2 (:REWRITE DEFAULT-LOGIOR-1))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
                        (1 1
                           (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(|(integerp (* 1/2 (logxor x y)))|
     (22 22
         (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (22 22
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (22 22
         (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (19 19
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:META META-INTEGERP-CORRECT))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (8 8
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (6 6 (:REWRITE |(* (- x) y)|))
     (6 1 (:REWRITE DEFAULT-LOGAND-2))
     (6 1 (:REWRITE DEFAULT-LOGAND-1))
     (2 2 (:REWRITE LOGAND-CONSTANT-MASK))
     (2 2 (:REWRITE DEFAULT-LOGNOT))
     (2 2 (:REWRITE DEFAULT-LOGIOR-2))
     (2 2 (:REWRITE DEFAULT-LOGIOR-1))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (1 1
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2)))
(|(equal (lognot x) (lognot y))|
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|)))
(|(equal (lognot x) -1)|
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(|(equal (lognot x) 0)|
     (7 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 2 (:REWRITE ACL2-NUMBERP-X))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(|(lognot (* 2 x))| (21 21
                        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                    (20 20
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                    (20 20 (:REWRITE NORMALIZE-ADDENDS))
                    (7 7 (:REWRITE |(* (- x) y)|))
                    (3 3 (:REWRITE REDUCE-INTEGERP-+))
                    (3 3 (:REWRITE INTEGERP-MINUS-X))
                    (3 3 (:META META-INTEGERP-CORRECT))
                    (1 1 (:REWRITE REDUCE-RATIONALP-+))
                    (1 1 (:REWRITE REDUCE-RATIONALP-*))
                    (1 1 (:REWRITE RATIONALP-MINUS-X))
                    (1 1 (:META META-RATIONALP-CORRECT)))
(|(lognot (floor x 2))|
     (263 263
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (240 6 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (234 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (162 162
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (162 162 (:REWRITE NORMALIZE-ADDENDS))
     (102 102 (:REWRITE |(* (- x) y)|))
     (48 48 (:REWRITE REDUCE-INTEGERP-+))
     (48 48 (:META META-INTEGERP-CORRECT))
     (20 20 (:REWRITE |(floor x 2)| . 2))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (- x) c)|)))
(FLOOR-LOGNOT-HELPER
     (528 18 (:LINEAR MOD-BOUNDS-1))
     (420 420
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (312 41 (:REWRITE REDUCE-INTEGERP-+))
     (257 7 (:REWRITE INTEGERP-/))
     (206 206
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (206 206 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (204 7 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (204 7 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (120 120
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (95 7 (:REWRITE CANCEL-MOD-+))
     (95 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (95 7
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (91 63 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (91 63
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (79 79 (:REWRITE THE-FLOOR-ABOVE))
     (79 79 (:REWRITE DEFAULT-LESS-THAN-2))
     (77 77
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (77 77
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (77 77
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (77 64 (:REWRITE |(equal (/ x) c)|))
     (74 74
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (74 74 (:REWRITE INTEGERP-<-CONSTANT))
     (74 74 (:REWRITE CONSTANT-<-INTEGERP))
     (74 74
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (74 74
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (74 74
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (74 74
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (74 74 (:REWRITE |(< c (- x))|))
     (74 74
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (74 74
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (74 74
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (74 74
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (74 74 (:REWRITE |(< (/ x) (/ y))|))
     (74 74 (:REWRITE |(< (- x) c)|))
     (74 74 (:REWRITE |(< (- x) (- y))|))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (64 64 (:REWRITE |(equal c (/ x))|))
     (64 64 (:REWRITE |(equal (/ x) (/ y))|))
     (64 64 (:REWRITE |(equal (- x) (- y))|))
     (63 63 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (63 63
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (63 63 (:REWRITE |(equal (- x) c)|))
     (63 9 (:LINEAR MOD-BOUNDS-3))
     (58 58 (:REWRITE |(* c (* d x))|))
     (58 42
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (58 42
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
     (54 54
         (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (51 51 (:REWRITE FOLD-CONSTS-IN-+))
     (42 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (41 41
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (41 41 (:REWRITE INTEGERP-MINUS-X))
     (41 41 (:META META-INTEGERP-CORRECT))
     (39 39 (:REWRITE |(< 0 (* x y))|))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (36 36
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (36 36 (:REWRITE |(< 0 (/ x))|))
     (33 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (28 7 (:REWRITE DEFAULT-MOD-RATIO))
     (27 27 (:REWRITE |(< y (+ (- c) x))|))
     (27 27 (:REWRITE |(< x (+ c/d y))|))
     (19 19 (:REWRITE |(< (+ c/d x) y)|))
     (19 19 (:REWRITE |(< (+ (- c) x) y)|))
     (18 18 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (7 7
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (7 7
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (7 7 (:REWRITE MOD-CANCEL-*-CONST))
     (7 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (7 7 (:REWRITE DEFAULT-MOD-1))
     (7 7 (:REWRITE |(mod x (- y))| . 3))
     (7 7 (:REWRITE |(mod x (- y))| . 2))
     (7 7 (:REWRITE |(mod x (- y))| . 1))
     (7 7
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (7 7
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (7 7 (:REWRITE |(mod (- x) y)| . 3))
     (7 7 (:REWRITE |(mod (- x) y)| . 2))
     (7 7 (:REWRITE |(mod (- x) y)| . 1))
     (7 7
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (7 7
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(* x (- y))|))
     (4 4 (:REWRITE |(* (- x) y)|))
     (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(/ (/ x))|)))
(FLOOR-LOGNOT
     (30028 420 (:REWRITE |(integerp (expt x n))|))
     (25564 3023
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (16654 358 (:REWRITE FLOOR-=-X/Y . 2))
     (12463 2324 (:REWRITE |(< (- x) c)|))
     (12243 201 (:REWRITE CANCEL-MOD-+))
     (9240 358 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (7656 72 (:REWRITE |(mod (+ 1 x) y)|))
     (7473 185 (:REWRITE |(integerp (- x))|))
     (5464 1928
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5028 250 (:REWRITE ODD-EXPT-THM))
     (4875 201 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (4021 756 (:REWRITE REDUCE-INTEGERP-+))
     (3757 3023 (:REWRITE DEFAULT-LESS-THAN-2))
     (3059 3023
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3059 3023
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3023 3023 (:REWRITE THE-FLOOR-ABOVE))
     (2934 65 (:LINEAR MOD-BOUNDS-3))
     (2805 114 (:LINEAR EXPT-X->=-X))
     (2805 114 (:LINEAR EXPT-X->-X))
     (2628 358 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (2628 358 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (2592 2592
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2436 225 (:REWRITE DEFAULT-MOD-RATIO))
     (2434 1842
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2366 2324
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2334 1928
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2328 2324 (:REWRITE |(< (- x) (- y))|))
     (2324 2324
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2324 2324
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2324 2324
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2324 2324 (:REWRITE |(< c (- x))|))
     (2324 2324
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2324 2324
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2324 2324
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2324 2324
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2324 2324 (:REWRITE |(< (/ x) (/ y))|))
     (2308 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (2280 1846 (:REWRITE SIMPLIFY-SUMS-<))
     (2234 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (2050 2050 (:REWRITE |(expt 1/c n)|))
     (2050 2050 (:REWRITE |(expt (- x) n)|))
     (2016 72 (:REWRITE |(* (* x y) z)|))
     (1928 1928 (:REWRITE INTEGERP-<-CONSTANT))
     (1928 1928 (:REWRITE CONSTANT-<-INTEGERP))
     (1805 201
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (1805 201
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (1584 358 (:REWRITE FLOOR-CANCEL-*-CONST))
     (1416 756 (:META META-INTEGERP-CORRECT))
     (1336 201 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1258 272
           (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (1141 1141
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1019 1019 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1019 1019
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (1019 1019
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (992 992
          (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
     (871 201
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (871 201 (:REWRITE MOD-CANCEL-*-CONST))
     (871 201
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (847 847 (:REWRITE |(< (* x y) 0)|))
     (834 272
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (583 201
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (582 190
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (562 562 (:REWRITE |(< (/ x) 0)|))
     (508 192
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (437 437 (:REWRITE |(< (+ c/d x) y)|))
     (414 414 (:REWRITE |(< x (+ c/d y))|))
     (413 413 (:REWRITE |(< 0 (* x y))|))
     (348 284 (:REWRITE |(- (* c x))|))
     (343 343
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (343 343
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (298 298
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (298 298 (:REWRITE |(floor x (- y))| . 2))
     (298 298 (:REWRITE |(floor x (- y))| . 1))
     (298 298 (:REWRITE |(floor (- x) y)| . 2))
     (274 274
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (272 272
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (272 272
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (268 268 (:REWRITE |(equal (/ x) (/ y))|))
     (229 225 (:REWRITE DEFAULT-MOD-1))
     (228 228
          (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (228 228
          (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (228 228
          (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (201 201
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (201 201 (:REWRITE |(mod x (- y))| . 3))
     (201 201 (:REWRITE |(mod x (- y))| . 2))
     (201 201 (:REWRITE |(mod x (- y))| . 1))
     (201 201
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (201 201 (:REWRITE |(mod (- x) y)| . 3))
     (201 201 (:REWRITE |(mod (- x) y)| . 2))
     (201 201 (:REWRITE |(mod (- x) y)| . 1))
     (201 201
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (192 192
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (192 192 (:REWRITE |(equal c (/ x))|))
     (192 192 (:REWRITE |(equal (/ x) c)|))
     (192 192 (:REWRITE |(equal (- x) c)|))
     (186 186
          (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
     (180 180 (:REWRITE |(equal (+ (- c) x) y)|))
     (152 152 (:REWRITE |(< (+ (- c) x) y)|))
     (140 140
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (134 86
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
     (134 86
          (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
     (133 133
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (133 133
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (133 133 (:REWRITE |(< 0 (/ x))|))
     (117 117 (:REWRITE |(* c (* d x))|))
     (114 114 (:LINEAR EXPT-LINEAR-UPPER-<))
     (114 114 (:LINEAR EXPT-LINEAR-LOWER-<))
     (114 114 (:LINEAR EXPT->=-1-TWO))
     (114 114 (:LINEAR EXPT->-1-TWO))
     (114 114 (:LINEAR EXPT-<=-1-ONE))
     (114 114 (:LINEAR EXPT-<-1-ONE))
     (86 86
         (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
     (77 77 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (72 72 (:TYPE-PRESCRIPTION ABS))
     (70 14 (:REWRITE FLOOR-=-X/Y . 4))
     (70 14
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (59 59 (:REWRITE FOLD-CONSTS-IN-+))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (42 42 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
     (38 38 (:REWRITE |(* 1/2 (floor x y))| . 3))
     (38 38 (:REWRITE |(* 1/2 (floor x y))| . 2))
     (36 36
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (24 24 (:REWRITE |(* 0 x)|))
     (16 16
         (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
     (16 16
         (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
     (10 10 (:REWRITE |(equal (expt 2 n) c)|))
     (8 8 (:REWRITE |(floor x 2)| . 2))
     (6 2
        (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
     (6 2
        (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL)))
(|(mod (lognot x) 2)| (78 2 (:LINEAR MOD-BOUNDS-3))
                      (76 7 (:REWRITE |(* y x)|))
                      (63 5 (:REWRITE DEFAULT-MOD-RATIO))
                      (44 44
                          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                      (37 37 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                      (20 20
                          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                      (20 20 (:REWRITE NORMALIZE-ADDENDS))
                      (19 19 (:REWRITE |(* (- x) y)|))
                      (11 11 (:REWRITE REDUCE-INTEGERP-+))
                      (11 11 (:META META-INTEGERP-CORRECT))
                      (9 5 (:REWRITE DEFAULT-MOD-1))
                      (5 5 (:REWRITE |(mod x 2)| . 2)))
(|(integerp (* 1/2 (lognot x)))|
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(* (- x) y)|)))
(LOGNOT-LOGAND (8 8
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (8 8 (:REWRITE NORMALIZE-ADDENDS))
               (3 3
                  (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
               (3 3
                  (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
               (3 3
                  (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
               (2 2
                  (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
               (2 2
                  (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
               (2 2
                  (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
               (2 2 (:REWRITE REDUCE-INTEGERP-+))
               (2 2 (:REWRITE LOGAND-CONSTANT-MASK))
               (2 2 (:REWRITE INTEGERP-MINUS-X))
               (2 2 (:REWRITE DEFAULT-LOGAND-2))
               (2 2 (:REWRITE DEFAULT-LOGAND-1))
               (2 2 (:META META-INTEGERP-CORRECT)))
(LOGNOT-LOGIOR (25 25
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
               (25 25
                   (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
               (7 7
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (7 7 (:REWRITE NORMALIZE-ADDENDS))
               (2 2 (:REWRITE REDUCE-INTEGERP-+))
               (2 2 (:REWRITE LOGAND-CONSTANT-MASK))
               (2 2 (:REWRITE INTEGERP-MINUS-X))
               (2 2 (:REWRITE DEFAULT-LOGAND-2))
               (2 2 (:REWRITE DEFAULT-LOGAND-1))
               (2 2 (:META META-INTEGERP-CORRECT)))
(LOGNOT-LOGNOT (3 3
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (3 3 (:REWRITE NORMALIZE-ADDENDS))
               (1 1 (:REWRITE REDUCE-INTEGERP-+))
               (1 1 (:REWRITE INTEGERP-MINUS-X))
               (1 1 (:META META-INTEGERP-CORRECT)))
