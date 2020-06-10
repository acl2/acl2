(RTL::MU (85 17 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
         (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
         (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
         (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
         (34 17 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
         (17 17
             (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
         (17 17 (:TYPE-PRESCRIPTION RATIONALP-MOD))
         (17 17 (:TYPE-PRESCRIPTION NATP))
         (17 17 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
         (17 17 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
         (17 17 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
         (17 17
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
         (17 17
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
         (17 17 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
         (17 17 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
         (17 17
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
         (17 17
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
         (17 17 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
         (17 17 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
         (17 17
             (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD)))
(RTL::REFLECTIONS (90 18 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                  (36 18 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                  (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (18 18
                      (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
                  (18 18 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                  (18 18 (:TYPE-PRESCRIPTION NATP))
                  (18 18 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                  (18 18 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (18 18 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                  (18 18
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                  (18 18
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (18 18 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (18 18 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                  (18 18
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                  (18 18
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (18 18 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                  (18 18 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
                  (18 18
                      (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD)))
(RTL::LEN-REFLECTIONS
     (6776 793 (:REWRITE RATIONALP-X))
     (4145 665 (:META META-RATIONALP-CORRECT))
     (3101 76 (:REWRITE RTL::MOD-DOES-NOTHING))
     (2857 1097 (:REWRITE DEFAULT-TIMES-2))
     (1692 1692
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1692 1692
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1692 1692
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1588 204 (:REWRITE ACL2-NUMBERP-X))
     (1331 931 (:META META-INTEGERP-CORRECT))
     (1306 14 (:REWRITE MOD-X-Y-=-X . 4))
     (1298 14 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1298 14 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1238 14 (:REWRITE MOD-ZERO . 4))
     (1234 14
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (931 931 (:REWRITE REDUCE-INTEGERP-+))
     (931 931 (:REWRITE INTEGERP-MINUS-X))
     (864 96 (:REWRITE RATIONALP-/))
     (840 168 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (697 697 (:REWRITE RATIONALP-MINUS-X))
     (690 14 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (678 14
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (678 14
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (678 14
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (665 665 (:REWRITE REDUCE-RATIONALP-+))
     (640 80 (:REWRITE INTP-3))
     (638 14 (:REWRITE MOD-CANCEL-*-CONST))
     (614 614
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (614 614
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (614 614
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (614 614
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (608 168 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (600 4 (:LINEAR MOD-BOUNDS-2))
     (600 4 (:LINEAR MOD-BOUNDS-1))
     (592 8 (:REWRITE |(* x (if a b c))|))
     (584 584
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (568 14 (:REWRITE MOD-ZERO . 3))
     (480 40 (:REWRITE INTP-1))
     (441 241 (:REWRITE DEFAULT-LESS-THAN-1))
     (429 163
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (429 163
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (397 163 (:REWRITE SIMPLIFY-SUMS-<))
     (396 244 (:REWRITE DEFAULT-DIVIDE))
     (386 25 (:REWRITE DEFAULT-MINUS))
     (354 10 (:REWRITE |(+ x (if a b c))|))
     (336 168 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (310 310
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (310 310
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (310 310
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (310 310
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (280 280 (:TYPE-PRESCRIPTION INTP-*))
     (266 14 (:REWRITE MOD-X-Y-=-X . 3))
     (258 14 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (258 14 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (257 257 (:REWRITE THE-FLOOR-BELOW))
     (257 257 (:REWRITE THE-FLOOR-ABOVE))
     (240 240 (:TYPE-PRESCRIPTION FIX))
     (236 236
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (236 236 (:REWRITE |(* c (* d x))|))
     (194 14 (:REWRITE MOD-X-Y-=-X . 2))
     (192 174 (:REWRITE CONSTANT-<-INTEGERP))
     (176 176 (:REWRITE INTEGERP-/))
     (174 174
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (174 174
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (174 174
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (174 174
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (174 174 (:REWRITE INTEGERP-<-CONSTANT))
     (174 174
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (174 174
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (174 174
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (174 174
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (174 174 (:REWRITE |(< c (- x))|))
     (174 174
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (174 174
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (174 174
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (174 174
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (174 174 (:REWRITE |(< (/ x) (/ y))|))
     (174 174 (:REWRITE |(< (- x) c)|))
     (174 174 (:REWRITE |(< (- x) (- y))|))
     (170 14 (:REWRITE CANCEL-MOD-+))
     (168 168
          (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (168 168 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (168 168 (:TYPE-PRESCRIPTION NATP))
     (168 168 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (168 168 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (168 168
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (168 168
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (168 168
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (168 168
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (168 168
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (168 168
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (168 168 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (168 168 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (168 168
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (118 105 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (118 105
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (118 105
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (116 116
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (116 116
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (105 105
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (105 105 (:REWRITE |(equal c (/ x))|))
     (105 105 (:REWRITE |(equal c (- x))|))
     (105 105 (:REWRITE |(equal (/ x) c)|))
     (105 105 (:REWRITE |(equal (/ x) (/ y))|))
     (105 105 (:REWRITE |(equal (- x) c)|))
     (105 105 (:REWRITE |(equal (- x) (- y))|))
     (92 92
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (83 83
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (83 83 (:REWRITE NORMALIZE-ADDENDS))
     (80 80 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
     (64 2 (:LINEAR RTL::MOD-BND-2))
     (54 6
         (:REWRITE |(<= x (/ y)) with (< y 0)|))
     (54 6
         (:REWRITE |(<= x (/ y)) with (< 0 y)|))
     (54 6 (:REWRITE |(< (/ x) y) with (< x 0)|))
     (54 6 (:REWRITE |(< (/ x) y) with (< 0 x)|))
     (50 50 (:REWRITE |(< (/ x) 0)|))
     (50 50 (:REWRITE |(< (* x y) 0)|))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (48 48 (:REWRITE DEFAULT-MOD-1))
     (48 48 (:REWRITE |(< 0 (/ x))|))
     (48 48 (:REWRITE |(< 0 (* x y))|))
     (39 39
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (39 39
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (35 24 (:REWRITE DEFAULT-CDR))
     (28 28 (:REWRITE |(< (+ c/d x) y)|))
     (28 28 (:REWRITE |(< (+ (- c) x) y)|))
     (20 2 (:LINEAR MOD-BOUNDS-3))
     (19 19
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (16 16 (:REWRITE |(not (equal x (/ y)))|))
     (16 16 (:REWRITE |(equal x (/ y))|))
     (14 14
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (14 14 (:REWRITE |(mod x (- y))| . 3))
     (14 14 (:REWRITE |(mod x (- y))| . 2))
     (14 14 (:REWRITE |(mod x (- y))| . 1))
     (14 14
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (14 14 (:REWRITE |(mod (- x) y)| . 3))
     (14 14 (:REWRITE |(mod (- x) y)| . 2))
     (14 14 (:REWRITE |(mod (- x) y)| . 1))
     (14 14
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (9 9 (:REWRITE |(- (* c x))|))
     (4 4 (:REWRITE ZP-OPEN))
     (4 4 (:REWRITE |(equal (* x y) 0)|))
     (4 4
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::MOD-DISTINCT-REFLECT
     (11205 2241 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (10255 10255
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (10255 10255
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (10255 10255
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (9944 118 (:REWRITE CANCEL-MOD-+))
     (8837 2241 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (7749 2241
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (7749 2241
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (4780 122 (:REWRITE |(integerp (- x))|))
     (4426 124 (:REWRITE DEFAULT-MOD-RATIO))
     (3944 312 (:REWRITE |(* (* x y) z)|))
     (3812 118 (:REWRITE MOD-ZERO . 3))
     (3258 1450 (:REWRITE DEFAULT-TIMES-2))
     (3110 122 (:REWRITE |(* (- x) y)|))
     (2917 185 (:REWRITE DEFAULT-PLUS-2))
     (2916 118 (:REWRITE MOD-X-Y-=-X . 4))
     (2916 118 (:REWRITE MOD-X-Y-=-X . 3))
     (2838 118 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2305 2241 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (2303 185 (:REWRITE DEFAULT-PLUS-1))
     (2241 2241 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2241 2241
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2241 2241
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2241 2241
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2112 1056 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (1844 292 (:META META-INTEGERP-CORRECT))
     (1658 1450 (:REWRITE DEFAULT-TIMES-1))
     (1586 118 (:REWRITE MOD-ZERO . 4))
     (1384 184 (:REWRITE INTEGERP-/))
     (1108 132 (:REWRITE DEFAULT-MINUS))
     (1056 1056 (:TYPE-PRESCRIPTION NATP))
     (1056 1056
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (1056 1056
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (1056 1056
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (916 916
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (916 916
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (916 916
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (916 916
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (828 124 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (822 822
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (734 734 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (699 413
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (675 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (647 411 (:REWRITE SIMPLIFY-SUMS-<))
     (647 411
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (623 415 (:REWRITE DEFAULT-LESS-THAN-1))
     (618 202
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (590 118 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (590 118 (:REWRITE MOD-X-Y-=-X . 2))
     (590 118
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (590 118
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (526 118
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (502 118
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (502 118
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (480 36 (:REWRITE |(* y (* x z))|))
     (443 415 (:REWRITE DEFAULT-LESS-THAN-2))
     (415 415 (:REWRITE THE-FLOOR-BELOW))
     (415 415 (:REWRITE THE-FLOOR-ABOVE))
     (415 415
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (415 415
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (415 415
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (413 413
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (413 413 (:REWRITE INTEGERP-<-CONSTANT))
     (413 413 (:REWRITE CONSTANT-<-INTEGERP))
     (413 413
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (413 413
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (413 413
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (413 413
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (413 413 (:REWRITE |(< c (- x))|))
     (413 413
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (413 413
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (413 413
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (413 413
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (413 413 (:REWRITE |(< (/ x) (/ y))|))
     (413 413 (:REWRITE |(< (- x) c)|))
     (413 413 (:REWRITE |(< (- x) (- y))|))
     (366 118 (:REWRITE MOD-CANCEL-*-CONST))
     (332 124 (:REWRITE DEFAULT-MOD-1))
     (328 328 (:REWRITE |(* c (* d x))|))
     (326 326
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (326 326 (:REWRITE DEFAULT-DIVIDE))
     (292 292 (:REWRITE REDUCE-INTEGERP-+))
     (292 292 (:REWRITE INTEGERP-MINUS-X))
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (259 259
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (255 255 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (202 202
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (202 202
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (202 202
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (202 202 (:REWRITE |(equal c (/ x))|))
     (202 202 (:REWRITE |(equal c (- x))|))
     (202 202 (:REWRITE |(equal (/ x) c)|))
     (202 202 (:REWRITE |(equal (/ x) (/ y))|))
     (202 202 (:REWRITE |(equal (- x) c)|))
     (202 202 (:REWRITE |(equal (- x) (- y))|))
     (194 194 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (182 118
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (182 118
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (182 118
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (158 158
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (158 158
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (158 158 (:REWRITE |(< (/ x) 0)|))
     (158 158 (:REWRITE |(< (* x y) 0)|))
     (150 150
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (124 124 (:REWRITE DEFAULT-MOD-2))
     (122 122 (:REWRITE |(- (* c x))|))
     (121 121
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (120 6 (:LINEAR MOD-BOUNDS-3))
     (118 118 (:REWRITE |(mod x (- y))| . 3))
     (118 118 (:REWRITE |(mod x (- y))| . 2))
     (118 118 (:REWRITE |(mod x (- y))| . 1))
     (118 118 (:REWRITE |(mod (- x) y)| . 3))
     (118 118 (:REWRITE |(mod (- x) y)| . 2))
     (118 118 (:REWRITE |(mod (- x) y)| . 1))
     (82 82
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (82 82 (:REWRITE |(< 0 (* x y))|))
     (80 80
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (80 80
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (80 80 (:REWRITE |(< 0 (/ x))|))
     (74 74 (:REWRITE |(equal (* x y) 0)|))
     (74 74
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (72 10 (:LINEAR RTL::MOD-BND-2))
     (60 12 (:LINEAR MOD-BOUNDS-2))
     (22 22 (:REWRITE |(equal (+ (- c) x) y)|))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (21 21 (:REWRITE |(< (+ (- c) x) y)|))
     (16 16 (:REWRITE |(+ c (+ d x))|))
     (12 12 (:REWRITE ZP-OPEN))
     (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10 (:LINEAR RTL::MOD-BND-3))
     (8 8 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(* a (/ a))|))
     (5 5 (:REWRITE |(< y (+ (- c) x))|))
     (5 5 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (4 4
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2
        (:REWRITE |(< x (/ y)) with (< 0 y)|)))
(RTL::REFLECTIONS-DISTINCT-POSITIVES-LEMMA-1
     (2392 29 (:REWRITE CANCEL-MOD-+))
     (1680 336 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1654 1654
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1654 1654
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1654 1654
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1265 6 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1233 87 (:REWRITE |(* (* x y) z)|))
     (1223 29 (:REWRITE MOD-ZERO . 3))
     (1192 336 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1181 6 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1176 336
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1176 336
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1111 29 (:REWRITE |(integerp (- x))|))
     (974 29 (:REWRITE MOD-X-Y-=-X . 4))
     (974 29 (:REWRITE MOD-X-Y-=-X . 3))
     (947 29 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (839 29 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (788 29 (:REWRITE DEFAULT-MOD-RATIO))
     (788 29 (:REWRITE |(* (- x) y)|))
     (761 85 (:REWRITE DEFAULT-PLUS-2))
     (757 409 (:REWRITE DEFAULT-TIMES-2))
     (704 29 (:REWRITE RTL::MOD-DOES-NOTHING))
     (677 677
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (677 677
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (677 677
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (677 677
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (517 74 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (515 29 (:REWRITE MOD-ZERO . 4))
     (456 94 (:META META-INTEGERP-CORRECT))
     (456 85 (:REWRITE DEFAULT-PLUS-1))
     (409 409 (:REWRITE DEFAULT-TIMES-1))
     (375 39 (:REWRITE DEFAULT-MINUS))
     (362 156 (:REWRITE SIMPLIFY-SUMS-<))
     (362 156
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (362 156
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (362 156 (:REWRITE DEFAULT-LESS-THAN-2))
     (336 336 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (336 336 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (336 336
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (336 336
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (331 78
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (320 44 (:REWRITE INTEGERP-/))
     (252 126 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (220 220
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (176 156
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (168 168
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (168 168
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (168 168
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (168 168
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (156 156 (:REWRITE THE-FLOOR-BELOW))
     (156 156 (:REWRITE THE-FLOOR-ABOVE))
     (156 156
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (156 156
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (156 156
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (156 156 (:REWRITE INTEGERP-<-CONSTANT))
     (156 156 (:REWRITE DEFAULT-LESS-THAN-1))
     (156 156 (:REWRITE CONSTANT-<-INTEGERP))
     (156 156
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (156 156
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (156 156
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (156 156
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (156 156 (:REWRITE |(< c (- x))|))
     (156 156
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (156 156
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (156 156
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (156 156
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (156 156 (:REWRITE |(< (/ x) (/ y))|))
     (156 156 (:REWRITE |(< (- x) c)|))
     (156 156 (:REWRITE |(< (- x) (- y))|))
     (145 29 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (145 29 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (145 29 (:REWRITE MOD-X-Y-=-X . 2))
     (145 29
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (145 29
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (145 29 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (145 29
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (145 29
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (126 126 (:TYPE-PRESCRIPTION NATP))
     (126 126
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (126 126 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (126 126 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (126 126
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (113 29 (:REWRITE MOD-CANCEL-*-CONST))
     (106 106 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (102 102 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (97 3 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (94 94 (:REWRITE REDUCE-INTEGERP-+))
     (94 94 (:REWRITE INTEGERP-MINUS-X))
     (87 87
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (87 87 (:REWRITE DEFAULT-DIVIDE))
     (87 87 (:REWRITE |(* c (* d x))|))
     (86 2 (:LINEAR MOD-BOUNDS-3))
     (85 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (78 78
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (78 78
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (78 78
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (78 78 (:REWRITE |(equal c (/ x))|))
     (78 78 (:REWRITE |(equal c (- x))|))
     (78 78 (:REWRITE |(equal (/ x) c)|))
     (78 78 (:REWRITE |(equal (/ x) (/ y))|))
     (78 78 (:REWRITE |(equal (- x) c)|))
     (78 78 (:REWRITE |(equal (- x) (- y))|))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (64 2 (:LINEAR RTL::MOD-BND-2))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (56 56 (:REWRITE |(< (/ x) 0)|))
     (56 56
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (56 56 (:REWRITE |(< (* x y) 0)|))
     (55 15 (:REWRITE ACL2-NUMBERP-X))
     (42 42
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (29 29
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (29 29 (:REWRITE DEFAULT-MOD-2))
     (29 29 (:REWRITE DEFAULT-MOD-1))
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
     (29 29 (:REWRITE |(- (* c x))|))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (27 27 (:REWRITE |(equal (* x y) 0)|))
     (27 27 (:REWRITE |(< 0 (/ x))|))
     (27 27
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (27 27 (:REWRITE |(< 0 (* x y))|))
     (20 5 (:REWRITE RATIONALP-X))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (17 17 (:REWRITE |(equal (+ (- c) x) y)|))
     (15 15 (:REWRITE RTL::PERM-MEMBER))
     (12 12 (:REWRITE ZP-OPEN))
     (9 7 (:REWRITE DEFAULT-CDR))
     (9 7 (:REWRITE DEFAULT-CAR))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (6 6
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE |(+ c (+ d x))|))
     (5 5 (:META META-RATIONALP-CORRECT))
     (4 1 (:REWRITE |(+ x x)|))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::REFLECTIONS-DISTINCT-POSITIVES-LEMMA-2
     (15423 7 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (12445 7 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (7147 92 (:REWRITE CANCEL-MOD-+))
     (5337 5337
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5337 5337
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5337 5337
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4420 884 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (3961 92 (:REWRITE MOD-ZERO . 3))
     (3792 297 (:REWRITE |(* (* x y) z)|))
     (3488 884 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (3400 884
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (3400 884
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (3208 92 (:REWRITE |(integerp (- x))|))
     (3207 92 (:REWRITE MOD-X-Y-=-X . 4))
     (3207 92 (:REWRITE MOD-X-Y-=-X . 3))
     (3118 92 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (2762 92 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (2545 155 (:REWRITE DEFAULT-PLUS-2))
     (2375 92 (:REWRITE DEFAULT-MOD-RATIO))
     (2375 92 (:REWRITE |(* (- x) y)|))
     (2327 1139 (:REWRITE DEFAULT-TIMES-2))
     (2317 92 (:REWRITE RTL::MOD-DOES-NOTHING))
     (1694 92 (:REWRITE MOD-ZERO . 4))
     (1281 113 (:REWRITE DEFAULT-MINUS))
     (1257 376 (:META META-INTEGERP-CORRECT))
     (1183 158
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1139 1139 (:REWRITE DEFAULT-TIMES-1))
     (1106 155 (:REWRITE DEFAULT-PLUS-1))
     (915 915
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (915 915
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (915 915
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (915 915
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (884 884 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (884 884 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (884 884
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (884 884
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (884 884
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (878 20 (:LINEAR MOD-BOUNDS-3))
     (786 494 (:REWRITE DEFAULT-LESS-THAN-2))
     (784 492 (:REWRITE SIMPLIFY-SUMS-<))
     (784 492
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (657 657
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (640 20 (:LINEAR RTL::MOD-BND-2))
     (581 581
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (581 581
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (581 581
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (581 581
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (571 187 (:REWRITE INTEGERP-/))
     (521 493
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (510 255 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (494 494 (:REWRITE THE-FLOOR-BELOW))
     (494 494 (:REWRITE THE-FLOOR-ABOVE))
     (494 494
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (494 494
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (494 494
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (494 494 (:REWRITE DEFAULT-LESS-THAN-1))
     (493 493 (:REWRITE INTEGERP-<-CONSTANT))
     (493 493 (:REWRITE CONSTANT-<-INTEGERP))
     (493 493
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (493 493
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (493 493
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (493 493
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (493 493 (:REWRITE |(< c (- x))|))
     (493 493
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (493 493
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (493 493
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (493 493
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (493 493 (:REWRITE |(< (/ x) (/ y))|))
     (493 493 (:REWRITE |(< (- x) c)|))
     (493 493 (:REWRITE |(< (- x) (- y))|))
     (460 92 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (460 92 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (460 92 (:REWRITE MOD-X-Y-=-X . 2))
     (460 92 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (460 92
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (424 92 (:REWRITE MOD-CANCEL-*-CONST))
     (418 158 (:REWRITE |(equal (- x) (- y))|))
     (392 376 (:REWRITE INTEGERP-MINUS-X))
     (376 376 (:REWRITE REDUCE-INTEGERP-+))
     (315 315 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (308 92
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (308 92
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (308 92
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (297 297
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (297 297 (:REWRITE DEFAULT-DIVIDE))
     (297 297 (:REWRITE |(* c (* d x))|))
     (255 255 (:TYPE-PRESCRIPTION NATP))
     (255 255
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (255 255 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (255 255 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (255 255
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (255 2
          (:REWRITE |(equal (mod a n) (mod b n))|))
     (244 92
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (244 92
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (244 92
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (210 210 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (207 207
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (207 207
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (207 207
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (207 207
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (200 40 (:LINEAR MOD-BOUNDS-2))
     (199 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (198 198
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (198 198
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (198 198 (:REWRITE |(< (/ x) 0)|))
     (198 198
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (198 198 (:REWRITE |(< (* x y) 0)|))
     (158 158
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (158 158
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (158 158
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (158 158 (:REWRITE |(equal c (/ x))|))
     (158 158 (:REWRITE |(equal c (- x))|))
     (158 158 (:REWRITE |(equal (/ x) c)|))
     (158 158 (:REWRITE |(equal (/ x) (/ y))|))
     (158 158 (:REWRITE |(equal (- x) c)|))
     (94 94 (:REWRITE |(- (* c x))|))
     (92 92 (:REWRITE DEFAULT-MOD-2))
     (92 92 (:REWRITE DEFAULT-MOD-1))
     (92 92 (:REWRITE |(mod x (- y))| . 3))
     (92 92 (:REWRITE |(mod x (- y))| . 2))
     (92 92 (:REWRITE |(mod x (- y))| . 1))
     (92 92 (:REWRITE |(mod (- x) y)| . 3))
     (92 92 (:REWRITE |(mod (- x) y)| . 2))
     (92 92 (:REWRITE |(mod (- x) y)| . 1))
     (90 90
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (90 90 (:REWRITE |(< 0 (* x y))|))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (89 89
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (89 89 (:REWRITE |(equal (* x y) 0)|))
     (89 89 (:REWRITE |(< 0 (/ x))|))
     (89 89
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (77 21 (:REWRITE ACL2-NUMBERP-X))
     (70 70
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 7 (:REWRITE RATIONALP-X))
     (26 26 (:REWRITE |(equal (+ (- c) x) y)|))
     (21 21 (:REWRITE RTL::PERM-MEMBER))
     (20 20 (:LINEAR RTL::MOD-BND-3))
     (15 15 (:REWRITE ZP-OPEN))
     (13 13 (:REWRITE |(+ c (+ d x))|))
     (13 10 (:REWRITE DEFAULT-CDR))
     (13 10 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE |(< (+ c/d x) y)|))
     (10 10 (:REWRITE |(< (+ (- c) x) y)|))
     (7 7 (:REWRITE REDUCE-RATIONALP-+))
     (7 7 (:REWRITE REDUCE-RATIONALP-*))
     (7 7 (:REWRITE RATIONALP-MINUS-X))
     (7 7
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (7 7 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 1 (:REWRITE |(+ x x)|))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::P-1-EVEN-COR
     (107 107
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (107 107
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (107 107
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (29 21 (:REWRITE DEFAULT-TIMES-2))
     (21 21 (:REWRITE DEFAULT-TIMES-1))
     (20 12 (:REWRITE DEFAULT-PLUS-2))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
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
     (4 4 (:META META-INTEGERP-CORRECT))
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
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(RTL::REFLECTIONS-DISTINCT-POSITIVES
     (3155 631 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2831 2831
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (2831 2831
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2223 631 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2167 631
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2167 631
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2131 44 (:REWRITE |(< (+ c/d x) y)|))
     (2105 30 (:REWRITE CANCEL-MOD-+))
     (1448 246 (:REWRITE DEFAULT-PLUS-2))
     (1107 495 (:REWRITE DEFAULT-TIMES-2))
     (1028 30 (:REWRITE MOD-ZERO . 3))
     (940 30 (:REWRITE MOD-X-Y-=-X . 4))
     (940 30 (:REWRITE MOD-X-Y-=-X . 3))
     (925 25 (:REWRITE |(integerp (- x))|))
     (924 226
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (914 30 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (857 246 (:REWRITE DEFAULT-PLUS-1))
     (810 30 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (790 260 (:REWRITE DEFAULT-LESS-THAN-2))
     (720 38 (:REWRITE |(< x (+ c/d y))|))
     (712 32 (:REWRITE |(* (- x) y)|))
     (710 30 (:REWRITE DEFAULT-MOD-RATIO))
     (680 30 (:REWRITE RTL::MOD-DOES-NOTHING))
     (679 679
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (679 679
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (679 679
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (679 679
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (656 238
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (631 631 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (631 631 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (631 631
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (631 631
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (631 631
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (582 45 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (562 260 (:REWRITE DEFAULT-LESS-THAN-1))
     (498 30 (:REWRITE MOD-ZERO . 4))
     (495 495 (:REWRITE DEFAULT-TIMES-1))
     (494 247 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (459 39 (:REWRITE DEFAULT-MINUS))
     (439 157 (:META META-INTEGERP-CORRECT))
     (305 227 (:REWRITE |(< c (- x))|))
     (288 288
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (263 263 (:REWRITE THE-FLOOR-BELOW))
     (263 263 (:REWRITE THE-FLOOR-ABOVE))
     (250 34 (:REWRITE INTEGERP-/))
     (247 247
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (247 247 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (247 247 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (247 247
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (246 226
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (238 238
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (238 238
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (232 232
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (232 232
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (232 232
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (232 232
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (227 227
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (227 227
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (227 227
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (227 227
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (227 227
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (227 227
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (227 227
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (227 227
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (227 227 (:REWRITE |(< (/ x) (/ y))|))
     (227 227 (:REWRITE |(< (- x) (- y))|))
     (226 226 (:REWRITE INTEGERP-<-CONSTANT))
     (226 226 (:REWRITE CONSTANT-<-INTEGERP))
     (205 205 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (190 64
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (165 165 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (157 157 (:REWRITE REDUCE-INTEGERP-+))
     (157 157 (:REWRITE INTEGERP-MINUS-X))
     (154 42 (:REWRITE ACL2-NUMBERP-X))
     (150 30 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (150 30 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (150 30 (:REWRITE MOD-X-Y-=-X . 2))
     (150 30 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (150 30
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (142 142
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (142 30
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (142 30
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (142 30
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (139 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (106 30 (:REWRITE MOD-CANCEL-*-CONST))
     (96 3 (:LINEAR RTL::MOD-BND-2))
     (91 91
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (91 91 (:REWRITE DEFAULT-DIVIDE))
     (91 91 (:REWRITE |(* c (* d x))|))
     (90 10
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (88 1 (:REWRITE |(* x (- y))|))
     (84 84 (:REWRITE |(< 0 (* x y))|))
     (80 68 (:REWRITE DEFAULT-CAR))
     (80 2 (:LINEAR MOD-BOUNDS-3))
     (78 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (78 64
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (67 67 (:REWRITE |(* a (/ a) b)|))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (64 64 (:REWRITE |(equal c (/ x))|))
     (64 64 (:REWRITE |(equal c (- x))|))
     (64 64 (:REWRITE |(equal (/ x) c)|))
     (64 64 (:REWRITE |(equal (/ x) (/ y))|))
     (64 64 (:REWRITE |(equal (- x) c)|))
     (64 64 (:REWRITE |(equal (- x) (- y))|))
     (62 62 (:REWRITE |(< 0 (/ x))|))
     (59 59
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (59 59
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (58 50 (:REWRITE DEFAULT-CDR))
     (56 56 (:REWRITE |(< (/ x) 0)|))
     (56 56 (:REWRITE |(< (* x y) 0)|))
     (56 14 (:REWRITE RATIONALP-X))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (55 55
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (55 55
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (38 30
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (38 30
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (38 30
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (33 33 (:REWRITE |(< (+ (- c) x) y)|))
     (30 30 (:REWRITE DEFAULT-MOD-2))
     (30 30 (:REWRITE DEFAULT-MOD-1))
     (30 30 (:REWRITE |(mod x (- y))| . 3))
     (30 30 (:REWRITE |(mod x (- y))| . 2))
     (30 30 (:REWRITE |(mod x (- y))| . 1))
     (30 30 (:REWRITE |(mod (- x) y)| . 3))
     (30 30 (:REWRITE |(mod (- x) y)| . 2))
     (30 30 (:REWRITE |(mod (- x) y)| . 1))
     (30 1 (:REWRITE |(+ (* c x) (* d x))|))
     (29 29 (:REWRITE RTL::PERM-MEMBER))
     (27 3 (:REWRITE MOD-POSITIVE . 3))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (26 26 (:REWRITE |(equal (* x y) 0)|))
     (26 26
         (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (15 15 (:REWRITE |(< y (+ (- c) x))|))
     (14 14 (:REWRITE REDUCE-RATIONALP-+))
     (14 14 (:REWRITE REDUCE-RATIONALP-*))
     (14 14 (:REWRITE RATIONALP-MINUS-X))
     (14 14 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:LINEAR RTL::MOD-BND-3))
     (2 2 (:REWRITE MOD-POSITIVE . 2))
     (1 1 (:REWRITE |(* 1 x)|))
     (1 1 (:REWRITE |(* 0 x)|)))
(RTL::PERM-REFLECTIONS
     (436980 6 (:DEFINITION RTL::REFLECTIONS))
     (335892 18
             (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (147338 35468
             (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (139608 180 (:REWRITE |(mod (- x) y)| . 1))
     (79953 2115
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (70596 126
            (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (47468 2912 (:REWRITE DEFAULT-PLUS-2))
     (42984 54 (:REWRITE MOD-X-I*J))
     (38880 54 (:REWRITE |(< (if a b c) x)|))
     (37704 96 (:REWRITE |(+ x (if a b c))|))
     (36816 42 (:REWRITE |(< x (if a b c))|))
     (35468 35468
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (35468 35468
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (35252 35252
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (32436 288 (:REWRITE CANCEL-MOD-+))
     (30902 2912 (:REWRITE DEFAULT-PLUS-1))
     (27946 1342 (:REWRITE INTEGERP-MINUS-X))
     (27811 8949 (:REWRITE DEFAULT-TIMES-2))
     (26760 26760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (26760 26760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (26760 26760
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (26460 342 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (25812 126 (:REWRITE |(+ (if a b c) x)|))
     (25614 234
            (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (25422 396 (:REWRITE RTL::MOD-DOES-NOTHING))
     (24858 342 (:REWRITE MOD-ZERO . 3))
     (22863 2241
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22104 342 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (19638 288 (:REWRITE MOD-X-Y-=-X . 3))
     (19224 288 (:REWRITE MOD-X-Y-=-X . 4))
     (18936 108 (:REWRITE |(+ (+ x y) z)|))
     (18588 1044 (:REWRITE DEFAULT-MINUS))
     (17850 3570 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (17850 3570 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (17850 3570
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (17850 3570
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (16704 342 (:REWRITE MOD-ZERO . 4))
     (14541 2749 (:REWRITE DEFAULT-LESS-THAN-1))
     (14187 2355 (:REWRITE |(< (- x) c)|))
     (13428 396 (:REWRITE DEFAULT-MOD-RATIO))
     (12621 8949 (:REWRITE DEFAULT-TIMES-1))
     (12397 2749 (:REWRITE DEFAULT-LESS-THAN-2))
     (10890 1026 (:REWRITE |(* (* x y) z)|))
     (9408 252 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (7489 2647
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7488 942 (:REWRITE |(- (* c x))|))
     (7026 42 (:REWRITE |(- (if a b c))|))
     (6966 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (6966 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (6966 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (6966 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (6552 630 (:REWRITE |(* y (* x z))|))
     (5703 2409 (:REWRITE |(< c (- x))|))
     (5262 288 (:REWRITE MOD-CANCEL-*-CONST))
     (4857 453 (:REWRITE |(+ 0 x)|))
     (3978 3978
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (3905 441
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3672 54 (:REWRITE FLOOR-ZERO . 3))
     (3570 3570
           (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (3570 3570 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (3570 3570 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (3570 3570
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (3570 3570
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (3570 3570
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (3493 2539
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3240 288 (:REWRITE MOD-X-Y-=-X . 2))
     (3240 288
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (3240 288
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (3204 720 (:REWRITE |(* (- x) y)|))
     (3058 446 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3033 495 (:REWRITE |(equal (- x) c)|))
     (2970 30 (:REWRITE |(- (+ x y))|))
     (2862 54 (:REWRITE CANCEL-FLOOR-+))
     (2749 2749 (:REWRITE THE-FLOOR-BELOW))
     (2749 2749 (:REWRITE THE-FLOOR-ABOVE))
     (2746 946 (:META META-INTEGERP-CORRECT))
     (2718 342 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (2718 342 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (2646 2539
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2409 2409
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2409 2409
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2409 2409
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2409 2409
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2409 2409
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2409 2409
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2409 2409
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2409 2409
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2409 2409 (:REWRITE |(< (/ x) (/ y))|))
     (2409 2409 (:REWRITE |(< (- x) (- y))|))
     (2304 2304 (:TYPE-PRESCRIPTION ABS))
     (2241 2241
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2241 2241 (:REWRITE INTEGERP-<-CONSTANT))
     (2241 2241 (:REWRITE CONSTANT-<-INTEGERP))
     (1998 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
     (1998 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (1998 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (1998 1998
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (1944 216 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1944 216
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1944 216
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1944 216
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (1944 216
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1890 54 (:REWRITE FLOOR-ZERO . 5))
     (1890 54 (:REWRITE FLOOR-ZERO . 4))
     (1836 54 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1692 180 (:REWRITE INTEGERP-/))
     (1683 441
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1674 54 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1620 396 (:REWRITE DEFAULT-MOD-1))
     (1411 1411
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1188 108 (:REWRITE |(* x (if a b c))|))
     (1188 54 (:REWRITE FLOOR-=-X/Y . 3))
     (1188 54 (:REWRITE FLOOR-=-X/Y . 2))
     (1152 1152 (:REWRITE DEFAULT-DIVIDE))
     (1080 216 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (1080 216 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (1080 216 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1080 216
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1026 54 (:REWRITE |(floor x 2)| . 2))
     (990 990 (:REWRITE |(* c (* d x))|))
     (990 126
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (972 162 (:REWRITE |(/ (* x y))|))
     (946 946 (:REWRITE REDUCE-INTEGERP-+))
     (936 936
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (908 10
          (:REWRITE RTL::PIGEONHOLE-PRINCIPLE-LEMMA-1))
     (864 54 (:REWRITE RTL::MOD-BY-1))
     (864 54 (:REWRITE |(mod x 1)|))
     (810 54 (:REWRITE |(mod x 2)| . 1))
     (783 495
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (774 774 (:REWRITE |(< (/ x) 0)|))
     (774 774 (:REWRITE |(< (* x y) 0)|))
     (624 624
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (624 624
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (594 54 (:REWRITE DEFAULT-FLOOR-RATIO))
     (593 593
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (587 587 (:REWRITE |(< 0 (* x y))|))
     (576 576 (:REWRITE |(* a (/ a))|))
     (575 423 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (552 552 (:REWRITE |(* 1 x)|))
     (495 495
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (495 495 (:REWRITE |(equal c (/ x))|))
     (495 495 (:REWRITE |(equal c (- x))|))
     (495 495 (:REWRITE |(equal (/ x) c)|))
     (495 495 (:REWRITE |(equal (/ x) (/ y))|))
     (495 495 (:REWRITE |(equal (- x) (- y))|))
     (486 486
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (462 309 (:REWRITE |(+ c (+ d x))|))
     (455 455 (:REWRITE |(< 0 (/ x))|))
     (441 441
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (396 396 (:REWRITE DEFAULT-MOD-2))
     (381 219 (:REWRITE |(< (+ c/d x) y)|))
     (377 377
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (377 377
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (342 84 (:REWRITE |(+ x (* c x))|))
     (329 138 (:REWRITE |(< x (+ c/d y))|))
     (288 288
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (270 270
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (270 270 (:REWRITE |(equal (* x y) 0)|))
     (270 54 (:REWRITE FLOOR-ZERO . 2))
     (270 54 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (270 54 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (270 54
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (270 54 (:REWRITE FLOOR-CANCEL-*-CONST))
     (270 54
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (249 12 (:REWRITE RTL::PERM-MEMBER))
     (248 216 (:REWRITE |(< (+ (- c) x) y)|))
     (236 1 (:REWRITE RTL::MEMBER-POSITIVES))
     (230 230 (:REWRITE |(* a (/ a) b)|))
     (216 216 (:TYPE-PRESCRIPTION FLOOR))
     (194 8 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (192 42 (:REWRITE |(+ (- x) (* c x))|))
     (180 180
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (180 180 (:REWRITE |(mod x (- y))| . 3))
     (180 180 (:REWRITE |(mod x (- y))| . 2))
     (180 180 (:REWRITE |(mod x (- y))| . 1))
     (180 180 (:REWRITE |(mod (- x) y)| . 3))
     (180 180 (:REWRITE |(mod (- x) y)| . 2))
     (174 6 (:DEFINITION MEMBER-EQUAL))
     (166 2 (:DEFINITION RTL::POSITIVES))
     (132 132 (:REWRITE |(< y (+ (- c) x))|))
     (126 126
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (126 126
          (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (126 126
          (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (126 126
          (:REWRITE |(< x (/ y)) with (< y 0)|))
     (126 126
          (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (108 108
          (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (108 108
          (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (108 108
          (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (108 108
          (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (90 90 (:REWRITE |(+ x (- x))|))
     (88 24 (:REWRITE ACL2-NUMBERP-X))
     (72 72
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (60 2 (:DEFINITION REMOVE1-EQUAL))
     (54 54 (:REWRITE MOD-X-I*J-V2))
     (54 54
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (54 54 (:REWRITE DEFAULT-FLOOR-2))
     (54 54 (:REWRITE DEFAULT-FLOOR-1))
     (54 54 (:REWRITE |(mod x 2)| . 2))
     (54 54 (:REWRITE |(floor x 2)| . 1))
     (54 54 (:REWRITE |(floor x (- y))| . 2))
     (54 54 (:REWRITE |(floor x (- y))| . 1))
     (54 54
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (54 54
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (54 54 (:REWRITE |(floor (- x) y)| . 2))
     (54 54 (:REWRITE |(floor (- x) y)| . 1))
     (54 54
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (54 54 (:REWRITE |(/ (/ x))|))
     (36 36 (:REWRITE FOLD-CONSTS-IN-+))
     (32 8 (:REWRITE RATIONALP-X))
     (26 26 (:REWRITE DEFAULT-CAR))
     (24 6 (:REWRITE |(+ x x)|))
     (20 20 (:REWRITE DEFAULT-CDR))
     (18 18
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (18 18
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (18 18
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (18 18 (:REWRITE |(equal (+ (- c) x) y)|))
     (18 18 (:REWRITE |(* x (- y))|))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 6 (:REWRITE |(- (- x))|)))
(RTL::TIMES-LIST-REFLECTIONS
     (291320 4 (:DEFINITION RTL::REFLECTIONS))
     (223928 12
             (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
     (98214 23626
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (93072 120 (:REWRITE |(mod (- x) y)| . 1))
     (53306 1406
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (47064 84
            (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (31654 1938 (:REWRITE DEFAULT-PLUS-2))
     (28656 36 (:REWRITE MOD-X-I*J))
     (26480 17824
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (25920 36 (:REWRITE |(< (if a b c) x)|))
     (25136 64 (:REWRITE |(+ x (if a b c))|))
     (24544 28 (:REWRITE |(< x (if a b c))|))
     (23626 23626
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (23626 23626
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (23482 23482
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (21624 192 (:REWRITE CANCEL-MOD-+))
     (21114 1294 (:REWRITE SIMPLIFY-SUMS-<))
     (20598 1938 (:REWRITE DEFAULT-PLUS-1))
     (18726 694 (:REWRITE NORMALIZE-ADDENDS))
     (18618 882 (:REWRITE INTEGERP-MINUS-X))
     (18559 5975 (:REWRITE DEFAULT-TIMES-2))
     (17824 17824
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (17824 17824
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (17824 17824
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (17640 228 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (17344 116 (:REWRITE |(+ y (+ x z))|))
     (17208 84 (:REWRITE |(+ (if a b c) x)|))
     (17076 156
            (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (16948 264 (:REWRITE RTL::MOD-DOES-NOTHING))
     (16572 228 (:REWRITE MOD-ZERO . 3))
     (15246 1490
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (14736 228 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (13092 192 (:REWRITE MOD-X-Y-=-X . 3))
     (12816 192 (:REWRITE MOD-X-Y-=-X . 4))
     (12624 72 (:REWRITE |(+ (+ x y) z)|))
     (12392 696 (:REWRITE DEFAULT-MINUS))
     (11900 2380 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (11900 2380 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (11900 2380
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11900 2380
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (11136 228 (:REWRITE MOD-ZERO . 4))
     (9686 1826 (:REWRITE DEFAULT-LESS-THAN-1))
     (9454 1566 (:REWRITE |(< (- x) c)|))
     (8952 264 (:REWRITE DEFAULT-MOD-RATIO))
     (8439 5975 (:REWRITE DEFAULT-TIMES-1))
     (8270 1826 (:REWRITE DEFAULT-LESS-THAN-2))
     (7964 296 (:REWRITE |(+ y x)|))
     (7300 688 (:REWRITE |(* (* x y) z)|))
     (6272 168 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (4992 628 (:REWRITE |(- (* c x))|))
     (4988 1760
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4684 28 (:REWRITE |(- (if a b c))|))
     (4644 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (4644 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (4644 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (4644 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (4368 420 (:REWRITE |(* y (* x z))|))
     (4292 628 (:DEFINITION FIX))
     (3798 1602 (:REWRITE |(< c (- x))|))
     (3508 192 (:REWRITE MOD-CANCEL-*-CONST))
     (3237 301 (:REWRITE |(+ 0 x)|))
     (2666 2666
           (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2601 293
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2448 36 (:REWRITE FLOOR-ZERO . 3))
     (2380 2380
           (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (2380 2380 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (2380 2380 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (2380 2380
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (2380 2380
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (2380 2380
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (2324 1688
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2160 192 (:REWRITE MOD-X-Y-=-X . 2))
     (2160 192
           (:REWRITE |(mod (+ x (mod a b)) y)|))
     (2160 192
           (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (2140 484 (:REWRITE |(* (- x) y)|))
     (2032 296 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2021 329 (:REWRITE |(equal (- x) c)|))
     (1980 20 (:REWRITE |(- (+ x y))|))
     (1908 36 (:REWRITE CANCEL-FLOOR-+))
     (1826 1826 (:REWRITE THE-FLOOR-BELOW))
     (1826 1826 (:REWRITE THE-FLOOR-ABOVE))
     (1818 618 (:META META-INTEGERP-CORRECT))
     (1812 228 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1812 228 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1736 148 (:REWRITE |(+ (* c x) (* d x))|))
     (1736 128 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1719 1688
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1602 1602
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1602 1602
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1602 1602
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1602 1602
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1602 1602
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1602 1602
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1602 1602
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1602 1602
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1602 1602 (:REWRITE |(< (/ x) (/ y))|))
     (1602 1602 (:REWRITE |(< (- x) (- y))|))
     (1536 1536 (:TYPE-PRESCRIPTION ABS))
     (1490 1490
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1490 1490 (:REWRITE INTEGERP-<-CONSTANT))
     (1490 1490 (:REWRITE CONSTANT-<-INTEGERP))
     (1332 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
     (1332 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (1332 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (1332 1332
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (1296 144 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1296 144
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1296 144
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1296 144
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (1296 144
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1260 36 (:REWRITE FLOOR-ZERO . 5))
     (1260 36 (:REWRITE FLOOR-ZERO . 4))
     (1224 36 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (1128 120 (:REWRITE INTEGERP-/))
     (1116 36 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1109 293
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1080 264 (:REWRITE DEFAULT-MOD-1))
     (938 938 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (792 72 (:REWRITE |(* x (if a b c))|))
     (792 36 (:REWRITE FLOOR-=-X/Y . 3))
     (792 36 (:REWRITE FLOOR-=-X/Y . 2))
     (768 768 (:REWRITE DEFAULT-DIVIDE))
     (720 144 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (720 144 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (720 144 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (720 144
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (710 12 (:REWRITE ZP-OPEN))
     (684 36 (:REWRITE |(floor x 2)| . 2))
     (664 664 (:REWRITE |(* c (* d x))|))
     (660 84
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (648 108 (:REWRITE |(/ (* x y))|))
     (624 624
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (618 618 (:REWRITE REDUCE-INTEGERP-+))
     (576 36 (:REWRITE RTL::MOD-BY-1))
     (576 36 (:REWRITE |(mod x 1)|))
     (540 36 (:REWRITE |(mod x 2)| . 1))
     (521 329
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (516 516 (:REWRITE |(< (/ x) 0)|))
     (516 516 (:REWRITE |(< (* x y) 0)|))
     (496 4 (:DEFINITION RTL::FACT))
     (416 416
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (416 416
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (398 398
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (396 36 (:REWRITE DEFAULT-FLOOR-RATIO))
     (389 389 (:REWRITE |(< 0 (* x y))|))
     (384 384 (:REWRITE |(* a (/ a))|))
     (381 281 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (368 368 (:REWRITE |(* 1 x)|))
     (329 329
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (329 329 (:REWRITE |(equal c (/ x))|))
     (329 329 (:REWRITE |(equal c (- x))|))
     (329 329 (:REWRITE |(equal (/ x) c)|))
     (329 329 (:REWRITE |(equal (/ x) (/ y))|))
     (329 329 (:REWRITE |(equal (- x) (- y))|))
     (324 324
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (322 207 (:REWRITE |(+ c (+ d x))|))
     (303 303 (:REWRITE |(< 0 (/ x))|))
     (293 293
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (264 264 (:REWRITE DEFAULT-MOD-2))
     (251 251
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (251 251
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (241 4 (:REWRITE RTL::PERM-MEMBER))
     (236 1 (:REWRITE RTL::MEMBER-POSITIVES))
     (228 56 (:REWRITE |(+ x (* c x))|))
     (212 142 (:REWRITE |(< (+ c/d x) y)|))
     (192 192
          (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (180 180
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (180 180 (:REWRITE |(equal (* x y) 0)|))
     (180 36 (:REWRITE FLOOR-ZERO . 2))
     (180 36 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (180 36 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (180 36
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (180 36 (:REWRITE FLOOR-CANCEL-*-CONST))
     (180 36
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (176 176 (:REWRITE |(* 0 x)|))
     (173 141 (:REWRITE |(< (+ (- c) x) y)|))
     (166 2 (:DEFINITION RTL::POSITIVES))
     (161 94 (:REWRITE |(< x (+ c/d y))|))
     (148 4 (:REWRITE |(* (+ x y) z)|))
     (146 146 (:REWRITE |(* a (/ a) b)|))
     (144 144 (:TYPE-PRESCRIPTION FLOOR))
     (128 28 (:REWRITE |(+ (- x) (* c x))|))
     (120 120
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (120 120 (:REWRITE |(mod x (- y))| . 3))
     (120 120 (:REWRITE |(mod x (- y))| . 2))
     (120 120 (:REWRITE |(mod x (- y))| . 1))
     (120 120 (:REWRITE |(mod (- x) y)| . 3))
     (120 120 (:REWRITE |(mod (- x) y)| . 2))
     (92 92 (:REWRITE |(< y (+ (- c) x))|))
     (84 84
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (84 84
         (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (84 84
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (84 84
         (:REWRITE |(< x (/ y)) with (< y 0)|))
     (84 84
         (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (72 72
         (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
     (72 72
         (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
     (72 72
         (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (72 72
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (60 60 (:REWRITE |(+ x (- x))|))
     (60 2 (:DEFINITION REMOVE1-EQUAL))
     (58 2 (:DEFINITION MEMBER-EQUAL))
     (48 48
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (44 12 (:REWRITE ACL2-NUMBERP-X))
     (36 36 (:REWRITE MOD-X-I*J-V2))
     (36 36
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (36 36 (:REWRITE DEFAULT-FLOOR-2))
     (36 36 (:REWRITE DEFAULT-FLOOR-1))
     (36 36 (:REWRITE |(mod x 2)| . 2))
     (36 36 (:REWRITE |(floor x 2)| . 1))
     (36 36 (:REWRITE |(floor x (- y))| . 2))
     (36 36 (:REWRITE |(floor x (- y))| . 1))
     (36 36
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (36 36
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (36 36 (:REWRITE |(floor (- x) y)| . 2))
     (36 36 (:REWRITE |(floor (- x) y)| . 1))
     (36 36
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (36 36 (:REWRITE |(/ (/ x))|))
     (24 24 (:REWRITE FOLD-CONSTS-IN-+))
     (16 4 (:REWRITE RATIONALP-X))
     (16 4 (:REWRITE |(+ x x)|))
     (12 12
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (12 12
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (12 12
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
     (12 12 (:REWRITE |(* x (- y))|))
     (11 11 (:REWRITE RTL::P-1-EVEN))
     (10 10 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(- (- x))|))
     (4 4 (:META META-RATIONALP-CORRECT)))
(RTL::MOD-MULT-2
     (340 68 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (324 68 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (320 320
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (320 320
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (320 320
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (320 320
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (300 68
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (300 68
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (224 2 (:LINEAR MOD-BOUNDS-3))
     (160 2 (:REWRITE |(* x (+ y z))|))
     (136 68 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (136 4 (:LINEAR MOD-BOUNDS-2))
     (136 4 (:LINEAR MOD-BOUNDS-1))
     (110 6 (:REWRITE RTL::MOD-DOES-NOTHING))
     (90 4 (:REWRITE |(* y (* x z))|))
     (72 4 (:REWRITE MOD-X-Y-=-X . 4))
     (72 4 (:REWRITE MOD-X-Y-=-X . 3))
     (70 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (70 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (70 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (70 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (68 68 (:TYPE-PRESCRIPTION NATP))
     (68 68 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (68 68 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (68 68
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (68 68 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (68 68 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (68 68
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (66 2 (:LINEAR RTL::MOD-BND-2))
     (60 2 (:LINEAR RTL::MOD-BND-1))
     (45 37 (:REWRITE DEFAULT-TIMES-2))
     (44 4 (:REWRITE MOD-ZERO . 3))
     (40 4 (:REWRITE DEFAULT-MOD-RATIO))
     (40 2 (:REWRITE |(+ (if a b c) x)|))
     (38 4 (:REWRITE MOD-ZERO . 4))
     (38 4 (:REWRITE MOD-X-Y-=-X . 2))
     (38 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (38 4
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (37 37 (:REWRITE DEFAULT-TIMES-1))
     (33 9 (:REWRITE DEFAULT-PLUS-2))
     (30 4 (:REWRITE CANCEL-MOD-+))
     (28 28 (:REWRITE THE-FLOOR-BELOW))
     (28 28 (:REWRITE THE-FLOOR-ABOVE))
     (28 28 (:REWRITE SIMPLIFY-SUMS-<))
     (28 28
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (28 28
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (28 28
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (28 28
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (28 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 28 (:REWRITE INTEGERP-<-CONSTANT))
     (28 28 (:REWRITE DEFAULT-LESS-THAN-2))
     (28 28 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (28 2 (:REWRITE |(* a (/ a))|))
     (26 2 (:REWRITE |(* x (if a b c))|))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (20 20 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (20 4
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (20 4
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (20 4
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (14 14
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (12 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (12 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 12 (:REWRITE |(equal (- x) c)|))
     (12 12 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:REWRITE |(< 0 (/ x))|))
     (12 12 (:REWRITE |(< 0 (* x y))|))
     (12 12 (:REWRITE |(< (/ x) 0)|))
     (12 12 (:REWRITE |(< (* x y) 0)|))
     (12 4 (:REWRITE MOD-CANCEL-*-CONST))
     (10 2 (:REWRITE |(+ 0 x)|))
     (9 9 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (8 8 (:REWRITE DEFAULT-DIVIDE))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (4 4 (:REWRITE DEFAULT-MOD-2))
     (4 4 (:REWRITE DEFAULT-MOD-1))
     (4 4 (:REWRITE |(mod x (- y))| . 3))
     (4 4 (:REWRITE |(mod x (- y))| . 2))
     (4 4 (:REWRITE |(mod x (- y))| . 1))
     (4 4
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(mod (- x) y)| . 3))
     (4 4 (:REWRITE |(mod (- x) y)| . 2))
     (4 4 (:REWRITE |(mod (- x) y)| . 1))
     (4 4
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (2 2 (:REWRITE |(* 1 x)|))
     (2 2 (:REWRITE |(* 0 x)|))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::TIMES-LIST-REFLECTION-MOD-PRODS
     (1049401 195 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (920385 195 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (211002 3987 (:REWRITE CANCEL-MOD-+))
     (183822 4058 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (180707 3987 (:REWRITE MOD-X-Y-=-X . 3))
     (179995 3987 (:REWRITE MOD-X-Y-=-X . 4))
     (170995 170995
             (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (170995 170995
             (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (170995 170995
             (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (167018 2534
             (:REWRITE RTL::MOD-MOD-PRODS-LEMMA-2))
     (162431 4058 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (161869 2610 (:REWRITE ZP-OPEN))
     (159647 4120 (:REWRITE RTL::MOD-DOES-NOTHING))
     (129040 25808 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (125984 4058 (:REWRITE MOD-ZERO . 4))
     (122484 25808 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (119532 25808
             (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (119532 25808
             (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (102020 44703 (:REWRITE DEFAULT-TIMES-2))
     (102006 28319
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (92779 4058 (:REWRITE DEFAULT-MOD-RATIO))
     (83477 44703 (:REWRITE DEFAULT-TIMES-1))
     (54502 8737 (:REWRITE DEFAULT-PLUS-2))
     (54176 25774
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (50870 28319 (:REWRITE DEFAULT-LESS-THAN-1))
     (49444 25774
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (45897 25894 (:REWRITE |(< (- x) c)|))
     (45523 1193 (:LINEAR RTL::MOD-BND-2))
     (39753 25774 (:REWRITE SIMPLIFY-SUMS-<))
     (36745 28319 (:REWRITE DEFAULT-LESS-THAN-2))
     (33863 8737 (:REWRITE DEFAULT-PLUS-1))
     (33502 25942 (:REWRITE |(< c (- x))|))
     (33238 5115
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (30028 25942 (:REWRITE |(< (- x) (- y))|))
     (29645 4826 (:REWRITE DEFAULT-MINUS))
     (28601 3987 (:REWRITE MOD-X-Y-=-X . 2))
     (28601 3987
            (:REWRITE |(mod (+ x (mod a b)) y)|))
     (28601 3987
            (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (28319 28319 (:REWRITE THE-FLOOR-BELOW))
     (28319 28319 (:REWRITE THE-FLOOR-ABOVE))
     (28319 28319
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (28319 28319
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (25942 25942
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (25942 25942
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (25942 25942
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (25942 25942
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (25942 25942
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (25942 25942
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (25942 25942
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (25942 25942
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (25942 25942 (:REWRITE |(< (/ x) (/ y))|))
     (25808 25808 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (25808 25808 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (25808 25808
            (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (25808 25808
            (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (25808 25808
            (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (25774 25774
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (25774 25774 (:REWRITE INTEGERP-<-CONSTANT))
     (25774 25774 (:REWRITE CONSTANT-<-INTEGERP))
     (25136 4058 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (25136 4058 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (23700 3987 (:REWRITE MOD-CANCEL-*-CONST))
     (21072 3987
            (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (21024 3939
            (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (21024 3939
            (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (20863 20863
            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (19496 19496
            (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (19496 19496
            (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (19496 19496
            (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (17409 5865 (:META META-INTEGERP-CORRECT))
     (15443 15443
            (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14200 2370 (:LINEAR MOD-BOUNDS-2))
     (13316 13289 (:REWRITE DEFAULT-DIVIDE))
     (13288 13288
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (12452 9740
            (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
     (9988 2857 (:REWRITE |(+ c (+ d x))|))
     (9740 9740
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (9740 9740
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (9740 9740
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (9110 9110 (:REWRITE |(< (/ x) 0)|))
     (9110 9110 (:REWRITE |(< (* x y) 0)|))
     (8990 8990
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8990 8990
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8904 4058 (:REWRITE DEFAULT-MOD-1))
     (7486 5189 (:REWRITE |(equal (/ x) c)|))
     (7183 3987
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (7028 7028
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
     (7028 7028
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
     (7028 7028
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
     (6408 6408 (:REWRITE |(* c (* d x))|))
     (6337 6337 (:REWRITE |(< 0 (* x y))|))
     (6271 3939
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (6263 3939
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (5979 5865 (:REWRITE INTEGERP-MINUS-X))
     (5912 620 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (5865 5865 (:REWRITE REDUCE-INTEGERP-+))
     (5720 2108 (:REWRITE INTEGERP-/))
     (5334 2667 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (5217 5190 (:REWRITE |(equal (/ x) (/ y))|))
     (5215 5188 (:REWRITE |(equal c (- x))|))
     (5192 5190
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (5190 5190
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (5189 5189 (:REWRITE |(equal c (/ x))|))
     (5115 5115
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4102 4102
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4058 4058 (:REWRITE DEFAULT-MOD-2))
     (3987 3987 (:REWRITE |(mod x (- y))| . 3))
     (3987 3987 (:REWRITE |(mod x (- y))| . 2))
     (3987 3987 (:REWRITE |(mod x (- y))| . 1))
     (3987 3987 (:REWRITE |(mod (- x) y)| . 3))
     (3987 3987 (:REWRITE |(mod (- x) y)| . 2))
     (3960 3960 (:REWRITE |(< 0 (/ x))|))
     (3912 3912
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3912 3912
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2667 2667 (:TYPE-PRESCRIPTION NATP))
     (2667 2667
           (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (2667 2667
           (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (2667 2667
           (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (2667 2667
           (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (2377 2377 (:REWRITE |(< x (+ c/d y))|))
     (2341 2341
           (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2136 2136
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (2136 2136
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (2136 2136
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (2136 2136
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (1881 209 (:REWRITE |(* (if a b c) x)|))
     (1839 18
           (:REWRITE |(equal (mod a n) (mod b n))|))
     (1614 1614 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1193 1193 (:LINEAR RTL::MOD-BND-3))
     (1107 1107
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1062 1062 (:REWRITE |(equal (* x y) 0)|))
     (1016 1016
           (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (888 21 (:REWRITE MOD-ZERO . 1))
     (748 748 (:REWRITE |(equal (+ (- c) x) y)|))
     (530 530
          (:REWRITE RTL::TIMES-LIST-EQUAL-FACT))
     (390 195
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (321 265 (:REWRITE DEFAULT-CDR))
     (321 265 (:REWRITE DEFAULT-CAR))
     (209 209 (:REWRITE |(* 0 x)|))
     (190 190 (:REWRITE FOLD-CONSTS-IN-+))
     (147 21 (:REWRITE MOD-ZERO . 2))
     (89 89 (:REWRITE |(< (+ c/d x) y)|))
     (89 89 (:REWRITE |(< (+ (- c) x) y)|))
     (55 1 (:REWRITE |(equal x (/ y))|))
     (28 1 (:REWRITE |(not (equal x (/ y)))|))
     (28 1 (:REWRITE |(/ (/ x))|))
     (27 2 (:REWRITE |(mod (+ 1 x) y)|))
     (18 18
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (12 12 (:TYPE-PRESCRIPTION RTL::PRIMEP))
     (9 3 (:REWRITE RTL::MOD-DISTINCT-REFLECT))
     (9 3 (:REWRITE RTL::MOD-DISTINCT))
     (4 2 (:REWRITE |(* -1 x)|))
     (3 3 (:REWRITE |(* 1 x)|))
     (2 2 (:TYPE-PRESCRIPTION ABS)))
(RTL::EULER-MU-EVEN
 (3416618 1598
          (:REWRITE RTL::MOD-MOD-PRODS-LEMMA-2))
 (2507793 322 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1089626 99 (:DEFINITION RTL::MOD-PRODS))
 (847117 322 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (503947 107
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (391882 4797 (:REWRITE CANCEL-MOD-+))
 (341139 107
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (298355 4797 (:REWRITE MOD-X-Y-=-X . 3))
 (273191 79166 (:REWRITE DEFAULT-TIMES-2))
 (270196 4797 (:REWRITE MOD-X-Y-=-X . 4))
 (264016 4838 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (257719 8696 (:REWRITE |(* (* x y) z)|))
 (257164 4838 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (242816 107
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (199272 4838 (:REWRITE MOD-ZERO . 4))
 (196748 26230
         (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (178859 4971 (:REWRITE DEFAULT-MOD-RATIO))
 (178665 178665
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (178665 178665
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (170057 4531
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (168072 94 (:REWRITE |(mod (if a b c) x)|))
 (166903 79166 (:REWRITE DEFAULT-TIMES-1))
 (158244 21294 (:REWRITE INTEGERP-MINUS-X))
 (138434 1252 (:REWRITE ZP-OPEN))
 (137981 26509
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (123344 1080 (:LINEAR RTL::MOD-BND-2))
 (108524 4725 (:REWRITE |(* y (* x z))|))
 (107749 107749
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (107749 107749
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (107593 107593
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (106491 31982 (:REWRITE DEFAULT-LESS-THAN-1))
 (87875 17575 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (87065 4797 (:REWRITE MOD-CANCEL-*-CONST))
 (86529 17575 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (86273 17575
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (86228 17566
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (79996 79780
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (79996 79780
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (79780 79780
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (79780
  79780
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (79780 79780
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (79780 79780
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (79780
      79780
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (79780
     79780
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (72830 1 (:DEFINITION RTL::REFLECTIONS))
 (71268 13935 (:REWRITE DEFAULT-PLUS-2))
 (71207 2869 (:REWRITE |(< x (+ c/d y))|))
 (68235 30125
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (66113 1078 (:LINEAR MOD-BOUNDS-3))
 (63882 9745 (:REWRITE DEFAULT-MINUS))
 (58957 4343 (:REWRITE |(mod (- x) y)| . 3))
 (56325 4343 (:REWRITE |(mod (- x) y)| . 2))
 (55854 4303
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (55377 28612 (:REWRITE |(< c (- x))|))
 (54474 30579
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (52281 31982 (:REWRITE DEFAULT-LESS-THAN-2))
 (51284 18188 (:META META-INTEGERP-CORRECT))
 (50979 4797 (:REWRITE MOD-X-Y-=-X . 2))
 (50979 4797
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (50979 4797
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (48363 13935 (:REWRITE DEFAULT-PLUS-1))
 (41616 133 (:REWRITE |(< (if a b c) x)|))
 (37925 37925
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (37391 4838 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (37391 4838 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (37335 1709
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (36816 42 (:REWRITE |(< x (if a b c))|))
 (35796 30125
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (32174 4264
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (31982 31982 (:REWRITE THE-FLOOR-BELOW))
 (31982 31982 (:REWRITE THE-FLOOR-ABOVE))
 (31461 4303
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (31044 39 (:REWRITE MOD-X-I*J))
 (30898 4082
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (29361 192
        (:REWRITE |(equal (mod a n) (mod b n))|))
 (28616 28612 (:REWRITE |(< (- x) (- y))|))
 (28612 28612
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (28612 28612
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (28612 28612
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (28612 28612
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (28612 28612
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (28612 28612
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (28612 28612
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (28612 28612
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (28612 28612 (:REWRITE |(< (/ x) (/ y))|))
 (26509 26509
        (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (26509 26509 (:REWRITE INTEGERP-<-CONSTANT))
 (26509 26509 (:REWRITE CONSTANT-<-INTEGERP))
 (23970 1410 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (23561 4570
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (23374 46 (:REWRITE |(+ x (if a b c))|))
 (19882 4971 (:REWRITE DEFAULT-MOD-1))
 (19140 4780 (:REWRITE |(equal (- x) c)|))
 (18853 15265
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (18853 15265
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (18853 15265
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (18853 15265
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (18642 91 (:REWRITE |(+ (if a b c) x)|))
 (18346 3941 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (18188 18188 (:REWRITE REDUCE-INTEGERP-+))
 (17575 17575
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (17575 17575
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (17566 17566 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (17566 17566
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (17130 2156 (:LINEAR MOD-BOUNDS-2))
 (16438 16438 (:REWRITE DEFAULT-DIVIDE))
 (16346 772 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (16094 16094
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (15083 15083
        (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13676 78 (:REWRITE |(+ (+ x y) z)|))
 (13602 13602 (:TYPE-PRESCRIPTION ABS))
 (10291 193 (:REWRITE |(* (if a b c) x)|))
 (10220 5053 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (10184 225 (:REWRITE DEFAULT-EXPT-2))
 (9704 9704 (:REWRITE |(* c (* d x))|))
 (9530 2550 (:REWRITE |(+ c (+ d x))|))
 (8967 8967 (:REWRITE |(< (* x y) 0)|))
 (8779 8779 (:REWRITE |(< (/ x) 0)|))
 (8396 8396 (:REWRITE |(< 0 (* x y))|))
 (7160 7160
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7160 7160
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6586 4780
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6076 6076
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5898 4734 (:REWRITE INTEGERP-/))
 (5667 5667 (:REWRITE |(< 0 (/ x))|))
 (5583 4303
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (5167 5053
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (5167 5053
       (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (5167 5053
       (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (5053 5053 (:TYPE-PRESCRIPTION NATP))
 (4971 4971 (:REWRITE DEFAULT-MOD-2))
 (4916 4780 (:REWRITE |(equal (- x) (- y))|))
 (4853 4853
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4780 4780
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4780 4780 (:REWRITE |(equal c (/ x))|))
 (4780 4780 (:REWRITE |(equal c (- x))|))
 (4780 4780 (:REWRITE |(equal (/ x) c)|))
 (4780 4780 (:REWRITE |(equal (/ x) (/ y))|))
 (4485 4485
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4440 746 (:REWRITE |(+ (* c x) (* d x))|))
 (4343 4343 (:REWRITE |(mod x (- y))| . 3))
 (4343 4343 (:REWRITE |(mod x (- y))| . 2))
 (4343 4343 (:REWRITE |(mod x (- y))| . 1))
 (4082 4082
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3950 290 (:LINEAR EXPT-<=-1-ONE))
 (3828 290 (:LINEAR EXPT->=-1-TWO))
 (3828 290 (:LINEAR EXPT->-1-TWO))
 (3828 290 (:LINEAR EXPT-<-1-ONE))
 (3490 172 (:REWRITE |(* x (if a b c))|))
 (3463 3463
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3462 290 (:LINEAR EXPT-X->=-X))
 (3462 290 (:LINEAR EXPT->=-1-ONE))
 (3462 290 (:LINEAR EXPT-<=-1-TWO))
 (3429 113 (:REWRITE |(* (+ x y) z)|))
 (3358 3358 (:REWRITE |(* a (/ a) b)|))
 (3340 290 (:LINEAR EXPT-X->-X))
 (3340 290 (:LINEAR EXPT->-1-ONE))
 (3340 290 (:LINEAR EXPT-<-1-TWO))
 (3327 954 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3068 3068
       (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3016 580
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2680 580
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2652 39 (:REWRITE FLOOR-ZERO . 3))
 (2397 2397 (:REWRITE |(equal (* x y) 0)|))
 (2222 227 (:REWRITE RTL::MOD-BY-1))
 (2222 227 (:REWRITE |(mod x 1)|))
 (2178 99 (:DEFINITION RTL::TIMES-LIST))
 (2067 39 (:REWRITE CANCEL-FLOOR-+))
 (1920 1920 (:REWRITE |(* a (/ a))|))
 (1919 227 (:REWRITE |(mod x 2)| . 2))
 (1843 322
       (:REWRITE |(equal (mod (+ x y) z) x)|))
 (1668 768 (:REWRITE |(< (+ c/d x) y)|))
 (1434 762 (:REWRITE |(< (+ (- c) x) y)|))
 (1404 156 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1404 156
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1404 156
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1404 156
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1404 156
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1365 39 (:REWRITE FLOOR-ZERO . 5))
 (1365 39 (:REWRITE FLOOR-ZERO . 4))
 (1353 1353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (1353 1353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (1353 1353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (1353 1353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
 (1326 39 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1222 94
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (1222 94
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1209 39 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1171 7 (:REWRITE |(- (if a b c))|))
 (1080 1080 (:LINEAR RTL::MOD-BND-3))
 (1068 6 (:REWRITE RTL::DIVIDES-FACT))
 (1034 1034 (:TYPE-PRESCRIPTION ZP))
 (872 872 (:REWRITE |(* 0 x)|))
 (858 39 (:REWRITE FLOOR-=-X/Y . 3))
 (858 39 (:REWRITE FLOOR-=-X/Y . 2))
 (780 156 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (780 156 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (780 156 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (780 156
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (773 227 (:REWRITE |(mod x 2)| . 1))
 (741 39 (:REWRITE |(floor x 2)| . 2))
 (702 117 (:REWRITE |(/ (* x y))|))
 (580 580
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (580 580
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (429 39 (:REWRITE DEFAULT-FLOOR-RATIO))
 (419 419 (:REWRITE |(< y (+ (- c) x))|))
 (396 99 (:DEFINITION IFIX))
 (290 290 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (290 290 (:LINEAR EXPT-LINEAR-UPPER-<))
 (290 290 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (290 290 (:LINEAR EXPT-LINEAR-LOWER-<))
 (279 279
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (279 279
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (279 279
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (279 279
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (266 266
      (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (266 266
      (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (266 266
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (266 266
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (265 2 (:REWRITE MOD-ZERO . 1))
 (227 227 (:REWRITE |(/ (/ x))|))
 (198 198 (:TYPE-PRESCRIPTION RTL::MOD-PRODS))
 (198 198
      (:REWRITE RTL::TIMES-LIST-EQUAL-FACT))
 (197 49 (:REWRITE |(+ x (* c x))|))
 (195 39 (:REWRITE FLOOR-ZERO . 2))
 (195 39 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (195 39 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (195 39
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (195 39 (:REWRITE FLOOR-CANCEL-*-CONST))
 (195 39
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (189 189 (:REWRITE |(equal (+ (- c) x) y)|))
 (188 188 (:DEFINITION RFIX))
 (162 6 (:REWRITE |(integerp (expt x n))|))
 (156 156 (:TYPE-PRESCRIPTION FLOOR))
 (131 131 (:REWRITE DEFAULT-EXPT-1))
 (131 131 (:REWRITE |(expt 1/c n)|))
 (131 131 (:REWRITE |(expt (- x) n)|))
 (129 129
      (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (114 114 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (107 107 (:REWRITE |(* x (- y))|))
 (99 99 (:REWRITE DEFAULT-CDR))
 (99 99 (:REWRITE DEFAULT-CAR))
 (94 94
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (92 28 (:REWRITE |(equal (expt x n) 0)|))
 (44 44 (:REWRITE FOLD-CONSTS-IN-+))
 (44 2 (:REWRITE MOD-ZERO . 2))
 (39 39 (:REWRITE MOD-X-I*J-V2))
 (39 39
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (39 39 (:REWRITE DEFAULT-FLOOR-2))
 (39 39 (:REWRITE DEFAULT-FLOOR-1))
 (39 39 (:REWRITE |(floor x 2)| . 1))
 (39 39 (:REWRITE |(floor x (- y))| . 2))
 (39 39 (:REWRITE |(floor x (- y))| . 1))
 (39 39
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (39 39
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (39 39 (:REWRITE |(floor (- x) y)| . 2))
 (39 39 (:REWRITE |(floor (- x) y)| . 1))
 (39 39
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (16 4 (:REWRITE |(+ x x)|)))
(RTL::EULER-MU-ODD
 (5722749 2671
          (:REWRITE RTL::MOD-MOD-PRODS-LEMMA-2))
 (3880833 528 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1319463 528 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (841590 198
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (765613 198
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (691280 8447 (:REWRITE CANCEL-MOD-+))
 (569698 198
         (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (532775 8447 (:REWRITE MOD-X-Y-=-X . 3))
 (493225 145465 (:REWRITE DEFAULT-TIMES-2))
 (484244 8637 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (483283 8447 (:REWRITE MOD-X-Y-=-X . 4))
 (472615 8637 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (409530 48945
         (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (371863 8637 (:REWRITE MOD-ZERO . 4))
 (368957 368957
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (368957 368957
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (318099 8917 (:REWRITE DEFAULT-MOD-RATIO))
 (299880 145465 (:REWRITE DEFAULT-TIMES-1))
 (294012 37131 (:REWRITE INTEGERP-MINUS-X))
 (284160 7887
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (281384 157 (:REWRITE |(mod (if a b c) x)|))
 (262167 49558
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (234048 2139 (:REWRITE ZP-OPEN))
 (225386 225386
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (225386 225386
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (224894 224894
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (223213 44687 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (209647 44687 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (205023 44687
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (198679 59405 (:REWRITE DEFAULT-LESS-THAN-1))
 (175403 28177 (:REWRITE DEFAULT-PLUS-2))
 (169286 7401
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (152144 8447 (:REWRITE MOD-CANCEL-*-CONST))
 (147246 146602
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (147246 146602
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (146602 146602
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (146602
  146602
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (146602 146602
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (146602 146602
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (146602
      146602
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (146602
     146602
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (125641 17958 (:REWRITE DEFAULT-MINUS))
 (119836 56071
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (119487 28177 (:REWRITE DEFAULT-PLUS-1))
 (119097 4958 (:REWRITE |(< x (+ c/d y))|))
 (111648 292 (:REWRITE |(< (if a b c) x)|))
 (108077 53391 (:REWRITE |(< c (- x))|))
 (102518 59405 (:REWRITE DEFAULT-LESS-THAN-2))
 (102067 56945
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (98678 7573 (:REWRITE |(mod (- x) y)| . 3))
 (97908 123 (:REWRITE MOD-X-I*J))
 (94282 7573 (:REWRITE |(mod (- x) y)| . 2))
 (90535 31519 (:META META-INTEGERP-CORRECT))
 (89707 8447 (:REWRITE MOD-X-Y-=-X . 2))
 (89707 8447
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (89707 8447
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (86300 114 (:REWRITE |(< x (if a b c))|))
 (72830 1 (:DEFINITION RTL::REFLECTIONS))
 (71226 130 (:REWRITE |(+ x (if a b c))|))
 (69344 69344
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (67849 8010
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (67069 8637 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (67069 8637 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (66589 56071
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (63180 2956
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (59405 59405 (:REWRITE THE-FLOOR-BELOW))
 (59405 59405 (:REWRITE THE-FLOOR-ABOVE))
 (58794 287 (:REWRITE |(+ (if a b c) x)|))
 (58709 7712
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (55274 53403 (:REWRITE |(< (- x) (- y))|))
 (53703 7278
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (53403 53403
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (53403 53403
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (53403 53403
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (53403 53403
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (53403 53403
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (53403 53403
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (53403 53403
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (53403 53403
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (53403 53403 (:REWRITE |(< (/ x) (/ y))|))
 (52570 7401
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (49558 49558
        (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (49558 49558 (:REWRITE INTEGERP-<-CONSTANT))
 (49558 49558 (:REWRITE CONSTANT-<-INTEGERP))
 (48638 317
        (:REWRITE |(equal (mod a n) (mod b n))|))
 (44687 44687
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (44687 44687
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (44613 44613 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (44600 44600
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (43521 8997 (:REWRITE |(equal (- x) c)|))
 (43132 246 (:REWRITE |(+ (+ x y) z)|))
 (40291 2419 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (38605 27289
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (38605 27289
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (38605 27289
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (38605 27289
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (35917 8917 (:REWRITE DEFAULT-MOD-1))
 (31519 31519 (:REWRITE REDUCE-INTEGERP-+))
 (31152 15198
        (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (29235 29235 (:REWRITE DEFAULT-DIVIDE))
 (28417 28417
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (28270 3606 (:LINEAR MOD-BOUNDS-2))
 (27690 27690
        (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (25250 25250 (:TYPE-PRESCRIPTION ABS))
 (17362 339 (:REWRITE |(* (if a b c) x)|))
 (17333 17300 (:REWRITE |(* c (* d x))|))
 (17309 495 (:REWRITE DEFAULT-EXPT-2))
 (16730 4648 (:REWRITE |(+ c (+ d x))|))
 (16284 15198
        (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (16284 15198
        (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (16284 15198
        (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (16175 16175 (:REWRITE |(< (* x y) 0)|))
 (15861 15861 (:REWRITE |(< (/ x) 0)|))
 (15563 15563 (:REWRITE |(< 0 (* x y))|))
 (14868 14868 (:TYPE-PRESCRIPTION NATP))
 (12903 12903
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12903 12903
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12898 1438 (:LINEAR EXPT-<=-1-ONE))
 (12516 1438 (:LINEAR EXPT->=-1-TWO))
 (12516 1438 (:LINEAR EXPT->-1-TWO))
 (12516 1438 (:LINEAR EXPT-<-1-ONE))
 (12348 9008
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12224 12224
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12098 2876
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (11456 7856 (:REWRITE INTEGERP-/))
 (11370 1438 (:LINEAR EXPT-X->=-X))
 (11370 1438 (:LINEAR EXPT->=-1-ONE))
 (11370 1438 (:LINEAR EXPT-<=-1-TWO))
 (11239 10867 (:REWRITE |(< 0 (/ x))|))
 (10988 1438 (:LINEAR EXPT-X->-X))
 (10988 1438 (:LINEAR EXPT->-1-ONE))
 (10988 1438 (:LINEAR EXPT-<-1-TWO))
 (10826 2876
        (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (10784 8997 (:REWRITE |(equal (- x) (- y))|))
 (10739 7401
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (9760 1452 (:REWRITE |(+ (* c x) (* d x))|))
 (9730 2133 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9369 9369
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9158 504 (:REWRITE |(equal (+ (- c) x) y)|))
 (9086 8997 (:REWRITE |(equal c (- x))|))
 (9008 9008
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8997 8997 (:REWRITE |(equal c (/ x))|))
 (8997 8997 (:REWRITE |(equal (/ x) c)|))
 (8997 8997 (:REWRITE |(equal (/ x) (/ y))|))
 (8917 8917 (:REWRITE DEFAULT-MOD-2))
 (8364 123 (:REWRITE FLOOR-ZERO . 3))
 (7985 7985
       (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (7712 7712
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7573 7573 (:REWRITE |(mod x (- y))| . 3))
 (7573 7573 (:REWRITE |(mod x (- y))| . 2))
 (7573 7573 (:REWRITE |(mod x (- y))| . 1))
 (7186 435 (:REWRITE |(* x (if a b c))|))
 (6736 216 (:REWRITE |(* (+ x y) z)|))
 (6519 123 (:REWRITE CANCEL-FLOOR-+))
 (6275 6275
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6143 5935 (:REWRITE |(* a (/ a) b)|))
 (5431 5431
       (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4637 437 (:REWRITE RTL::MOD-BY-1))
 (4637 437 (:REWRITE |(mod x 1)|))
 (4428 492 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (4428 492
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4428 492
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4428 492
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (4428 492
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4305 123 (:REWRITE FLOOR-ZERO . 5))
 (4305 123 (:REWRITE FLOOR-ZERO . 4))
 (4293 4293 (:REWRITE |(equal (* x y) 0)|))
 (4182 123 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (4060 3852 (:REWRITE |(* a (/ a))|))
 (4053 4053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (4053 4053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (4053 4053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (4053 4053
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
 (4004 182 (:DEFINITION RTL::TIMES-LIST))
 (3813 123 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3536 112 (:REWRITE |(integerp (expt x n))|))
 (3414 1464 (:REWRITE |(< (+ c/d x) y)|))
 (3263 437 (:REWRITE |(mod x 2)| . 2))
 (2964 527
       (:REWRITE |(equal (mod (+ x y) z) x)|))
 (2907 1451 (:REWRITE |(< (+ (- c) x) y)|))
 (2876 2876
       (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2876 2876
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2759 2759
       (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2706 123 (:REWRITE FLOOR-=-X/Y . 3))
 (2706 123 (:REWRITE FLOOR-=-X/Y . 2))
 (2460 492 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2460 492 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2460 492 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2460 492
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2337 123 (:REWRITE |(floor x 2)| . 2))
 (2314 13 (:REWRITE RTL::DIVIDES-FACT))
 (2214 369 (:REWRITE |(/ (* x y))|))
 (2159 437 (:REWRITE |(mod x 2)| . 1))
 (2041 157
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2041 157
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1985 1985 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (1808 1808 (:LINEAR RTL::MOD-BND-3))
 (1729 1729 (:REWRITE |(* 0 x)|))
 (1727 1727 (:TYPE-PRESCRIPTION ZP))
 (1438 1438 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1438 1438 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1438 1438 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1438 1438 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1353 123 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1171 7 (:REWRITE |(- (if a b c))|))
 (863 863 (:REWRITE |(< y (+ (- c) x))|))
 (850 11 (:REWRITE |(equal (expt x n) -1)|))
 (728 182 (:DEFINITION IFIX))
 (615 123 (:REWRITE FLOOR-ZERO . 2))
 (615 123 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (615 123 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (615 123
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (615 123 (:REWRITE FLOOR-CANCEL-*-CONST))
 (615 123
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (613 613
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (613 613
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (613 613
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (613 613
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (565 141 (:REWRITE |(+ x (* c x))|))
 (560 560
      (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (560 560
      (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (560 560
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (560 560
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (492 492 (:TYPE-PRESCRIPTION FLOOR))
 (449 449 (:REWRITE |(/ (/ x))|))
 (364 364 (:TYPE-PRESCRIPTION RTL::MOD-PRODS))
 (364 364
      (:REWRITE RTL::TIMES-LIST-EQUAL-FACT))
 (338 338 (:REWRITE DEFAULT-EXPT-1))
 (338 338 (:REWRITE |(expt 1/c n)|))
 (338 338 (:REWRITE |(expt (- x) n)|))
 (314 314 (:DEFINITION RFIX))
 (210 162 (:REWRITE |(equal (expt x n) 0)|))
 (182 182 (:REWRITE DEFAULT-CDR))
 (182 182 (:REWRITE DEFAULT-CAR))
 (157 157
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (123 123 (:REWRITE MOD-X-I*J-V2))
 (123 123
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (123 123 (:REWRITE DEFAULT-FLOOR-2))
 (123 123 (:REWRITE DEFAULT-FLOOR-1))
 (123 123 (:REWRITE |(floor x 2)| . 1))
 (123 123 (:REWRITE |(floor x (- y))| . 2))
 (123 123 (:REWRITE |(floor x (- y))| . 1))
 (123 123
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (123 123
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (123 123 (:REWRITE |(floor (- x) y)| . 2))
 (123 123 (:REWRITE |(floor (- x) y)| . 1))
 (123 123
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (120 120 (:REWRITE FOLD-CONSTS-IN-+))
 (65 5 (:REWRITE MOD-ZERO . 2)))
(RTL::GAUSS-LEMMA
 (93370 5
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (39639 1048
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38794 64 (:REWRITE |(mod (- x) y)| . 1))
 (30680 35 (:REWRITE |(< x (if a b c))|))
 (19881 49
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (17625 978 (:REWRITE SIMPLIFY-SUMS-<))
 (16823 1126 (:REWRITE DEFAULT-PLUS-2))
 (14539 108 (:REWRITE |(+ y (+ x z))|))
 (12345 12345
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12345 12345
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12285 12285
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (11940 15 (:REWRITE MOD-X-I*J))
 (11847 1126 (:REWRITE DEFAULT-PLUS-1))
 (11573 94 (:REWRITE CANCEL-MOD-+))
 (11230 434 (:REWRITE NORMALIZE-ADDENDS))
 (10800 15 (:REWRITE |(< (if a b c) x)|))
 (9862 9862
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9862 9862
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9862 9862
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (9690 109 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9085 1083
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8882 2664 (:REWRITE DEFAULT-TIMES-2))
 (8545 15 (:REWRITE |(+ x (if a b c))|))
 (8522 109 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (8226 109 (:REWRITE MOD-ZERO . 3))
 (8052 94 (:REWRITE MOD-X-Y-=-X . 3))
 (7937 94 (:REWRITE MOD-X-Y-=-X . 4))
 (7794 404 (:REWRITE INTEGERP-MINUS-X))
 (7740 1548 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (7588 1118 (:REWRITE |(< (- x) c)|))
 (7496 1548 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (7472 1548
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (7472 1548
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (7386 79
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (7384 1248 (:REWRITE DEFAULT-LESS-THAN-2))
 (7377 109 (:REWRITE MOD-ZERO . 4))
 (7170 35 (:REWRITE |(+ (if a b c) x)|))
 (6214 1248 (:REWRITE DEFAULT-LESS-THAN-1))
 (5718 3 (:LINEAR RTL::MOD-BND-1))
 (5260 30 (:REWRITE |(+ (+ x y) z)|))
 (4606 171 (:REWRITE |(+ y x)|))
 (4519 2664 (:REWRITE DEFAULT-TIMES-1))
 (4500 124 (:REWRITE DEFAULT-MOD-RATIO))
 (4038 286 (:REWRITE DEFAULT-MINUS))
 (3790 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (3746 151
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3062 78 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (3033 353 (:DEFINITION FIX))
 (3025 285 (:REWRITE |(* (* x y) z)|))
 (2543 1198
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2384 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (2048 1133 (:REWRITE |(< c (- x))|))
 (1979 269 (:REWRITE |(- (* c x))|))
 (1955 575
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (1955 575
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (1955 575
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (1955 575
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (1826 94 (:REWRITE MOD-CANCEL-*-CONST))
 (1820 175 (:REWRITE |(* y (* x z))|))
 (1693 148 (:REWRITE |(+ 0 x)|))
 (1660 214 (:REWRITE |(* (- x) y)|))
 (1548 1548 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (1548 1548 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1548 1548
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1548 1548
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1548 1548
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1505 175 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1433 1168
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1420 1420
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1420
  1420
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1420 1420
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1420 1420
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (1420
      1420
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1420
     1420
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1420 1420
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1420 1420
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1372 94 (:REWRITE MOD-X-Y-=-X . 2))
 (1372 94 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1372 94
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1352 97 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (1330 105 (:REWRITE |(+ (* c x) (* d x))|))
 (1263 3 (:LINEAR RTL::MOD-BND-2))
 (1248 1248 (:REWRITE THE-FLOOR-BELOW))
 (1248 1248 (:REWRITE THE-FLOOR-ABOVE))
 (1168 1168
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1168 1168
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1135 144 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1133 1133
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1133 1133
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1133 1133
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1133 1133
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1133 1133
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1133 1133
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1133 1133
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1133 1133
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1133 1133 (:REWRITE |(< (/ x) (/ y))|))
 (1133 1133 (:REWRITE |(< (- x) (- y))|))
 (1107 117 (:LINEAR EXPT-<=-1-ONE))
 (1083 1083
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1083 1083 (:REWRITE INTEGERP-<-CONSTANT))
 (1083 1083 (:REWRITE CONSTANT-<-INTEGERP))
 (1074 117 (:LINEAR EXPT->=-1-TWO))
 (1074 117 (:LINEAR EXPT->-1-TWO))
 (1074 117 (:LINEAR EXPT-<-1-ONE))
 (1026 109 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1026 109 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1020 15 (:REWRITE FLOOR-ZERO . 3))
 (975 117 (:LINEAR EXPT-X->=-X))
 (975 117 (:LINEAR EXPT->=-1-ONE))
 (975 117 (:LINEAR EXPT-<=-1-TWO))
 (942 117 (:LINEAR EXPT-X->-X))
 (942 117 (:LINEAR EXPT->-1-ONE))
 (942 117 (:LINEAR EXPT-<-1-TWO))
 (930 10 (:REWRITE |(- (+ x y))|))
 (872 167 (:REWRITE |(equal (- x) c)|))
 (817 14 (:REWRITE |(integerp (- x))|))
 (802 151
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (795 15 (:REWRITE CANCEL-FLOOR-+))
 (794 294 (:META META-INTEGERP-CORRECT))
 (763 15 (:REWRITE |(equal (+ (- c) x) y)|))
 (660 124 (:REWRITE DEFAULT-MOD-1))
 (641 641 (:TYPE-PRESCRIPTION ABS))
 (627 627 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (575 575
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4G))
 (575 575
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
 (575 575
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
 (575 575
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
 (546 49
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (540 60 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (540 60
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (540 60
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (540 60
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (540 60
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (525 15 (:REWRITE FLOOR-ZERO . 5))
 (525 15 (:REWRITE FLOOR-ZERO . 4))
 (510 15 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (470 50 (:REWRITE INTEGERP-/))
 (465 15 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (365 365 (:REWRITE DEFAULT-DIVIDE))
 (330 30 (:REWRITE |(* x (if a b c))|))
 (330 15 (:REWRITE FLOOR-=-X/Y . 3))
 (330 15 (:REWRITE FLOOR-=-X/Y . 2))
 (305 305
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (300 60 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (300 60 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (300 60 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (300 60
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (299 299 (:REWRITE |(< (/ x) 0)|))
 (299 299 (:REWRITE |(< (* x y) 0)|))
 (295 5 (:REWRITE ZP-OPEN))
 (294 294 (:REWRITE REDUCE-INTEGERP-+))
 (285 15 (:REWRITE |(floor x 2)| . 2))
 (282 3 (:LINEAR MOD-BOUNDS-3))
 (279 276 (:REWRITE |(* c (* d x))|))
 (278 278 (:REWRITE |(< 0 (* x y))|))
 (270 45 (:REWRITE |(/ (* x y))|))
 (259 259
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (254 254
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (254 254
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (249 168
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (243 243 (:REWRITE |(< 0 (/ x))|))
 (240 15 (:REWRITE RTL::MOD-BY-1))
 (240 15 (:REWRITE |(mod x 1)|))
 (234 234
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (234 234
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (234 234
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (234 234
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (225 15 (:REWRITE |(mod x 2)| . 1))
 (218 218
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (218 218
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (198 118 (:REWRITE |(+ c (+ d x))|))
 (168 168
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (167 167 (:REWRITE |(equal c (/ x))|))
 (167 167 (:REWRITE |(equal c (- x))|))
 (167 167 (:REWRITE |(equal (/ x) c)|))
 (167 167 (:REWRITE |(equal (/ x) (/ y))|))
 (167 167 (:REWRITE |(equal (- x) (- y))|))
 (165 15 (:REWRITE DEFAULT-FLOOR-RATIO))
 (160 160 (:REWRITE |(* a (/ a))|))
 (160 160 (:REWRITE |(* 1 x)|))
 (151 151
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (150 75 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
 (135 135
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (124 124 (:REWRITE DEFAULT-MOD-2))
 (117 117 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (117 117 (:LINEAR EXPT-LINEAR-UPPER-<))
 (117 117 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (117 117 (:LINEAR EXPT-LINEAR-LOWER-<))
 (115 115 (:REWRITE |(< (+ c/d x) y)|))
 (115 115 (:REWRITE |(< (+ (- c) x) y)|))
 (114 6 (:LINEAR MOD-BOUNDS-2))
 (110 110 (:REWRITE |(* 0 x)|))
 (89 89
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (86 1 (:REWRITE |(equal (expt x n) -1)|))
 (80 80
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (80 20 (:REWRITE |(+ x (* c x))|))
 (75 75 (:TYPE-PRESCRIPTION NATP))
 (75 75 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (75 75 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (75 75
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
 (75 75 (:REWRITE |(equal (* x y) 0)|))
 (75 15 (:REWRITE FLOOR-ZERO . 2))
 (75 15 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (75 15 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (75 15
     (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (75 15 (:REWRITE FLOOR-CANCEL-*-CONST))
 (75 15
     (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (70 15 (:REWRITE |(+ (- x) (* c x))|))
 (70 14 (:REWRITE |(equal (expt x n) 0)|))
 (64 64
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (64 64 (:REWRITE |(mod x (- y))| . 3))
 (64 64 (:REWRITE |(mod x (- y))| . 2))
 (64 64 (:REWRITE |(mod x (- y))| . 1))
 (64 64 (:REWRITE |(mod (- x) y)| . 3))
 (64 64 (:REWRITE |(mod (- x) y)| . 2))
 (60 60 (:TYPE-PRESCRIPTION FLOOR))
 (60 60 (:REWRITE |(* a (/ a) b)|))
 (55 55 (:REWRITE |(< y (+ (- c) x))|))
 (55 55 (:REWRITE |(< x (+ c/d y))|))
 (49 49
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (38 38 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (38 38
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (35 35
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (35 35
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (35 35
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (35 35
     (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (34 34
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (34 34 (:REWRITE |(+ x (- x))|))
 (32 2
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30
     (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (30 30
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (30 30
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (30 30
     (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (26 7 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (15 15 (:REWRITE MOD-X-I*J-V2))
 (15 15
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (15 15 (:REWRITE DEFAULT-FLOOR-2))
 (15 15 (:REWRITE DEFAULT-FLOOR-1))
 (15 15 (:REWRITE |(mod x 2)| . 2))
 (15 15 (:REWRITE |(floor x 2)| . 1))
 (15 15 (:REWRITE |(floor x (- y))| . 2))
 (15 15 (:REWRITE |(floor x (- y))| . 1))
 (15 15
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (15 15
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (15 15 (:REWRITE |(floor (- x) y)| . 2))
 (15 15 (:REWRITE |(floor (- x) y)| . 1))
 (15 15
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (15 15 (:REWRITE |(/ (/ x))|))
 (11 11 (:REWRITE RTL::P-1-EVEN))
 (5 5 (:REWRITE DEFAULT-EXPT-1))
 (5 5
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (5 5
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE |(* x (- y))|))
 (4 1 (:REWRITE |(+ x x)|))
 (3 3 (:LINEAR RTL::MOD-BND-3))
 (2 2 (:REWRITE |(equal x (if a b c))|))
 (2 2 (:REWRITE |(equal (if a b c) x)|)))
(RTL::MU-0-REWRITE
     (533 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (533 533
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (495 99 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (303 99 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (303 99
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (303 99
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (295 99 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (267 3 (:REWRITE CANCEL-MOD-+))
     (188 17 (:REWRITE INTEGERP-MINUS-X))
     (146 82 (:REWRITE DEFAULT-TIMES-2))
     (146 28 (:REWRITE SIMPLIFY-SUMS-<))
     (146 28
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (146 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (135 11 (:REWRITE |(* (* x y) z)|))
     (132 3 (:REWRITE MOD-ZERO . 3))
     (122 32 (:REWRITE DEFAULT-LESS-THAN-2))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (113 113
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (99 99 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (99 99
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (99 99 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (99 99
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (96 48 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (93 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (90 41 (:REWRITE DEFAULT-PLUS-2))
     (90 3 (:REWRITE MOD-X-Y-=-X . 3))
     (82 82 (:REWRITE DEFAULT-TIMES-1))
     (75 3 (:REWRITE DEFAULT-MOD-RATIO))
     (64 32 (:REWRITE DEFAULT-LESS-THAN-1))
     (62 14 (:META META-INTEGERP-CORRECT))
     (60 60
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (58 2 (:LINEAR MOD-BOUNDS-3))
     (48 48 (:TYPE-PRESCRIPTION NATP))
     (48 48 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (48 48
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (42 6 (:REWRITE INTEGERP-/))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 41 (:REWRITE NORMALIZE-ADDENDS))
     (41 41 (:REWRITE DEFAULT-PLUS-1))
     (32 32 (:REWRITE THE-FLOOR-BELOW))
     (32 32 (:REWRITE THE-FLOOR-ABOVE))
     (31 31
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (31 31
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (30 30
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (27 3 (:REWRITE DEFAULT-MINUS))
     (27 3 (:REWRITE |(- (* c x))|))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (15 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (15 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 3 (:REWRITE MOD-ZERO . 4))
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (15 3 (:REWRITE MOD-X-Y-=-X . 4))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE MOD-CANCEL-*-CONST))
     (15 3
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 3
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (14 14 (:REWRITE ZP-OPEN))
     (14 14 (:REWRITE REDUCE-INTEGERP-+))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (11 11 (:REWRITE DEFAULT-DIVIDE))
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
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 2 (:LINEAR RTL::MOD-BND-2))
     (3 3
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE DEFAULT-MOD-2))
     (3 3 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE |(mod x (- y))| . 3))
     (3 3 (:REWRITE |(mod x (- y))| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 1))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(mod (- x) y)| . 3))
     (3 3 (:REWRITE |(mod (- x) y)| . 2))
     (3 3 (:REWRITE |(mod (- x) y)| . 1))
     (3 3
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::MU-REWRITE-LEMMA-1
     (885 885
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (885 885
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (885 177 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (573 177 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (486 263 (:REWRITE DEFAULT-PLUS-2))
     (476 288 (:REWRITE DEFAULT-TIMES-2))
     (437 177
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (421 177 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (356 356
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (356 356
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (356 356
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (356 356
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (288 288 (:REWRITE DEFAULT-TIMES-1))
     (267 3 (:REWRITE CANCEL-MOD-+))
     (266 263 (:REWRITE DEFAULT-PLUS-1))
     (224 112 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (203 113 (:REWRITE DEFAULT-LESS-THAN-2))
     (202 202
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (201 201
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (199 69 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (194 23 (:REWRITE INTEGERP-MINUS-X))
     (193 113 (:REWRITE DEFAULT-LESS-THAN-1))
     (183 15 (:REWRITE |(* (* x y) z)|))
     (177 177 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (177 177
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (177 177
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (175 175
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (174 6 (:LINEAR MOD-BOUNDS-3))
     (132 3 (:REWRITE MOD-ZERO . 3))
     (113 113 (:REWRITE THE-FLOOR-BELOW))
     (113 113 (:REWRITE THE-FLOOR-ABOVE))
     (112 112 (:TYPE-PRESCRIPTION NATP))
     (112 112
          (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (112 112 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (112 112 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (112 112
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (94 94
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (94 94
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (93 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (90 3 (:REWRITE MOD-X-Y-=-X . 3))
     (75 3 (:REWRITE DEFAULT-MOD-RATIO))
     (73 73
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (68 20 (:META META-INTEGERP-CORRECT))
     (60 12 (:LINEAR MOD-BOUNDS-2))
     (46 46 (:REWRITE |(< x (+ c/d y))|))
     (42 6 (:REWRITE INTEGERP-/))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (28 4 (:REWRITE DEFAULT-MINUS))
     (27 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (27 3 (:REWRITE |(- (* c x))|))
     (25 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 24 (:REWRITE |(< y (+ (- c) x))|))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
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
     (15 15
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (15 15 (:REWRITE DEFAULT-DIVIDE))
     (15 3 (:REWRITE MOD-ZERO . 4))
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (15 3 (:REWRITE MOD-X-Y-=-X . 4))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE MOD-CANCEL-*-CONST))
     (15 3
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 3
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (12 12 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (12 6 (:LINEAR RTL::MOD-BND-2))
     (9 9 (:REWRITE ZP-OPEN))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:LINEAR RTL::MOD-BND-3))
     (3 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3 (:REWRITE DEFAULT-MOD-2))
     (3 3 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE |(mod x (- y))| . 3))
     (3 3 (:REWRITE |(mod x (- y))| . 2))
     (3 3 (:REWRITE |(mod x (- y))| . 1))
     (3 3
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(mod (- x) y)| . 3))
     (3 3 (:REWRITE |(mod (- x) y)| . 2))
     (3 3 (:REWRITE |(mod (- x) y)| . 1))
     (3 3
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
(RTL::MU-REWRITE-LEMMA-2
     (2643 6 (:DEFINITION RTL::MU))
     (2184 17 (:REWRITE RTL::MU-0-REWRITE))
     (1058 37 (:REWRITE |(< (+ c/d x) y)|))
     (1012 384 (:REWRITE DEFAULT-PLUS-2))
     (750 50
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (735 40
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (684 684
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (684 684
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (684 684
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (684 684
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (543 384 (:REWRITE DEFAULT-PLUS-1))
     (515 20 (:REWRITE RTL::INTEGERP-FL))
     (391 43 (:REWRITE |(< (- x) c)|))
     (365 201 (:REWRITE DEFAULT-TIMES-2))
     (329 6 (:REWRITE ZP-OPEN))
     (310 10 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (257 32 (:REWRITE RTL::FL+INT-REWRITE))
     (211 211
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (201 201 (:REWRITE DEFAULT-TIMES-1))
     (168 31 (:REWRITE |(+ c (+ d x))|))
     (126 126
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (108 6 (:REWRITE |(- (+ x y))|))
     (106 57 (:REWRITE DEFAULT-LESS-THAN-1))
     (101 57 (:REWRITE DEFAULT-LESS-THAN-2))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (100 100
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (86 37 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (80 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (71 18 (:REWRITE DEFAULT-MINUS))
     (62 37
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (58 13 (:REWRITE |(+ (- x) (* c x))|))
     (57 57 (:REWRITE THE-FLOOR-BELOW))
     (57 57 (:REWRITE THE-FLOOR-ABOVE))
     (54 54 (:REWRITE REDUCE-INTEGERP-+))
     (54 54 (:REWRITE INTEGERP-MINUS-X))
     (54 54 (:META META-INTEGERP-CORRECT))
     (50 50
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (50 50
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (47 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
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
     (43 43 (:REWRITE |(< (- x) (- y))|))
     (39 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (37 37 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (37 37
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (37 37 (:REWRITE INTEGERP-<-CONSTANT))
     (37 37 (:REWRITE CONSTANT-<-INTEGERP))
     (34 34 (:REWRITE |(< x (+ c/d y))|))
     (30 30 (:REWRITE |(* a (/ a) b)|))
     (24 6 (:REWRITE |(- (* c x))|))
     (23 23 (:REWRITE |(< (+ (- c) x) y)|))
     (20 20 (:REWRITE |(< y (+ (- c) x))|))
     (17 17 (:TYPE-PRESCRIPTION NATP))
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
     (12 12 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
     (7 7 (:REWRITE |(* 1 x)|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (6 6 (:REWRITE RTL::MOD-DOES-NOTHING))
     (6 6 (:REWRITE FOLD-CONSTS-IN-+))
     (6 6 (:REWRITE |(< 0 (/ x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE |(* (- x) y)|))
     (6 6 (:LINEAR RTL::N<=FL-LINEAR))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::MU-REWRITE-LEMMA-3
     (424 8 (:REWRITE CANCEL-MOD-+))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (348 348
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (248 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (240 8 (:REWRITE MOD-X-Y-=-X . 3))
     (218 34 (:REWRITE INTEGERP-MINUS-X))
     (208 8 (:REWRITE RTL::MOD-DOES-NOTHING))
     (200 40 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (200 40 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (176 8 (:REWRITE MOD-ZERO . 3))
     (136 16 (:REWRITE |(* (- x) y)|))
     (128 40 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (128 40
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (128 40
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (128 8 (:REWRITE RTL::INTEGERP-FL))
     (104 26 (:REWRITE |(* y x)|))
     (88 8 (:REWRITE DEFAULT-MOD-RATIO))
     (80 16 (:REWRITE DEFAULT-MINUS))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (76 76 (:REWRITE DEFAULT-TIMES-2))
     (76 76 (:REWRITE DEFAULT-TIMES-1))
     (72 16 (:REWRITE |(- (* c x))|))
     (44 2 (:LINEAR MOD-BOUNDS-3))
     (42 42
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (40 40 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (40 40
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (40 40 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (40 40
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (40 8 (:REWRITE MOD-ZERO . 4))
     (40 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (40 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (40 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (40 8 (:REWRITE MOD-X-Y-=-X . 4))
     (40 8 (:REWRITE MOD-X-Y-=-X . 2))
     (40 8
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (40 8 (:REWRITE MOD-CANCEL-*-CONST))
     (40 8 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (40 8
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (40 8
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (36 18 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (26 26 (:REWRITE REDUCE-INTEGERP-+))
     (26 26 (:META META-INTEGERP-CORRECT))
     (24 24 (:REWRITE THE-FLOOR-BELOW))
     (24 24 (:REWRITE THE-FLOOR-ABOVE))
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
     (24 24 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (18 18
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (18 18 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (18 18 (:TYPE-PRESCRIPTION NATP))
     (18 18 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (18 18 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (18 18 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (18 18
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (8 8 (:REWRITE DEFAULT-MOD-2))
     (8 8 (:REWRITE DEFAULT-MOD-1))
     (8 8 (:REWRITE |(mod x (- y))| . 3))
     (8 8 (:REWRITE |(mod x (- y))| . 2))
     (8 8 (:REWRITE |(mod x (- y))| . 1))
     (8 8
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (8 8
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (8 8 (:REWRITE |(mod (- x) y)| . 3))
     (8 8 (:REWRITE |(mod (- x) y)| . 2))
     (8 8 (:REWRITE |(mod (- x) y)| . 1))
     (8 8
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (8 8 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:LINEAR RTL::N<=FL-LINEAR))
     (2 2 (:LINEAR RTL::MOD-BND-3)))
(RTL::MU-REWRITE (1535 36 (:REWRITE RTL::INTEGERP-FL))
                 (819 68
                      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
                 (515 54 (:REWRITE RTL::FL+INT-REWRITE))
                 (385 98 (:REWRITE DEFAULT-PLUS-2))
                 (352 352
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                 (352 352
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                 (352 352
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                 (352 352
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                 (264 264
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                 (264 264
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                 (264 264
                      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                 (235 47 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                 (235 47 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                 (228 74 (:META META-INTEGERP-CORRECT))
                 (179 98 (:REWRITE DEFAULT-PLUS-1))
                 (175 47 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                 (175 47
                      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                 (175 47
                      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                 (77 77
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (74 74 (:REWRITE REDUCE-INTEGERP-+))
                 (74 74 (:REWRITE INTEGERP-MINUS-X))
                 (59 42 (:REWRITE DEFAULT-TIMES-2))
                 (53 14 (:REWRITE DEFAULT-MINUS))
                 (47 47 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                 (47 47
                     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                 (47 47 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                 (47 47
                     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                 (44 42 (:REWRITE DEFAULT-TIMES-1))
                 (31 31
                     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
                 (30 15 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
                 (28 28 (:LINEAR RTL::FL-MONOTONE-LINEAR))
                 (22 5
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (15 15
                     (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
                 (15 15 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                 (15 15 (:TYPE-PRESCRIPTION NATP))
                 (15 15 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                 (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                 (15 15 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
                 (15 15
                     (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
                 (14 14 (:LINEAR RTL::N<=FL-LINEAR))
                 (12 3 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                 (10 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (8 8 (:REWRITE |(* (- x) y)|))
                 (7 7
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                 (5 5
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (5 5 (:REWRITE |(equal c (/ x))|))
                 (5 5 (:REWRITE |(equal c (- x))|))
                 (5 5 (:REWRITE |(equal (/ x) c)|))
                 (5 5 (:REWRITE |(equal (- x) c)|))
                 (4 4 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::NO-INTEGER-7-8)
(RTL::MOD-P-8-CHOICES
     (3652 3652
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3652 3652
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (3652 3652
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2575 515 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2575 515 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2561 67 (:REWRITE CANCEL-MOD-+))
     (1791 515
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1791 515
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1733 67 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (1517 67 (:REWRITE MOD-X-Y-=-X . 3))
     (1491 515 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1454 22 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (1417 67 (:REWRITE RTL::MOD-DOES-NOTHING))
     (1214 22 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (1088 1088
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1088 1088
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1088 1088
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1034 863 (:REWRITE DEFAULT-TIMES-2))
     (1009 128 (:REWRITE INTEGERP-MINUS-X))
     (955 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (949 108
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (879 138 (:REWRITE |(* (- x) y)|))
     (863 863 (:REWRITE DEFAULT-TIMES-1))
     (742 67
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (681 14 (:REWRITE |(equal (+ (- c) x) y)|))
     (644 66 (:REWRITE RTL::INTEGERP-FL))
     (520 419 (:REWRITE DEFAULT-PLUS-2))
     (519 110
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (515 515 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (515 515
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (515 515
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (515 515
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (497 67 (:REWRITE DEFAULT-MOD-RATIO))
     (488 419 (:REWRITE DEFAULT-PLUS-1))
     (488 67 (:REWRITE MOD-ZERO . 3))
     (484 484
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (412 137 (:REWRITE DEFAULT-MINUS))
     (404 202 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (335 67 (:REWRITE MOD-ZERO . 4))
     (335 67 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (335 67 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (335 67 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (335 67 (:REWRITE MOD-X-Y-=-X . 4))
     (335 67 (:REWRITE MOD-X-Y-=-X . 2))
     (335 67 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (335 67
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (319 67
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (319 67
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (292 172
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (292 172 (:REWRITE DEFAULT-LESS-THAN-2))
     (262 172
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (231 67 (:REWRITE MOD-CANCEL-*-CONST))
     (204 204
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (202 202 (:TYPE-PRESCRIPTION NATP))
     (202 202 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (202 202 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (202 202
          (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (202 172 (:REWRITE DEFAULT-LESS-THAN-1))
     (196 196 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (188 68 (:REWRITE |(equal (- x) c)|))
     (174 174 (:REWRITE THE-FLOOR-BELOW))
     (174 174 (:REWRITE THE-FLOOR-ABOVE))
     (172 172
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (172 172
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (172 172
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (172 172
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (172 172 (:REWRITE INTEGERP-<-CONSTANT))
     (172 172 (:REWRITE CONSTANT-<-INTEGERP))
     (172 172
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (172 172
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (172 172
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (172 172
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (172 172 (:REWRITE |(< c (- x))|))
     (172 172
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (172 172
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (172 172
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (172 172
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (172 172 (:REWRITE |(< (/ x) (/ y))|))
     (172 172 (:REWRITE |(< (- x) c)|))
     (172 172 (:REWRITE |(< (- x) (- y))|))
     (88 8 (:LINEAR MOD-BOUNDS-3))
     (83 67
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (83 67
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (81 9 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (81 9
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (81 9
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (81 9
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (81 9
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (80 16 (:LINEAR MOD-BOUNDS-2))
     (69 68 (:REWRITE |(equal (- x) (- y))|))
     (68 68 (:REWRITE |(equal c (/ x))|))
     (68 68 (:REWRITE |(equal c (- x))|))
     (68 68 (:REWRITE |(equal (/ x) c)|))
     (68 68 (:REWRITE |(equal (/ x) (/ y))|))
     (67 67
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (67 67 (:REWRITE DEFAULT-MOD-2))
     (67 67 (:REWRITE DEFAULT-MOD-1))
     (67 67 (:REWRITE |(mod x (- y))| . 3))
     (67 67 (:REWRITE |(mod x (- y))| . 2))
     (67 67 (:REWRITE |(mod x (- y))| . 1))
     (67 67
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (67 67
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (67 67 (:REWRITE |(mod (- x) y)| . 3))
     (67 67 (:REWRITE |(mod (- x) y)| . 2))
     (67 67 (:REWRITE |(mod (- x) y)| . 1))
     (64 64 (:LINEAR RTL::FL-MONOTONE-LINEAR))
     (63 63 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (61 61 (:REWRITE REDUCE-INTEGERP-+))
     (61 61 (:META META-INTEGERP-CORRECT))
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
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (45 9
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (45 9
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (32 32 (:LINEAR RTL::N<=FL-LINEAR))
     (28 25 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (24 24 (:REWRITE RTL::PERM-MEMBER))
     (22 22
         (:REWRITE |(equal (mod (+ x y) z) x)|))
     (16 4 (:REWRITE REDUCE-RATIONALP-*))
     (14 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (8 8 (:LINEAR RTL::MOD-BND-3))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (4 4 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 1 (:REWRITE |(* -1 x)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE MOD-POSITIVE . 3))
     (2 2 (:REWRITE MOD-POSITIVE . 2))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 1 (:REWRITE |(- (- x))|)))
(RTL::SECOND-SUPPLEMENT
     (901 17 (:REWRITE CANCEL-MOD-+))
     (723 723
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (723 723
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (550 110 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (550 110 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (438 47 (:REWRITE INTEGERP-MINUS-X))
     (338 110
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (296 17 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (289 34 (:REWRITE |(* (- x) y)|))
     (278 17 (:REWRITE MOD-X-Y-=-X . 3))
     (261 21
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (261 21
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (258 94
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (258 33 (:REWRITE RTL::MOD-DOES-NOTHING))
     (257 9 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (214 180 (:REWRITE DEFAULT-TIMES-2))
     (213 35
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (206 17 (:REWRITE MOD-ZERO . 3))
     (187 17 (:REWRITE DEFAULT-MOD-RATIO))
     (185 180 (:REWRITE DEFAULT-TIMES-1))
     (170 34 (:REWRITE DEFAULT-MINUS))
     (161 157
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (157 157
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (157 157
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (157 157
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (153 34 (:REWRITE |(- (* c x))|))
     (137 9 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (110 110
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (110 110
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (106 53 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (100 100
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (98 75 (:REWRITE DEFAULT-PLUS-2))
     (94 94 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (94 94
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (85 17 (:REWRITE MOD-ZERO . 4))
     (85 17 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (85 17 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (85 17 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (85 17 (:REWRITE MOD-X-Y-=-X . 4))
     (85 17 (:REWRITE MOD-X-Y-=-X . 2))
     (85 17
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (85 17 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (85 17
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (85 17
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (79 75 (:REWRITE DEFAULT-PLUS-1))
     (64 4 (:REWRITE RTL::INTEGERP-FL))
     (62 14 (:REWRITE |(+ c (+ d x))|))
     (53 53
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (53 53 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (53 53 (:TYPE-PRESCRIPTION NATP))
     (53 53 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (53 53 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (53 53 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (53 53
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (48 8 (:LINEAR MOD-BOUNDS-1))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (37 17 (:REWRITE MOD-CANCEL-*-CONST))
     (35 35 (:REWRITE THE-FLOOR-BELOW))
     (35 35 (:REWRITE THE-FLOOR-ABOVE))
     (35 35 (:REWRITE SIMPLIFY-SUMS-<))
     (35 35
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (35 35
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (35 35
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (35 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 35 (:REWRITE INTEGERP-<-CONSTANT))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-2))
     (35 35 (:REWRITE DEFAULT-LESS-THAN-1))
     (35 35 (:REWRITE CONSTANT-<-INTEGERP))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< c (- x))|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (35 35
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (35 35 (:REWRITE |(< (/ x) (/ y))|))
     (35 35 (:REWRITE |(< (- x) c)|))
     (35 35 (:REWRITE |(< (- x) (- y))|))
     (34 34
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (34 34 (:REWRITE NORMALIZE-ADDENDS))
     (30 30 (:REWRITE REDUCE-INTEGERP-+))
     (30 30 (:META META-INTEGERP-CORRECT))
     (21 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (20 4 (:LINEAR MOD-BOUNDS-3))
     (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (17 17 (:REWRITE DEFAULT-MOD-2))
     (17 17 (:REWRITE DEFAULT-MOD-1))
     (17 17 (:REWRITE |(mod x (- y))| . 3))
     (17 17 (:REWRITE |(mod x (- y))| . 2))
     (17 17 (:REWRITE |(mod x (- y))| . 1))
     (17 17
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (17 17
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (17 17 (:REWRITE |(mod (- x) y)| . 3))
     (17 17 (:REWRITE |(mod (- x) y)| . 2))
     (17 17 (:REWRITE |(mod (- x) y)| . 1))
     (17 17
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (9 9 (:REWRITE RTL::PERM-MEMBER))
     (9 9 (:REWRITE RTL::NO-INTEGER-7-8))
     (9 9
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (8 4 (:LINEAR RTL::MOD-BND-2))
     (8 4 (:LINEAR RTL::MOD-BND-1))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:LINEAR RTL::MOD-BND-3)))
