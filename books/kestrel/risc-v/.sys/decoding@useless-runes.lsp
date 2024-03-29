(RISCV::GET-OPCODE)
(RISCV::UBYTE7P-OF-GET-OPCODE
 (10 1 (:REWRITE LOGHEAD-IDENTITY))
 (8 1 (:DEFINITION UNSIGNED-BYTE-P))
 (6 1 (:DEFINITION INTEGER-RANGE-P))
 (3 1 (:REWRITE LOGTAIL-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-0))
 (1 1 (:REWRITE LOGTAIL-0-I))
 )
(RISCV::GET-RD)
(RISCV::UBYTE5P-OF-GET-RD
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-RS1)
(RISCV::UBYTE5P-OF-GET-RS1
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-RS2)
(RISCV::UBYTE5P-OF-GET-RS2
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-FUNCT3)
(RISCV::UBYTE3P-OF-GET-FUNCT3
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-FUNCT7)
(RISCV::UBYTE7P-OF-GET-FUNCT7
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-IMM-ITYPE)
(RISCV::UBYTE12P-OF-GET-IMM-ITYPE
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-IMM-STYPE)
(RISCV::UBYTE12P-OF-GET-IMM-STYPE
 (19294 4 (:REWRITE LOGHEAD-IDENTITY))
 (10718 20 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (9042 136 (:REWRITE THE-FLOOR-ABOVE))
 (8884 4 (:REWRITE |(< (if a b c) x)|))
 (5300 30 (:REWRITE |(+ y x)|))
 (4820 2 (:LINEAR LOGHEAD-LEQ))
 (3690 3690 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (3690 3690 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3690 3690 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3690 3690 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3156 71 (:REWRITE DEFAULT-PLUS-1))
 (3146 71 (:REWRITE DEFAULT-PLUS-2))
 (3075 21 (:REWRITE NORMALIZE-ADDENDS))
 (1534 158 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1422 158 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1422 158 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (1422 158 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1228 22 (:REWRITE FLOOR-ZERO . 3))
 (1170 130 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1166 22 (:REWRITE CANCEL-FLOOR-+))
 (1008 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1008 10 (:DEFINITION FIX))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (790 158 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (646 126 (:REWRITE DEFAULT-LESS-THAN-1))
 (634 22 (:REWRITE FLOOR-ZERO . 5))
 (632 22 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (624 22 (:REWRITE FLOOR-ZERO . 4))
 (620 22 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (618 112 (:REWRITE INTEGERP-MINUS-X))
 (530 122 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (506 506 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (506 506 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (506 506 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (506 506 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (484 22 (:REWRITE FLOOR-=-X/Y . 2))
 (440 398 (:REWRITE DEFAULT-TIMES-2))
 (400 398 (:REWRITE DEFAULT-TIMES-1))
 (374 44 (:REWRITE |(* (- x) y)|))
 (280 25 (:REWRITE DEFAULT-FLOOR-RATIO))
 (260 10 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (220 44 (:REWRITE DEFAULT-MINUS))
 (220 10 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (204 204 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (198 44 (:REWRITE |(- (* c x))|))
 (188 112 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (188 112 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (136 136 (:REWRITE THE-FLOOR-BELOW))
 (130 130 (:TYPE-PRESCRIPTION FLOOR))
 (130 112 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (126 126 (:REWRITE DEFAULT-LESS-THAN-2))
 (124 2 (:REWRITE LOGTAIL-IDENTITY))
 (118 2 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
 (114 112 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (112 112 (:REWRITE SIMPLIFY-SUMS-<))
 (112 112 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (112 112 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (112 112 (:REWRITE INTEGERP-<-CONSTANT))
 (112 112 (:REWRITE CONSTANT-<-INTEGERP))
 (112 112 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (112 112 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (112 112 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (112 112 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (112 112 (:REWRITE |(< c (- x))|))
 (112 112 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (112 112 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (112 112 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (112 112 (:REWRITE |(< (/ x) (/ y))|))
 (112 112 (:REWRITE |(< (- x) c)|))
 (112 112 (:REWRITE |(< (- x) (- y))|))
 (110 22 (:REWRITE FLOOR-ZERO . 2))
 (110 22 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (110 22 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (102 22 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (102 22 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (94 22 (:REWRITE FLOOR-CANCEL-*-CONST))
 (90 90 (:REWRITE REDUCE-INTEGERP-+))
 (90 90 (:META META-INTEGERP-CORRECT))
 (80 80 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (67 67 (:REWRITE |(< (* x y) 0)|))
 (61 61 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (61 61 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (61 61 (:REWRITE |(< (/ x) 0)|))
 (50 10 (:REWRITE |(+ 0 x)|))
 (46 46 (:TYPE-PRESCRIPTION ABS))
 (30 22 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (30 22 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (26 25 (:REWRITE DEFAULT-FLOOR-1))
 (25 25 (:REWRITE DEFAULT-FLOOR-2))
 (22 22 (:REWRITE |(floor x (- y))| . 2))
 (22 22 (:REWRITE |(floor x (- y))| . 1))
 (22 22 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (22 22 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (22 22 (:REWRITE |(floor (- x) y)| . 2))
 (22 22 (:REWRITE |(floor (- x) y)| . 1))
 (22 22 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (20 10 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (18 18 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< 0 (/ x))|))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (14 2 (:REWRITE |(* (if a b c) x)|))
 (11 11 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE |(+ x (- x))|))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 )
(RISCV::GET-IMM-BTYPE)
(RISCV::UBYTE12P-OF-GET-IMM-BTYPE
 (29616 6 (:REWRITE LOGHEAD-IDENTITY))
 (17768 8 (:REWRITE |(< (if a b c) x)|))
 (14984 28 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (12694 190 (:REWRITE THE-FLOOR-ABOVE))
 (7444 42 (:REWRITE |(+ y x)|))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4820 2 (:LINEAR LOGHEAD-LEQ))
 (4440 103 (:REWRITE DEFAULT-PLUS-1))
 (4430 103 (:REWRITE DEFAULT-PLUS-2))
 (4322 32 (:REWRITE NORMALIZE-ADDENDS))
 (2164 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1800 200 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1774 32 (:REWRITE FLOOR-ZERO . 3))
 (1696 32 (:REWRITE CANCEL-FLOOR-+))
 (1416 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1416 14 (:DEFINITION FIX))
 (1152 176 (:REWRITE DEFAULT-LESS-THAN-1))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (972 32 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (916 32 (:REWRITE FLOOR-ZERO . 5))
 (906 32 (:REWRITE FLOOR-ZERO . 4))
 (896 160 (:REWRITE INTEGERP-MINUS-X))
 (870 32 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (738 168 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (704 32 (:REWRITE FLOOR-=-X/Y . 2))
 (644 582 (:REWRITE DEFAULT-TIMES-2))
 (588 582 (:REWRITE DEFAULT-TIMES-1))
 (544 64 (:REWRITE |(* (- x) y)|))
 (438 39 (:REWRITE DEFAULT-FLOOR-RATIO))
 (364 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (320 64 (:REWRITE DEFAULT-MINUS))
 (308 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (298 298 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (288 64 (:REWRITE |(- (* c x))|))
 (266 154 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (266 154 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (200 200 (:TYPE-PRESCRIPTION FLOOR))
 (190 190 (:REWRITE THE-FLOOR-BELOW))
 (180 154 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (176 176 (:REWRITE DEFAULT-LESS-THAN-2))
 (160 32 (:REWRITE FLOOR-ZERO . 2))
 (160 32 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (160 32 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (158 154 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (154 154 (:REWRITE SIMPLIFY-SUMS-<))
 (154 154 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (154 154 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (154 154 (:REWRITE INTEGERP-<-CONSTANT))
 (154 154 (:REWRITE CONSTANT-<-INTEGERP))
 (154 154 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (154 154 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (154 154 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (154 154 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (154 154 (:REWRITE |(< c (- x))|))
 (154 154 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (154 154 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (154 154 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (154 154 (:REWRITE |(< (/ x) (/ y))|))
 (154 154 (:REWRITE |(< (- x) c)|))
 (154 154 (:REWRITE |(< (- x) (- y))|))
 (144 32 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (144 32 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (136 32 (:REWRITE FLOOR-CANCEL-*-CONST))
 (128 128 (:REWRITE REDUCE-INTEGERP-+))
 (128 128 (:META META-INTEGERP-CORRECT))
 (118 2 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
 (112 112 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (95 95 (:REWRITE |(< (* x y) 0)|))
 (87 87 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (87 87 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (87 87 (:REWRITE |(< (/ x) 0)|))
 (70 14 (:REWRITE |(+ 0 x)|))
 (66 66 (:TYPE-PRESCRIPTION ABS))
 (48 32 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (48 32 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (42 39 (:REWRITE DEFAULT-FLOOR-1))
 (39 39 (:REWRITE DEFAULT-FLOOR-2))
 (32 32 (:REWRITE |(floor x (- y))| . 2))
 (32 32 (:REWRITE |(floor x (- y))| . 1))
 (32 32 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 32 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (32 32 (:REWRITE |(floor (- x) y)| . 2))
 (32 32 (:REWRITE |(floor (- x) y)| . 1))
 (32 32 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (28 4 (:REWRITE |(* (if a b c) x)|))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< 0 (/ x))|))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE |(+ x (- x))|))
 (14 14 (:REWRITE |(* a (/ a) b)|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 )
(RISCV::GET-IMM-UTYPE)
(RISCV::UBYTE20P-OF-GET-IMM-UTYPE
 (30 2 (:DEFINITION UNSIGNED-BYTE-P))
 (27 2 (:DEFINITION INTEGER-RANGE-P))
 (26 1 (:REWRITE LOGHEAD-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (8 1 (:REWRITE LOGTAIL-IDENTITY))
 (6 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGER-RANGE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RISCV::GET-IMM-JTYPE)
(RISCV::UBYTE20P-OF-GET-IMM-JTYPE
 (29616 6 (:REWRITE LOGHEAD-IDENTITY))
 (17768 8 (:REWRITE |(< (if a b c) x)|))
 (14984 28 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (12694 190 (:REWRITE THE-FLOOR-ABOVE))
 (7444 42 (:REWRITE |(+ y x)|))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6196 6196 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4820 2 (:LINEAR LOGHEAD-LEQ))
 (4440 103 (:REWRITE DEFAULT-PLUS-1))
 (4430 103 (:REWRITE DEFAULT-PLUS-2))
 (4322 32 (:REWRITE NORMALIZE-ADDENDS))
 (2164 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (2052 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1800 200 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1774 32 (:REWRITE FLOOR-ZERO . 3))
 (1696 32 (:REWRITE CANCEL-FLOOR-+))
 (1416 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1416 14 (:DEFINITION FIX))
 (1152 176 (:REWRITE DEFAULT-LESS-THAN-1))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1140 228 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (972 32 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (916 32 (:REWRITE FLOOR-ZERO . 5))
 (906 32 (:REWRITE FLOOR-ZERO . 4))
 (896 160 (:REWRITE INTEGERP-MINUS-X))
 (870 32 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (738 168 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (728 728 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (704 32 (:REWRITE FLOOR-=-X/Y . 2))
 (644 582 (:REWRITE DEFAULT-TIMES-2))
 (588 582 (:REWRITE DEFAULT-TIMES-1))
 (544 64 (:REWRITE |(* (- x) y)|))
 (438 39 (:REWRITE DEFAULT-FLOOR-RATIO))
 (364 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (320 64 (:REWRITE DEFAULT-MINUS))
 (308 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (298 298 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (288 64 (:REWRITE |(- (* c x))|))
 (266 154 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (266 154 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (200 200 (:TYPE-PRESCRIPTION FLOOR))
 (190 190 (:REWRITE THE-FLOOR-BELOW))
 (180 154 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (176 176 (:REWRITE DEFAULT-LESS-THAN-2))
 (160 32 (:REWRITE FLOOR-ZERO . 2))
 (160 32 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (160 32 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (158 154 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (154 154 (:REWRITE SIMPLIFY-SUMS-<))
 (154 154 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (154 154 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (154 154 (:REWRITE INTEGERP-<-CONSTANT))
 (154 154 (:REWRITE CONSTANT-<-INTEGERP))
 (154 154 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (154 154 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (154 154 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (154 154 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (154 154 (:REWRITE |(< c (- x))|))
 (154 154 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (154 154 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (154 154 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (154 154 (:REWRITE |(< (/ x) (/ y))|))
 (154 154 (:REWRITE |(< (- x) c)|))
 (154 154 (:REWRITE |(< (- x) (- y))|))
 (144 32 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (144 32 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (136 32 (:REWRITE FLOOR-CANCEL-*-CONST))
 (128 128 (:REWRITE REDUCE-INTEGERP-+))
 (128 128 (:META META-INTEGERP-CORRECT))
 (118 2 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
 (112 112 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (95 95 (:REWRITE |(< (* x y) 0)|))
 (87 87 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (87 87 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (87 87 (:REWRITE |(< (/ x) 0)|))
 (70 14 (:REWRITE |(+ 0 x)|))
 (66 66 (:TYPE-PRESCRIPTION ABS))
 (48 32 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (48 32 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (42 39 (:REWRITE DEFAULT-FLOOR-1))
 (39 39 (:REWRITE DEFAULT-FLOOR-2))
 (32 32 (:REWRITE |(floor x (- y))| . 2))
 (32 32 (:REWRITE |(floor x (- y))| . 1))
 (32 32 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (32 32 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (32 32 (:REWRITE |(floor (- x) y)| . 2))
 (32 32 (:REWRITE |(floor (- x) y)| . 1))
 (32 32 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (28 4 (:REWRITE |(* (if a b c) x)|))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< 0 (/ x))|))
 (26 26 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE |(+ x (- x))|))
 (14 14 (:REWRITE |(* a (/ a) b)|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (2 2 (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 )
(RISCV::DECODE-RTYPE)
(RISCV::UBYTE3P-OF-DECODE-RTYPE.FUNCT3)
(RISCV::UBYTE7P-OF-DECODE-RTYPE.FUNCT7)
(RISCV::UBYTE5P-OF-DECODE-RTYPE.RD)
(RISCV::UBYTE5P-OF-DECODE-RTYPE.RS1)
(RISCV::UBYTE5P-OF-DECODE-RTYPE.RS2)
(RISCV::DECODE-ITYPE)
(RISCV::UBYTE3P-OF-DECODE-ITYPE.FUNCT3)
(RISCV::UBYTE5P-OF-DECODE-ITYPE.RD)
(RISCV::UBYTE5P-OF-DECODE-ITYPE.RS1)
(RISCV::UBYTE12P-OF-DECODE-ITYPE.IMM)
(RISCV::DECODE-STYPE)
(RISCV::UBYTE3P-OF-DECODE-STYPE.FUNCT3)
(RISCV::UBYTE5P-OF-DECODE-STYPE.RS1)
(RISCV::UBYTE5P-OF-DECODE-STYPE.RS2)
(RISCV::UBYTE12P-OF-DECODE-STYPE.IMM)
(RISCV::DECODE-BTYPE)
(RISCV::UBYTE3P-OF-DECODE-BTYPE.FUNCT3)
(RISCV::UBYTE5P-OF-DECODE-BTYPE.RS1)
(RISCV::UBYTE5P-OF-DECODE-BTYPE.RS2)
(RISCV::UBYTE12P-OF-DECODE-BTYPE.IMM)
(RISCV::DECODE-UTYPE)
(RISCV::UBYTE5P-OF-DECODE-UTYPE.RD)
(RISCV::UBYTE20P-OF-DECODE-UTYPE.IMM)
(RISCV::DECODE-JTYPE)
(RISCV::UBYTE5P-OF-DECODE-JTYPE.RD)
(RISCV::UBYTE20P-OF-DECODE-JTYPE.IMM)
(RISCV::DECODE
 (24 3 (:REWRITE LOGHEAD-IDENTITY))
 (18 3 (:DEFINITION UNSIGNED-BYTE-P))
 (15 3 (:DEFINITION INTEGER-RANGE-P))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(RISCV::INSTR-OPTIONP-OF-DECODE)
