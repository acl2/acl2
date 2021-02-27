(FM9001::TV-IF-BODY (46 26 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                    (46 26 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                    (46 26
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                    (46 26
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                    (26 26 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                    (26 26
                        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                    (26 26 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                    (26 26
                        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                    (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                    (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                    (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                    (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                    (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                    (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(FM9001::TV-IF*)
(FM9001::TV-IF*$DESTRUCTURE
     (4908 36 (:REWRITE TAKE-OF-TOO-MANY))
     (4626 18 (:DEFINITION TAKE))
     (3744 90 (:DEFINITION NFIX))
     (2676 36 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (2568 36 (:REWRITE TAKE-OF-LEN-FREE))
     (1998 54 (:REWRITE FM9001::LEN-SIS))
     (1674 18 (:DEFINITION NTHCDR))
     (1548 72 (:REWRITE |(equal (+ (- c) x) y)|))
     (1098 18 (:REWRITE |(< (+ (- c) x) y)|))
     (1074 174
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (936 936 (:TYPE-PRESCRIPTION LEN))
     (702 54 (:DEFINITION LEN))
     (486 252 (:REWRITE DEFAULT-PLUS-2))
     (396 6 (:REWRITE CANCEL-MOD-+))
     (360 360 (:LINEAR LEN-WHEN-PREFIXP))
     (348 174 (:REWRITE DEFAULT-LESS-THAN-1))
     (342 342
          (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (312 138
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (288 138
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (270 252 (:REWRITE DEFAULT-PLUS-1))
     (252 36 (:REWRITE TAKE-WHEN-ATOM))
     (240 6 (:REWRITE MOD-X-Y-=-X . 3))
     (234 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (232 106 (:REWRITE DEFAULT-CDR))
     (228 174 (:REWRITE DEFAULT-LESS-THAN-2))
     (216 72 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (216 72
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (216 36 (:REWRITE |(+ c (+ d x))|))
     (210 138 (:REWRITE SIMPLIFY-SUMS-<))
     (198 30 (:REWRITE INTEGERP-MINUS-X))
     (180 180 (:REWRITE THE-FLOOR-BELOW))
     (180 180 (:REWRITE THE-FLOOR-ABOVE))
     (174 174
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (174 174
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (168 72
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (162 162
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (162 162 (:REWRITE NORMALIZE-ADDENDS))
     (162 6 (:REWRITE MOD-ZERO . 3))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (156 156
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (156 138
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (138 138
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (138 138 (:REWRITE INTEGERP-<-CONSTANT))
     (138 138 (:REWRITE CONSTANT-<-INTEGERP))
     (138 138
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (138 138
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (138 138
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (138 138
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (138 138 (:REWRITE |(< c (- x))|))
     (138 138
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (138 138
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (138 138
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (138 138 (:REWRITE |(< (/ x) (/ y))|))
     (138 138 (:REWRITE |(< (- x) c)|))
     (138 138 (:REWRITE |(< (- x) (- y))|))
     (137 65 (:REWRITE DEFAULT-CAR))
     (132 132 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (132 6 (:DEFINITION BINARY-APPEND))
     (126 12 (:REWRITE |(* (- x) y)|))
     (108 108
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (108 108
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (108 18 (:REWRITE |(+ y x)|))
     (102 66 (:REWRITE DEFAULT-TIMES-2))
     (96 66 (:REWRITE DEFAULT-TIMES-1))
     (90 90 (:REWRITE |(< (* x y) 0)|))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (84 84 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (84 12 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (84 6 (:REWRITE DEFAULT-MOD-RATIO))
     (72 72 (:REWRITE FM9001::TREE-SIZE-ATOM))
     (72 72
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (72 72
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (72 72
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (72 72 (:REWRITE |(equal c (/ x))|))
     (72 72 (:REWRITE |(equal c (- x))|))
     (72 72 (:REWRITE |(equal (/ x) c)|))
     (72 72 (:REWRITE |(equal (/ x) (/ y))|))
     (72 72 (:REWRITE |(equal (- x) c)|))
     (72 72 (:REWRITE |(equal (- x) (- y))|))
     (72 72 (:REWRITE |(< (/ x) 0)|))
     (72 36 (:REWRITE |(+ 0 x)|))
     (72 12 (:REWRITE DEFAULT-MINUS))
     (66 12 (:REWRITE |(- (* c x))|))
     (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (60 12 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (60 12
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (60 12
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (48 6 (:REWRITE MOD-X-Y-=-X . 4))
     (42 6 (:REWRITE MOD-ZERO . 4))
     (42 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (42 6 (:REWRITE MOD-X-Y-=-X . 2))
     (42 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (42 6
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (36 36 (:TYPE-PRESCRIPTION NFIX))
     (36 36
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (36 36 (:REWRITE |(< (+ c/d x) y)|))
     (36 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (36 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (36 6
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (36 6 (:REWRITE MOD-CANCEL-*-CONST))
     (36 6
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:META META-INTEGERP-CORRECT))
     (18 18 (:REWRITE |(< y (+ (- c) x))|))
     (18 18 (:REWRITE |(< x (+ c/d y))|))
     (12 12 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (12 12
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (12 12 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (12 12
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (12 12 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (12 6 (:REWRITE DEFAULT-MOD-1))
     (6 6 (:REWRITE MOD-POSITIVE . 3))
     (6 6 (:REWRITE MOD-POSITIVE . 2))
     (6 6
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE DEFAULT-MOD-2))
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
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|)))
(FM9001::TV-IF&
     (67800 10
            (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
     (67770 10
            (:DEFINITION STR::ISTRPREFIXP$INLINE))
     (66760 70
            (:REWRITE STR::IPREFIXP-WHEN-PREFIXP))
     (50370 1120 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (45480 210 (:REWRITE PREFIXP-OF-CONS-LEFT))
     (44820 60
            (:REWRITE STR::IPREFIXP-OF-CONS-LEFT))
     (38960 1120
            (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (38110 560 (:REWRITE PREFIXP-OF-CONS-RIGHT))
     (11220 11220 (:TYPE-PRESCRIPTION LEN))
     (8800 1140 (:DEFINITION LEN))
     (8530 2117
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5847 1171 (:REWRITE ACL2-NUMBERP-X))
     (3854 2117
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3780 3780 (:LINEAR LEN-WHEN-PREFIXP))
     (2907 1396 (:REWRITE DEFAULT-PLUS-2))
     (2423 599 (:REWRITE RATIONALP-X))
     (2214 2004 (:REWRITE DEFAULT-CDR))
     (2144 2117 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2117 2117
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2117 2117
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2117 2117
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2117 2117 (:REWRITE |(equal c (/ x))|))
     (2117 2117 (:REWRITE |(equal c (- x))|))
     (2117 2117 (:REWRITE |(equal (/ x) c)|))
     (2117 2117 (:REWRITE |(equal (/ x) (/ y))|))
     (2117 2117 (:REWRITE |(equal (- x) c)|))
     (2117 2117 (:REWRITE |(equal (- x) (- y))|))
     (2100 40 (:DEFINITION INTEGER-ABS))
     (1960 190 (:REWRITE STR::CONSP-OF-EXPLODE))
     (1890 1890
           (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (1885 1396 (:REWRITE DEFAULT-PLUS-1))
     (1690 1690
           (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (1276 1276
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1190 1190 (:TYPE-PRESCRIPTION PREFIXP))
     (1180 560
           (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (1120 1120 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (1120 1120 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (1120 1120
           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (1120 1120
           (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (981 891 (:REWRITE DEFAULT-CAR))
     (700 20 (:REWRITE |(+ (if a b c) x)|))
     (620 620 (:REWRITE REDUCE-INTEGERP-+))
     (620 620 (:REWRITE INTEGERP-MINUS-X))
     (620 620 (:META META-INTEGERP-CORRECT))
     (620 20 (:REWRITE NUMERATOR-NEGATIVE))
     (599 599 (:REWRITE REDUCE-RATIONALP-+))
     (599 599 (:REWRITE REDUCE-RATIONALP-*))
     (599 599 (:REWRITE RATIONALP-MINUS-X))
     (599 599 (:META META-RATIONALP-CORRECT))
     (560 20 (:DEFINITION LENGTH))
     (370 60
          (:REWRITE STR::IPREFIXP-WHEN-NOT-CONSP-RIGHT))
     (350 350
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (196 81 (:REWRITE DEFAULT-LESS-THAN-1))
     (180 180 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (180 180
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (180 180
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (180 180
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (180 180
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (140 40 (:REWRITE DEFAULT-MINUS))
     (105 81
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (99 81 (:REWRITE DEFAULT-LESS-THAN-2))
     (94 61
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (94 61 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (81 81 (:REWRITE THE-FLOOR-BELOW))
     (81 81 (:REWRITE THE-FLOOR-ABOVE))
     (81 81 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (81 81
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (81 81
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (81 81
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (81 81 (:REWRITE INTEGERP-<-CONSTANT))
     (81 81 (:REWRITE CONSTANT-<-INTEGERP))
     (81 81
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (81 81
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (81 81
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (81 81
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (81 81 (:REWRITE |(< c (- x))|))
     (81 81
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (81 81
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (81 81
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (81 81
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (81 81 (:REWRITE |(< (/ x) (/ y))|))
     (81 81 (:REWRITE |(< (- x) c)|))
     (81 81 (:REWRITE |(< (- x) (- y))|))
     (80 80
         (:TYPE-PRESCRIPTION STR::ICHAREQV$INLINE))
     (70 70
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (60 60 (:REWRITE |(< (/ x) 0)|))
     (60 60 (:REWRITE |(< (* x y) 0)|))
     (54 18
         (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
     (46 46 (:REWRITE FOLD-CONSTS-IN-+))
     (46 46 (:REWRITE |(+ c (+ d x))|))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (40 20
         (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
     (36 36
         (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
     (30 30
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (20 20 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (20 20
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (20 20 (:REWRITE DEFAULT-REALPART))
     (20 20
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (20 20
         (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (20 20 (:REWRITE DEFAULT-IMAGPART))
     (12 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (10 10
         (:TYPE-PRESCRIPTION STR::ISTRPREFIXP$INLINE))
     (10 10 (:REWRITE DEFAULT-SYMBOL-NAME))
     (10 10 (:REWRITE |(< y (+ (- c) x))|))
     (10 10 (:REWRITE |(< x (+ c/d y))|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|)))
(FM9001::TV-IF$NETLIST (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
                       (2 2 (:REWRITE DEFAULT-CAR))
                       (1 1 (:REWRITE DEFAULT-CDR)))
(FM9001::TV-IF-INDUCTION)
(FM9001::CDR-APPEND-SINGLETON
     (756 378
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (378 378 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (378 378 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (314 16
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (232 24 (:REWRITE ACL2-NUMBERP-X))
     (106 16
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (104 8 (:REWRITE RATIONALP-X))
     (99 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (80 44 (:REWRITE DEFAULT-CDR))
     (34 17 (:REWRITE DEFAULT-PLUS-2))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (17 17 (:REWRITE DEFAULT-PLUS-1))
     (16 16
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (16 16 (:REWRITE DEFAULT-CAR))
     (16 16 (:REWRITE |(equal c (/ x))|))
     (16 16 (:REWRITE |(equal c (- x))|))
     (16 16 (:REWRITE |(equal (/ x) c)|))
     (16 16 (:REWRITE |(equal (/ x) (/ y))|))
     (16 16 (:REWRITE |(equal (- x) c)|))
     (16 16 (:REWRITE |(equal (- x) (- y))|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (12 12
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8 (:REWRITE REDUCE-RATIONALP-*))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE RATIONALP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:META META-RATIONALP-CORRECT))
     (8 8 (:META META-INTEGERP-CORRECT))
     (3 3 (:REWRITE CONSP-OF-APPEND))
     (3 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|)))
(FM9001::TV-IF$VALUE-AUX
     (884 4 (:DEFINITION TAKE))
     (646 8 (:REWRITE TAKE-OF-TOO-MANY))
     (570 15 (:REWRITE ZP-OPEN))
     (546 13 (:REWRITE CONSP-OF-TAKE))
     (524 8 (:DEFINITION PAIRLIS$))
     (380 14 (:REWRITE FM9001::DISJOINT-ATOM))
     (367 4
          (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-2))
     (312 17 (:DEFINITION ATOM))
     (278 8 (:REWRITE TAKE-OF-LEN-FREE))
     (256 4 (:DEFINITION NTHCDR))
     (238 4
          (:REWRITE FM9001::SINGLETON-ASSOC-EQ-VALUES))
     (203 29 (:DEFINITION LEN))
     (184 4 (:REWRITE |(< (+ (- c) x) y)|))
     (173 49
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (150 10 (:REWRITE |(equal (+ (- c) x) y)|))
     (140 4 (:REWRITE CAR-OF-TAKE))
     (129 43
          (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (111 66 (:REWRITE DEFAULT-PLUS-2))
     (108 1 (:REWRITE LEN-WHEN-PREFIXP))
     (102 4 (:REWRITE FM9001::DISJOINT-NTHCDR))
     (94 12
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (90 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (82 70 (:REWRITE DEFAULT-CDR))
     (81 49 (:REWRITE DEFAULT-LESS-THAN-2))
     (74 66 (:REWRITE DEFAULT-PLUS-1))
     (73 73 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (73 8 (:REWRITE FM9001::NTHCDR-OF-LEN-L))
     (66 40
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (66 40 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (66 4 (:REWRITE PREFIXP-WHEN-PREFIXP))
     (66 1
         (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-2))
     (63 6 (:DEFINITION TRUE-LISTP))
     (58 49 (:REWRITE NORMALIZE-ADDENDS))
     (56 49 (:REWRITE DEFAULT-LESS-THAN-1))
     (54 54 (:LINEAR LEN-WHEN-PREFIXP))
     (50 1 (:DEFINITION SUBSETP-EQUAL))
     (49 49 (:REWRITE THE-FLOOR-BELOW))
     (49 49 (:REWRITE THE-FLOOR-ABOVE))
     (49 49
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (48 48
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (48 2
         (:REWRITE FM9001::STRIP-CARS-PAIRLIS$))
     (46 40 (:REWRITE SIMPLIFY-SUMS-<))
     (45 12 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
     (41 41
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (41 41 (:REWRITE INTEGERP-<-CONSTANT))
     (41 41 (:REWRITE CONSTANT-<-INTEGERP))
     (41 41
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (41 41
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (41 41
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (41 41
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (41 41 (:REWRITE |(< c (- x))|))
     (41 41
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (41 41
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (41 41 (:REWRITE |(< (/ x) (/ y))|))
     (41 41 (:REWRITE |(< (- x) c)|))
     (41 41 (:REWRITE |(< (- x) (- y))|))
     (41 1 (:DEFINITION MEMBER-EQUAL))
     (40 7 (:DEFINITION BINARY-APPEND))
     (34 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (33 33 (:REWRITE DEFAULT-CAR))
     (32 6 (:REWRITE |(+ y x)|))
     (28 28 (:TYPE-PRESCRIPTION FM9001::BVP))
     (27 27
         (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
     (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
     (24 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 4 (:REWRITE TAKE-WHEN-PREFIXP))
     (24 1 (:REWRITE |(+ y (+ x z))|))
     (22 22 (:TYPE-PRESCRIPTION PAIRLIS$))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (22 22 (:REWRITE |(< 0 (* x y))|))
     (20 14 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (19 1
         (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-1))
     (16 16
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (16 4 (:REWRITE |(+ c (+ d x))|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (13 12 (:REWRITE |(equal (- x) c)|))
     (13 12 (:REWRITE |(equal (- x) (- y))|))
     (12 12
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (12 12 (:REWRITE |(equal c (/ x))|))
     (12 12 (:REWRITE |(equal c (- x))|))
     (12 12 (:REWRITE |(equal (/ x) c)|))
     (12 12 (:REWRITE |(equal (/ x) (/ y))|))
     (12 2 (:DEFINITION STRIP-CARS))
     (11 11 (:TYPE-PRESCRIPTION STRIP-CARS))
     (11 3 (:REWRITE ACL2-NUMBERP-X))
     (9 9 (:TYPE-PRESCRIPTION PREFIXP))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE TAKE-WHEN-ATOM))
     (8 8 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:TYPE-PRESCRIPTION ATOM))
     (6 5 (:REWRITE |(+ 0 x)|))
     (6 2
        (:TYPE-PRESCRIPTION FM9001::BVP-NTHCDR))
     (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (5 2 (:REWRITE FM9001::DISJOINT-TAKE))
     (4 4
        (:REWRITE FM9001::SUBSETP-TRANSITIVITY))
     (4 4
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (4 4
        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 2 (:REWRITE DEFAULT-MINUS))
     (4 2 (:DEFINITION FIX))
     (4 1 (:REWRITE RATIONALP-X))
     (4 1
        (:REWRITE FM9001::DISJOINT-NTHCDR-TAKE-OF-DISJOINT-LISTS))
     (3 1 (:REWRITE FM9001::BVP-NTHCDR))
     (2 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
     (1 1 (:REWRITE |(+ x (- x))|))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(FM9001::NOT-PRIMP-TV-IF
     (102 51
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (102 51
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (51 51 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (51 51
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (51 51
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (51 51
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (51 51 (:REWRITE |(equal c (/ x))|))
     (51 51 (:REWRITE |(equal c (- x))|))
     (51 51 (:REWRITE |(equal (/ x) c)|))
     (51 51 (:REWRITE |(equal (/ x) (/ y))|))
     (51 51 (:REWRITE |(equal (- x) c)|))
     (51 51 (:REWRITE |(equal (- x) (- y))|)))
(FM9001::TV-IF$VALUE
    (17446 671 (:DEFINITION FM9001::DELETE-TO-EQ))
    (8550 6235 (:REWRITE DEFAULT-CDR))
    (8246 21
          (:DEFINITION FM9001::TV-IF-INDUCTION))
    (5117 1744
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
    (4656 24 (:REWRITE LEN-OF-APPEND))
    (4548 1137
          (:REWRITE FM9001::SI-OF-DIFF-SYMBOLS-2))
    (3810 93 (:REWRITE CAR-OF-TAKE))
    (3782 1895 (:REWRITE DEFAULT-PLUS-2))
    (3522 932
          (:REWRITE FM9001::ASSOC-EQ-OF-NON-FN-NETLIST))
    (3483 223 (:DEFINITION BINARY-APPEND))
    (3385 1744
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
    (3202 1744 (:REWRITE SIMPLIFY-SUMS-EQUAL))
    (2958 1895 (:REWRITE DEFAULT-PLUS-1))
    (2396 652 (:REWRITE ACL2-NUMBERP-X))
    (2300 2300
          (:TYPE-PRESCRIPTION FM9001::NET-SYNTAX-OKP))
    (2179 1843 (:REWRITE NORMALIZE-ADDENDS))
    (1852 53 (:DEFINITION MEMBER-EQUAL))
    (1817 1817
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
    (1748 1748
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
    (1744 1744
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
    (1744 1744 (:REWRITE |(equal c (/ x))|))
    (1744 1744 (:REWRITE |(equal c (- x))|))
    (1744 1744 (:REWRITE |(equal (/ x) c)|))
    (1744 1744 (:REWRITE |(equal (/ x) (/ y))|))
    (1744 1744 (:REWRITE |(equal (- x) c)|))
    (1744 1744 (:REWRITE |(equal (- x) (- y))|))
    (1638 56 (:REWRITE TAKE-MORE-OF-TAKE-FEWER))
    (1624 56 (:REWRITE TAKE-FEWER-OF-TAKE-MORE))
    (1614 84 (:REWRITE FM9001::DISJOINT-ATOM))
    (1600 50
          (:REWRITE FM9001::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
    (1488 30
          (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-2))
    (1218 657
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
    (1146 657
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
    (1137 1137 (:REWRITE DEFAULT-SYMBOL-NAME))
    (1110 657 (:REWRITE DEFAULT-LESS-THAN-1))
    (872 218 (:REWRITE RATIONALP-X))
    (870 290
         (:REWRITE FM9001::NET-SYNTAX-OKP-DELETE-TO-EQ-NETLIST))
    (719 655 (:REWRITE SIMPLIFY-SUMS-<))
    (693 657 (:REWRITE DEFAULT-LESS-THAN-2))
    (660 660 (:REWRITE THE-FLOOR-BELOW))
    (660 660 (:REWRITE THE-FLOOR-ABOVE))
    (657 657
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
    (657 657
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
    (657 657
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
    (657 657
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
    (657 657 (:REWRITE INTEGERP-<-CONSTANT))
    (657 657 (:REWRITE CONSTANT-<-INTEGERP))
    (657 657
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
    (657 657
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
    (657 657
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
    (657 657
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
    (657 657 (:REWRITE |(< c (- x))|))
    (657 657
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
    (657 657
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
    (657 657
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
    (657 657
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
    (657 657 (:REWRITE |(< (/ x) (/ y))|))
    (657 657 (:REWRITE |(< (- x) c)|))
    (657 657 (:REWRITE |(< (- x) (- y))|))
    (644 644 (:LINEAR LEN-WHEN-PREFIXP))
    (640 640 (:REWRITE REMOVE-WEAK-INEQUALITIES))
    (632 632 (:TYPE-PRESCRIPTION FM9001::BVP))
    (632 268 (:REWRITE TAKE-WHEN-ATOM))
    (632 138 (:REWRITE FM9001::V-THREEFIX-BVP))
    (613 613
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
    (613 613
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
    (613 613 (:REWRITE |(< (/ x) 0)|))
    (613 613 (:REWRITE |(< (* x y) 0)|))
    (613 154
         (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
    (556 278 (:REWRITE CONSP-OF-TAKE))
    (540 540
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
    (540 540
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
    (540 540
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
    (472 472 (:TYPE-PRESCRIPTION PAIRLIS$))
    (402 134
         (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
    (378 178 (:REWRITE DEFAULT-MINUS))
    (323 239 (:REWRITE INTEGERP-MINUS-X))
    (283 55 (:REWRITE REPEAT-WHEN-ZP))
    (236 236 (:REWRITE REDUCE-INTEGERP-+))
    (236 236 (:META META-INTEGERP-CORRECT))
    (218 218 (:REWRITE REDUCE-RATIONALP-+))
    (218 218 (:REWRITE REDUCE-RATIONALP-*))
    (218 218 (:REWRITE RATIONALP-MINUS-X))
    (218 218 (:META META-RATIONALP-CORRECT))
    (198 3 (:REWRITE CANCEL-MOD-+))
    (192 24
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
    (144 24 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
    (123 69 (:REWRITE DEFAULT-TIMES-2))
    (120 24 (:REWRITE |(+ x x)|))
    (120 3 (:REWRITE MOD-X-Y-=-X . 3))
    (117 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
    (96 32
        (:TYPE-PRESCRIPTION FM9001::BVP-NTHCDR))
    (84 69 (:REWRITE DEFAULT-TIMES-1))
    (81 3 (:REWRITE MOD-ZERO . 3))
    (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
    (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
    (78 78 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
    (64 36 (:REWRITE CONSP-OF-REPEAT))
    (63 6 (:REWRITE |(* (- x) y)|))
    (60 20
        (:TYPE-PRESCRIPTION FM9001::BVP-TAKE))
    (54 54 (:TYPE-PRESCRIPTION ATOM))
    (54 54
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
    (52 28 (:DEFINITION FIX))
    (50 26 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
    (48 16 (:REWRITE FM9001::BVP-NTHCDR))
    (42 3 (:REWRITE DEFAULT-MOD-RATIO))
    (33 6 (:REWRITE |(- (* c x))|))
    (30 10 (:REWRITE FM9001::BVP-TAKE))
    (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
    (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
    (30 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
    (30 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
    (24 3 (:REWRITE MOD-X-Y-=-X . 4))
    (21 3 (:REWRITE MOD-ZERO . 4))
    (21 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
    (21 3 (:REWRITE MOD-X-Y-=-X . 2))
    (21 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
    (21 3
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
    (18 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
    (18 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
    (18 3
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
    (18 3 (:REWRITE MOD-CANCEL-*-CONST))
    (18 3
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
    (14 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
    (13 13 (:REWRITE |(equal (+ (- c) x) y)|))
    (12 12
        (:REWRITE FM9001::SUBSETP-TRANSITIVITY))
    (12 12 (:REWRITE |(equal x (if a b c))|))
    (10 10
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
    (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
    (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
    (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
    (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
    (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
    (6 3 (:REWRITE DEFAULT-MOD-1))
    (4 4
       (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
    (4 2 (:REWRITE FM9001::F-GATES=B-GATES))
    (3 3 (:REWRITE MOD-POSITIVE . 3))
    (3 3 (:REWRITE MOD-POSITIVE . 2))
    (3 3
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
    (3 3 (:REWRITE DEFAULT-MOD-2))
    (3 3 (:REWRITE |(mod x (- y))| . 3))
    (3 3 (:REWRITE |(mod x (- y))| . 2))
    (3 3 (:REWRITE |(mod x (- y))| . 1))
    (3 3
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
    (3 3
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
    (3 3 (:REWRITE |(mod (- x) y)| . 3))
    (3 3 (:REWRITE |(mod (- x) y)| . 2))
    (3 3 (:REWRITE |(mod (- x) y)| . 1))
    (3 3
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
    (2 2 (:TYPE-PRESCRIPTION ZP))
    (2 2 (:REWRITE |(< y (+ (- c) x))|))
    (2 2 (:REWRITE |(< x (+ c/d y))|))
    (2 2 (:REWRITE |(< 0 (/ x))|))
    (2 2 (:REWRITE |(< 0 (* x y))|))
    (2 2 (:REWRITE |(+ x (- x))|)))
