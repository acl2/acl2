(RTL::INPUT-CONSTRAINTS)
(RTL::OPA)
(RTL::OPB)
(RTL::FNUM)
(RTL::RIN)
(RTL::INPUT-CONSTRAINTS-LEMMA)
(RTL::DNP)
(RTL::FZP)
(RTL::RMODE)
(F)
(RTL::SIGNA)
(RTL::EXPA)
(RTL::MANA)
(RTL::CLASSA)
(RTL::FLAGS-A)
(RTL::SIGNB)
(RTL::EXPB)
(RTL::MANB)
(RTL::CLASSB)
(RTL::FLAGS-B)
(RTL::SIGN)
(RTL::DATA-SPECIAL)
(RTL::FLAGS-SPECIAL)
(RTL::DIVPOW2)
(RTL::SIGA)
(RTL::SIGB)
(RTL::EXPDIFF)
(RTL::DIV)
(RTL::RP-1)
(RTL::RN-1)
(RTL::EXPQ)
(RTL::Q-1)
(N)
(RTL::RP-3N1)
(RTL::RN-3N1)
(RTL::QP-3N1)
(RTL::QN-3N1)
(RTL::QINC)
(RTL::QTRUNC)
(RTL::STK)
(RTL::QRND)
(RTL::INX)
(RTL::QRNDDEN)
(RTL::INXDEN)
(RTL::DATA-FINAL)
(RTL::FLAGS-FINAL)
(RTL::DATA)
(RTL::FLAGS)
(RTL::FDIV64-LEMMA)
(Q (1156 1156
         (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
   (1156 1156
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (1156 1156
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (1156 1156
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
   (790 158 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
   (790 158 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
   (750 158 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
   (750 158
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
   (750 158
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
   (750 25 (:REWRITE MOD-X-Y-=-X-Y . 2))
   (725 25 (:REWRITE MOD-X-Y-=-X . 3))
   (625 25 (:REWRITE RTL::MOD-DOES-NOTHING))
   (550 25 (:REWRITE MOD-ZERO . 3))
   (275 25 (:REWRITE DEFAULT-MOD-RATIO))
   (228 57 (:REWRITE |(* y x)|))
   (175 15
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
   (175 15 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
   (160 5 (:REWRITE MOD-X-Y-=-X-Y . 1))
   (158 158 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
   (158 158
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
   (158 158
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
   (158 158
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
   (158 158 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
   (151 151 (:REWRITE DEFAULT-TIMES-2))
   (151 151 (:REWRITE DEFAULT-TIMES-1))
   (125 111 (:REWRITE DEFAULT-PLUS-1))
   (125 25 (:REWRITE MOD-ZERO . 4))
   (125 25 (:REWRITE MOD-X-Y-=-X-Y . 3))
   (125 25 (:REWRITE MOD-X-Y-=-X+Y . 3))
   (125 25 (:REWRITE MOD-X-Y-=-X+Y . 2))
   (125 25 (:REWRITE MOD-X-Y-=-X . 4))
   (125 25 (:REWRITE MOD-X-Y-=-X . 2))
   (125 25
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
   (125 25
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
   (121 22
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
   (111 111 (:REWRITE DEFAULT-PLUS-2))
   (110 5 (:LINEAR MOD-BOUNDS-3))
   (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
   (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
   (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
   (89 89 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
   (83 83 (:REWRITE THE-FLOOR-BELOW))
   (83 83 (:REWRITE THE-FLOOR-ABOVE))
   (83 83
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
   (83 83
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
   (83 83
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
   (83 83
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
   (83 83 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
   (83 83 (:REWRITE INTEGERP-<-CONSTANT))
   (83 83 (:REWRITE DEFAULT-LESS-THAN-2))
   (83 83 (:REWRITE DEFAULT-LESS-THAN-1))
   (83 83 (:REWRITE CONSTANT-<-INTEGERP))
   (83 83
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
   (83 83
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
   (83 83
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
   (83 83
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
   (83 83 (:REWRITE |(< c (- x))|))
   (83 83
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
   (83 83
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
   (83 83
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
   (83 83
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
   (83 83 (:REWRITE |(< (/ x) (/ y))|))
   (83 83 (:REWRITE |(< (- x) c)|))
   (83 83 (:REWRITE |(< (- x) (- y))|))
   (78 78
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
   (57 5 (:REWRITE MOD-X-Y-=-X+Y . 1))
   (52 2 (:REWRITE MOD-ZERO . 1))
   (50 10 (:LINEAR MOD-BOUNDS-2))
   (33 33 (:REWRITE REMOVE-WEAK-INEQUALITIES))
   (33 33 (:REWRITE REDUCE-INTEGERP-+))
   (33 33 (:REWRITE INTEGERP-MINUS-X))
   (33 33 (:META META-INTEGERP-CORRECT))
   (32 32
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
   (25 25
       (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
   (25 25
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
   (25 25 (:REWRITE DEFAULT-MOD-2))
   (25 25 (:REWRITE DEFAULT-MOD-1))
   (25 25 (:REWRITE |(mod x (- y))| . 3))
   (25 25 (:REWRITE |(mod x (- y))| . 2))
   (25 25 (:REWRITE |(mod x (- y))| . 1))
   (25 25
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
   (25 25
       (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
   (25 25
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
   (22 22
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
   (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
   (15 15
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
   (15 15 (:REWRITE |(equal c (/ x))|))
   (15 15 (:REWRITE |(equal c (- x))|))
   (15 15 (:REWRITE |(equal (/ x) c)|))
   (15 15 (:REWRITE |(equal (/ x) (/ y))|))
   (15 15 (:REWRITE |(equal (- x) c)|))
   (15 15 (:REWRITE |(equal (- x) (- y))|))
   (14 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
   (11 11 (:TYPE-PRESCRIPTION NATP))
   (10 2 (:REWRITE MOD-ZERO . 2))
   (7 7 (:REWRITE ZP-OPEN))
   (6 6 (:REWRITE |(< (+ c/d x) y)|))
   (6 6 (:REWRITE |(< (+ (- c) x) y)|))
   (5 5
      (:REWRITE |(equal (mod (+ x y) z) x)|))
   (5 5 (:REWRITE |(+ 0 x)|))
   (5 5 (:LINEAR RTL::MOD-BND-3))
   (4 4 (:REWRITE |(< y (+ (- c) x))|))
   (4 4 (:REWRITE |(< x (+ c/d y))|))
   (2 2
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
   (1 1
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
   (1 1
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
   (1 1 (:REWRITE |(< (/ x) 0)|))
   (1 1 (:REWRITE |(< (* x y) 0)|)))
(RTL::FDIV64-LOOP-0-SUBLEMMA
     (4729 299 (:REWRITE DEFAULT-MOD-RATIO))
     (3812 413 (:REWRITE |(* y x)|))
     (3406 291 (:REWRITE MOD-ZERO . 3))
     (3096 3096
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3096 3096
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (2471 291 (:REWRITE MOD-X-Y-=-X . 4))
     (2160 180 (:REWRITE |(* x (+ y z))|))
     (1905 1173 (:REWRITE DEFAULT-PLUS-2))
     (1495 299 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (1475 295 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (1475 295 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (1430 286 (:REWRITE MOD-X-Y-=-X . 2))
     (1430 286
           (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1430 286
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (1173 1173 (:REWRITE DEFAULT-PLUS-1))
     (1006 1006 (:REWRITE DEFAULT-TIMES-2))
     (1006 1006 (:REWRITE DEFAULT-TIMES-1))
     (716 716
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (716 716
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (716 716
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (716 716
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (596 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (596 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (593 593
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (486 486
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (486 486 (:REWRITE NORMALIZE-ADDENDS))
     (401 201 (:REWRITE RTL::MOD-DOES-NOTHING))
     (299 299 (:REWRITE DEFAULT-MOD-2))
     (299 299 (:REWRITE DEFAULT-MOD-1))
     (286 286
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (286 286 (:REWRITE |(mod x (- y))| . 3))
     (286 286 (:REWRITE |(mod x (- y))| . 2))
     (286 286 (:REWRITE |(mod x (- y))| . 1))
     (286 286
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (286 286
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (286 286
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (233 233 (:REWRITE THE-FLOOR-BELOW))
     (233 233 (:REWRITE THE-FLOOR-ABOVE))
     (233 233 (:REWRITE SIMPLIFY-SUMS-<))
     (233 233
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (233 233
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (233 233
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (233 233
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (233 233
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (233 233 (:REWRITE INTEGERP-<-CONSTANT))
     (233 233 (:REWRITE DEFAULT-LESS-THAN-2))
     (233 233 (:REWRITE DEFAULT-LESS-THAN-1))
     (233 233 (:REWRITE CONSTANT-<-INTEGERP))
     (233 233
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (233 233
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (233 233
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (233 233
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (233 233 (:REWRITE |(< c (- x))|))
     (233 233
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (233 233
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (233 233
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (233 233
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (233 233 (:REWRITE |(< (/ x) (/ y))|))
     (233 233 (:REWRITE |(< (- x) c)|))
     (233 233 (:REWRITE |(< (- x) (- y))|))
     (201 201
          (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (198 105
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (166 166 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (141 107
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (140 140 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (140 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (140 140 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (136 68 (:TYPE-PRESCRIPTION RTL::NATP-MOD))
     (134 105
          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (130 26
          (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
     (130 4 (:LINEAR MOD-BOUNDS-3))
     (126 60
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (117 117 (:REWRITE REDUCE-INTEGERP-+))
     (117 117 (:REWRITE INTEGERP-MINUS-X))
     (117 117 (:META META-INTEGERP-CORRECT))
     (112 112 (:REWRITE |(< (+ c/d x) y)|))
     (112 112 (:REWRITE |(< (+ (- c) x) y)|))
     (107 107
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (107 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
     (106 105 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (105 105
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (105 105 (:REWRITE |(equal c (/ x))|))
     (105 105 (:REWRITE |(equal c (- x))|))
     (105 105 (:REWRITE |(equal (/ x) c)|))
     (105 105 (:REWRITE |(equal (/ x) (/ y))|))
     (105 105 (:REWRITE |(equal (- x) c)|))
     (105 105 (:REWRITE |(equal (- x) (- y))|))
     (68 68 (:TYPE-PRESCRIPTION RTL::NATP-MOD-2))
     (68 68 (:TYPE-PRESCRIPTION NATP))
     (68 68
         (:TYPE-PRESCRIPTION RTL::INTEGERP-MOD))
     (57 57
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (53 53
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (52 52 (:REWRITE |(< 0 (/ x))|))
     (52 52 (:REWRITE |(< 0 (* x y))|))
     (46 46 (:REWRITE |(equal (+ (- c) x) y)|))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (40 1 (:REWRITE MOD-ZERO . 1))
     (26 26
         (:TYPE-PRESCRIPTION RTL::RATIONALP-MOD))
     (26 26 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (26 26
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
     (26 26
         (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
     (5 1 (:REWRITE MOD-ZERO . 2))
     (4 4 (:LINEAR RTL::MOD-BND-3))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE |(equal (mod (+ x y) z) x)|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::FDIV64-LOOP-0-LEMMA
     (144 114 (:REWRITE DEFAULT-PLUS-2))
     (140 86 (:REWRITE DEFAULT-TIMES-2))
     (114 114 (:REWRITE DEFAULT-PLUS-1))
     (86 86 (:REWRITE DEFAULT-TIMES-1))
     (85 85
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (85 85 (:REWRITE NORMALIZE-ADDENDS))
     (68 68
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (65 16
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (65 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (59 3 (:REWRITE DEFAULT-MOD-RATIO))
     (50 10 (:REWRITE ACL2-NUMBERP-X))
     (39 23 (:REWRITE SIMPLIFY-SUMS-<))
     (39 23
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (37 23 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (35 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (32 1 (:REWRITE MOD-X-Y-=-X . 3))
     (30 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (30 2 (:REWRITE |(+ (+ x y) z)|))
     (27 23 (:REWRITE DEFAULT-LESS-THAN-1))
     (27 3 (:REWRITE MOD-ZERO . 4))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (25 23
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (25 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (24 23
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (24 23
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (23 23 (:REWRITE INTEGERP-<-CONSTANT))
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
     (22 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 2 (:REWRITE |(* y (* x z))|))
     (20 5 (:REWRITE RATIONALP-X))
     (17 16
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
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:REWRITE INTEGERP-MINUS-X))
     (10 10 (:META META-INTEGERP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (5 1 (:REWRITE MOD-X-Y-=-X . 4))
     (5 1 (:REWRITE MOD-X-Y-=-X . 2))
     (5 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:TYPE-PRESCRIPTION ABS))
     (3 3 (:REWRITE DEFAULT-MOD-2))
     (3 3 (:REWRITE DEFAULT-MOD-1))
     (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(RTL::FNUM-VALS)
(RTL::RP-3N1-REWRITE (600 120
                          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (426 66 (:REWRITE ACL2-NUMBERP-X))
                     (285 120
                          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (180 45 (:REWRITE RATIONALP-X))
                     (159 120 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (120 120 (:REWRITE |(equal c (/ x))|))
                     (120 120 (:REWRITE |(equal c (- x))|))
                     (120 120 (:REWRITE |(equal (/ x) c)|))
                     (120 120 (:REWRITE |(equal (/ x) (/ y))|))
                     (120 120 (:REWRITE |(equal (- x) c)|))
                     (120 120 (:REWRITE |(equal (- x) (- y))|))
                     (108 54 (:REWRITE DEFAULT-PLUS-2))
                     (90 90 (:TYPE-PRESCRIPTION BOOLEANP))
                     (63 9 (:REWRITE DEFAULT-MOD-RATIO))
                     (54 54 (:REWRITE DEFAULT-PLUS-1))
                     (45 45 (:REWRITE REDUCE-RATIONALP-+))
                     (45 45 (:REWRITE REDUCE-RATIONALP-*))
                     (45 45 (:REWRITE REDUCE-INTEGERP-+))
                     (45 45 (:REWRITE RATIONALP-MINUS-X))
                     (45 45 (:REWRITE INTEGERP-MINUS-X))
                     (45 45 (:META META-RATIONALP-CORRECT))
                     (45 45 (:META META-INTEGERP-CORRECT))
                     (39 24 (:REWRITE DEFAULT-TIMES-2))
                     (38 38
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (33 24 (:REWRITE DEFAULT-TIMES-1))
                     (18 9 (:REWRITE DEFAULT-MOD-1))
                     (18 9 (:REWRITE |(mod (if a b c) x)|))
                     (18 9 (:REWRITE |(* (if a b c) x)|))
                     (9 9 (:REWRITE DEFAULT-MOD-2))
                     (6 3 (:REWRITE DEFAULT-LESS-THAN-1))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 3))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
                     (3 3 (:REWRITE THE-FLOOR-BELOW))
                     (3 3 (:REWRITE THE-FLOOR-ABOVE))
                     (3 3 (:REWRITE DEFAULT-LESS-THAN-2)))
(RTL::RN-3N1-REWRITE (600 120
                          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (426 66 (:REWRITE ACL2-NUMBERP-X))
                     (285 120
                          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (180 45 (:REWRITE RATIONALP-X))
                     (159 120 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (120 120 (:REWRITE |(equal c (/ x))|))
                     (120 120 (:REWRITE |(equal c (- x))|))
                     (120 120 (:REWRITE |(equal (/ x) c)|))
                     (120 120 (:REWRITE |(equal (/ x) (/ y))|))
                     (120 120 (:REWRITE |(equal (- x) c)|))
                     (120 120 (:REWRITE |(equal (- x) (- y))|))
                     (108 54 (:REWRITE DEFAULT-PLUS-2))
                     (90 90 (:TYPE-PRESCRIPTION BOOLEANP))
                     (63 9 (:REWRITE DEFAULT-MOD-RATIO))
                     (54 54 (:REWRITE DEFAULT-PLUS-1))
                     (45 45 (:REWRITE REDUCE-RATIONALP-+))
                     (45 45 (:REWRITE REDUCE-RATIONALP-*))
                     (45 45 (:REWRITE REDUCE-INTEGERP-+))
                     (45 45 (:REWRITE RATIONALP-MINUS-X))
                     (45 45 (:REWRITE INTEGERP-MINUS-X))
                     (45 45 (:META META-RATIONALP-CORRECT))
                     (45 45 (:META META-INTEGERP-CORRECT))
                     (39 24 (:REWRITE DEFAULT-TIMES-2))
                     (38 38
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (33 24 (:REWRITE DEFAULT-TIMES-1))
                     (18 9 (:REWRITE DEFAULT-MOD-1))
                     (18 9 (:REWRITE |(mod (if a b c) x)|))
                     (18 9 (:REWRITE |(* (if a b c) x)|))
                     (9 9 (:REWRITE DEFAULT-MOD-2))
                     (6 3 (:REWRITE DEFAULT-LESS-THAN-1))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 3))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
                     (3 3 (:REWRITE THE-FLOOR-BELOW))
                     (3 3 (:REWRITE THE-FLOOR-ABOVE))
                     (3 3 (:REWRITE DEFAULT-LESS-THAN-2)))
(RTL::QP-3N1-REWRITE (600 120
                          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (414 54 (:REWRITE ACL2-NUMBERP-X))
                     (285 120
                          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (180 45 (:REWRITE RATIONALP-X))
                     (147 120 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (120 120 (:REWRITE |(equal c (/ x))|))
                     (120 120 (:REWRITE |(equal c (- x))|))
                     (120 120 (:REWRITE |(equal (/ x) c)|))
                     (120 120 (:REWRITE |(equal (/ x) (/ y))|))
                     (120 120 (:REWRITE |(equal (- x) c)|))
                     (120 120 (:REWRITE |(equal (- x) (- y))|))
                     (108 54 (:REWRITE DEFAULT-PLUS-2))
                     (90 90 (:TYPE-PRESCRIPTION BOOLEANP))
                     (63 9 (:REWRITE DEFAULT-MOD-RATIO))
                     (54 54 (:REWRITE DEFAULT-PLUS-1))
                     (50 50
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (45 45 (:REWRITE REDUCE-RATIONALP-+))
                     (45 45 (:REWRITE REDUCE-RATIONALP-*))
                     (45 45 (:REWRITE REDUCE-INTEGERP-+))
                     (45 45 (:REWRITE RATIONALP-MINUS-X))
                     (45 45 (:REWRITE INTEGERP-MINUS-X))
                     (45 45 (:META META-RATIONALP-CORRECT))
                     (45 45 (:META META-INTEGERP-CORRECT))
                     (39 24 (:REWRITE DEFAULT-TIMES-2))
                     (33 24 (:REWRITE DEFAULT-TIMES-1))
                     (18 9 (:REWRITE DEFAULT-MOD-1))
                     (18 9 (:REWRITE |(mod (if a b c) x)|))
                     (18 9 (:REWRITE |(* (if a b c) x)|))
                     (9 9 (:REWRITE DEFAULT-MOD-2))
                     (6 3 (:REWRITE DEFAULT-LESS-THAN-1))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 3))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
                     (3 3 (:REWRITE THE-FLOOR-BELOW))
                     (3 3 (:REWRITE THE-FLOOR-ABOVE))
                     (3 3 (:REWRITE DEFAULT-LESS-THAN-2)))
(RTL::QN-3N1-REWRITE (600 120
                          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (414 54 (:REWRITE ACL2-NUMBERP-X))
                     (285 120
                          (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                     (180 45 (:REWRITE RATIONALP-X))
                     (147 120 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                     (120 120
                          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                     (120 120 (:REWRITE |(equal c (/ x))|))
                     (120 120 (:REWRITE |(equal c (- x))|))
                     (120 120 (:REWRITE |(equal (/ x) c)|))
                     (120 120 (:REWRITE |(equal (/ x) (/ y))|))
                     (120 120 (:REWRITE |(equal (- x) c)|))
                     (120 120 (:REWRITE |(equal (- x) (- y))|))
                     (108 54 (:REWRITE DEFAULT-PLUS-2))
                     (90 90 (:TYPE-PRESCRIPTION BOOLEANP))
                     (63 9 (:REWRITE DEFAULT-MOD-RATIO))
                     (54 54 (:REWRITE DEFAULT-PLUS-1))
                     (50 50
                         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                     (45 45 (:REWRITE REDUCE-RATIONALP-+))
                     (45 45 (:REWRITE REDUCE-RATIONALP-*))
                     (45 45 (:REWRITE REDUCE-INTEGERP-+))
                     (45 45 (:REWRITE RATIONALP-MINUS-X))
                     (45 45 (:REWRITE INTEGERP-MINUS-X))
                     (45 45 (:META META-RATIONALP-CORRECT))
                     (45 45 (:META META-INTEGERP-CORRECT))
                     (39 24 (:REWRITE DEFAULT-TIMES-2))
                     (33 24 (:REWRITE DEFAULT-TIMES-1))
                     (18 9 (:REWRITE DEFAULT-MOD-1))
                     (18 9 (:REWRITE |(mod (if a b c) x)|))
                     (18 9 (:REWRITE |(* (if a b c) x)|))
                     (9 9 (:REWRITE DEFAULT-MOD-2))
                     (6 3 (:REWRITE DEFAULT-LESS-THAN-1))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 3))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
                     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
                     (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
                     (3 3 (:REWRITE THE-FLOOR-BELOW))
                     (3 3 (:REWRITE THE-FLOOR-ABOVE))
                     (3 3 (:REWRITE DEFAULT-LESS-THAN-2)))
