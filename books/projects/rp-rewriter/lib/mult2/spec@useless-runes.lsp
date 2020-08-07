(RP::MULT-SIMPLE-SPEC-AUX)
(RP::INTEGERP-OF-MULT-SIMPLE-SPEC-AUX
     (160 10
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (89 89
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (70 64 (:REWRITE DEFAULT-*-2))
     (70 64 (:REWRITE DEFAULT-*-1))
     (68 50 (:REWRITE DEFAULT-+-2))
     (52 50 (:REWRITE DEFAULT-+-1))
     (30 10 (:DEFINITION NFIX))
     (28 28 (:REWRITE DEFAULT-<-2))
     (28 28 (:REWRITE DEFAULT-<-1))
     (25 20 (:REWRITE DEFAULT-UNARY-MINUS))
     (17 17 (:REWRITE DEFAULT-NUMERATOR))
     (17 17 (:REWRITE DEFAULT-DENOMINATOR))
     (13 13 (:REWRITE ZP-OPEN)))
(RP::MULT-SIMPLE-SPEC-IS-*
     (5759 5755
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (5759 5755
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (5757 5753
           (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (4273 129 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (3805 129 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (2164 2164
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
     (1861 377 (:REWRITE DEFAULT-DIVIDE))
     (1790 166 (:LINEAR MOD-BOUNDS-2))
     (1686 814
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1641 329 (:REWRITE DEFAULT-MOD-2))
     (1566 294 (:REWRITE MOD-CANCEL-*-CONST))
     (1565 1565
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1565 1565
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1535 897 (:REWRITE DEFAULT-LESS-THAN-1))
     (1432 68 (:REWRITE ZP-OPEN))
     (1431 281
           (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1431 281
           (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (1360 128 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (1257 819
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1194 18
           (:REWRITE |(equal (mod a n) (mod b n))|))
     (1096 129 (:REWRITE FLOOR-=-X/Y . 2))
     (1093 897 (:REWRITE DEFAULT-LESS-THAN-2))
     (1081 1081
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1074 38 (:LINEAR EXPT-X->=-X))
     (1074 38 (:LINEAR EXPT-X->-X))
     (920 60
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (914 895
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (914 895
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (907 819
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (897 897 (:REWRITE THE-FLOOR-BELOW))
     (819 819 (:REWRITE INTEGERP-<-CONSTANT))
     (819 819 (:REWRITE CONSTANT-<-INTEGERP))
     (819 819
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (819 819
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (819 819
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (819 819
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (819 819 (:REWRITE |(< c (- x))|))
     (819 819
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (819 819
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (819 819
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (819 819 (:REWRITE |(< (/ x) (/ y))|))
     (819 819 (:REWRITE |(< (- x) c)|))
     (819 819 (:REWRITE |(< (- x) (- y))|))
     (813 813 (:REWRITE DEFAULT-EXPT-2))
     (813 813 (:REWRITE DEFAULT-EXPT-1))
     (813 813 (:REWRITE |(expt 1/c n)|))
     (813 813 (:REWRITE |(expt (- x) n)|))
     (757 307 (:REWRITE |(floor x 2)| . 2))
     (744 744
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (650 38 (:LINEAR EXPT-<=-1-TWO))
     (580 460
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (580 460
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (559 329 (:REWRITE DEFAULT-MOD-1))
     (537 129 (:REWRITE FLOOR-CANCEL-*-CONST))
     (466 402 (:REWRITE DEFAULT-FLOOR-1))
     (464 464 (:REWRITE |(< (* x y) 0)|))
     (462 462 (:REWRITE |(< (/ x) 0)|))
     (460 460
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
     (460 460
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
     (460 460
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
     (460 460
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
     (441 437 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (402 402 (:REWRITE DEFAULT-FLOOR-2))
     (395 383 (:REWRITE |(- (* c x))|))
     (350 338 (:REWRITE |(* c (* d x))|))
     (288 96 (:REWRITE |(* 1/2 (floor x y))| . 3))
     (288 96 (:REWRITE |(* 1/2 (floor x y))| . 2))
     (281 281
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (281 281 (:REWRITE |(mod x (- y))| . 3))
     (281 281 (:REWRITE |(mod x (- y))| . 2))
     (281 281 (:REWRITE |(mod x (- y))| . 1))
     (281 281
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (281 281 (:REWRITE |(mod (- x) y)| . 3))
     (281 281 (:REWRITE |(mod (- x) y)| . 2))
     (281 281 (:REWRITE |(mod (- x) y)| . 1))
     (281 281
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (205 205
          (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (192 192
          (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
     (176 35
          (:REWRITE |(equal (mod (+ x y) z) x)|))
     (170 10 (:REWRITE |(* (- c) (expt d n))|))
     (161 129 (:REWRITE FLOOR-ZERO . 2))
     (161 129 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (161 129 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (157 125
          (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (157 125
          (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (138 58 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
     (125 125
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (125 125 (:REWRITE |(floor x (- y))| . 2))
     (125 125 (:REWRITE |(floor x (- y))| . 1))
     (125 125
          (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (125 125
          (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (125 125 (:REWRITE |(floor (- x) y)| . 2))
     (125 125 (:REWRITE |(floor (- x) y)| . 1))
     (125 125
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (124 64 (:REWRITE |(equal (/ x) c)|))
     (120 120 (:REWRITE |(< x (+ c/d y))|))
     (114 6 (:REWRITE |(* (- (/ c)) (expt d n))|))
     (108 108 (:REWRITE |(< 0 (* x y))|))
     (76 76
         (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (76 76
         (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (76 76
         (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (76 76
         (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (76 2 (:REWRITE MOD-ZERO . 1))
     (72 64 (:REWRITE |(equal (- x) (- y))|))
     (70 70 (:REWRITE |(< 0 (/ x))|))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (68 68
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (64 64 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
     (64 64
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (64 64
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (64 64 (:REWRITE |(equal c (/ x))|))
     (64 64 (:REWRITE |(equal (/ x) (/ y))|))
     (64 64 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (64 64 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (60 60
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (60 60 (:REWRITE |(equal c (- x))|))
     (60 60 (:REWRITE |(equal (- x) c)|))
     (50 50 (:REWRITE |(< (+ c/d x) y)|))
     (48 48 (:REWRITE |(< y (+ (- c) x))|))
     (48 48 (:REWRITE |(< (+ (- c) x) y)|))
     (40 40
         (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (40 20 (:REWRITE O-INFP->NEQ-0))
     (38 38 (:TYPE-PRESCRIPTION ABS))
     (38 38 (:LINEAR EXPT-LINEAR-UPPER-<=))
     (38 38 (:LINEAR EXPT-LINEAR-UPPER-<))
     (38 38 (:LINEAR EXPT-LINEAR-LOWER-<=))
     (38 38 (:LINEAR EXPT-LINEAR-LOWER-<))
     (38 38 (:LINEAR EXPT->=-1-TWO))
     (38 38 (:LINEAR EXPT->-1-TWO))
     (38 38 (:LINEAR EXPT-<=-1-ONE))
     (38 38 (:LINEAR EXPT-<-1-TWO))
     (38 38 (:LINEAR EXPT-<-1-ONE))
     (32 32 (:REWRITE FLOOR-NEGATIVE . 4))
     (32 32 (:REWRITE FLOOR-NEGATIVE . 3))
     (32 32 (:REWRITE FLOOR-NEGATIVE . 2))
     (32 32 (:REWRITE FLOOR-NEGATIVE . 1))
     (32 32
         (:REWRITE |(floor (floor x y) z)| . 5))
     (32 32
         (:REWRITE |(floor (floor x y) z)| . 4))
     (32 32
         (:REWRITE |(floor (floor x y) z)| . 3))
     (32 32
         (:REWRITE |(floor (floor x y) z)| . 2))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (18 2 (:REWRITE MOD-ZERO . 2))
     (17 17 (:REWRITE |(equal (+ (- c) x) y)|))
     (11 11 (:REWRITE |(* 2 (floor x y))| . 2))
     (8 4 (:REWRITE |(+ (* c x) (* d x))|))
     (5 5 (:REWRITE FOLD-CONSTS-IN-+))
     (5 1 (:REWRITE |(- (if a b c))|))
     (4 4 (:REWRITE |(not (equal x (/ y)))|))
     (4 4 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(/ (/ x))|))
     (3 3
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
     (3 3
        (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RP::CREATE-PPS)
(RP::INTEGER-LISTP-OF-CREATE-PPS
     (224 14
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (135 135
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (113 92 (:REWRITE DEFAULT-+-2))
     (101 83 (:REWRITE DEFAULT-*-2))
     (95 92 (:REWRITE DEFAULT-+-1))
     (95 83 (:REWRITE DEFAULT-*-1))
     (76 76 (:REWRITE DEFAULT-<-2))
     (76 76 (:REWRITE DEFAULT-<-1))
     (42 14 (:DEFINITION NFIX))
     (39 3 (:DEFINITION EXPT))
     (36 33 (:REWRITE DEFAULT-CDR))
     (36 33 (:REWRITE DEFAULT-CAR))
     (35 28 (:REWRITE DEFAULT-UNARY-MINUS))
     (25 25 (:REWRITE DEFAULT-NUMERATOR))
     (25 25 (:REWRITE DEFAULT-DENOMINATOR))
     (13 13 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE ZIP-OPEN)))
(RP::SUM-PPS-BY-ROW (257 3
                         (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                    (255 1 (:DEFINITION APPLY$-BADGEP))
                    (177 1 (:DEFINITION SUBSETP-EQUAL))
                    (164 14 (:DEFINITION MEMBER-EQUAL))
                    (102 7
                         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                    (96 96 (:REWRITE DEFAULT-CDR))
                    (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                    (30 30 (:REWRITE DEFAULT-CAR))
                    (21 21
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                    (20 2 (:DEFINITION NATP))
                    (14 14
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                    (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                    (9 1 (:DEFINITION RP::SUM-PPS-BY-ROW))
                    (7 7 (:TYPE-PRESCRIPTION LEN))
                    (7 1 (:DEFINITION LEN))
                    (6 3
                       (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                    (6 1 (:DEFINITION ALL-NILS))
                    (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                    (5 5
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (5 2 (:REWRITE DEFAULT-+-1))
                    (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                    (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                    (4 2
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (4 2 (:REWRITE DEFAULT-+-2))
                    (4 2
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                    (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
                    (2 2
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (2 2 (:REWRITE DEFAULT-<-2))
                    (2 2 (:REWRITE DEFAULT-<-1))
                    (2 2
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (2 1
                       (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                    (2 1
                       (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                    (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::INTEGERP-OF-SUM-PPS-BY-ROW
     (277 7
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (267 5 (:DEFINITION APPLY$-BADGEP))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (103 103 (:REWRITE DEFAULT-CDR))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (40 40 (:REWRITE DEFAULT-CAR))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 2 (:DEFINITION NATP))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (7 7 (:TYPE-PRESCRIPTION LEN))
     (7 1 (:DEFINITION LEN))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (3 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::MULT-BYROW-SPEC)
(RP::ASH-OF-0 (7 1 (:REWRITE DEFAULT-FLOOR-RATIO))
              (4 1 (:REWRITE |(* y x)|))
              (3 3 (:REWRITE REDUCE-INTEGERP-+))
              (3 3 (:REWRITE INTEGERP-MINUS-X))
              (3 3
                 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
              (3 3 (:META META-INTEGERP-CORRECT))
              (2 2 (:REWRITE DEFAULT-TIMES-2))
              (2 2 (:REWRITE DEFAULT-TIMES-1))
              (1 1 (:REWRITE DEFAULT-FLOOR-2))
              (1 1 (:REWRITE DEFAULT-FLOOR-1))
              (1 1 (:REWRITE |(* 1 x)|)))
(RP::MULT-BYROW-SPEC-IS-MULT-SIMPLE-SPEC-LEMMA
 (841 39 (:REWRITE DEFAULT-FLOOR-RATIO))
 (599 266 (:REWRITE DEFAULT-TIMES-2))
 (544 8 (:REWRITE FLOOR-ZERO . 3))
 (499 266 (:REWRITE DEFAULT-TIMES-1))
 (451 88 (:REWRITE DEFAULT-PLUS-1))
 (432 8 (:REWRITE CANCEL-FLOOR-+))
 (325
  325
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (325 325
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (325
     325
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (325 325
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (325 325
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (281 89 (:REWRITE INTEGERP-MINUS-X))
 (280 8 (:REWRITE FLOOR-ZERO . 5))
 (280 8 (:REWRITE FLOOR-ZERO . 4))
 (272 8 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (268 268
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (248 8 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (184 8 (:REWRITE FLOOR-=-X/Y . 2))
 (180 18 (:REWRITE DEFAULT-DIVIDE))
 (171 88 (:REWRITE DEFAULT-PLUS-2))
 (156 39 (:REWRITE DEFAULT-FLOOR-2))
 (136 16 (:REWRITE |(* (- x) y)|))
 (132 12 (:REWRITE ACL2-NUMBERP-X))
 (117 117
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (117 117
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (117 117
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (103 39 (:REWRITE DEFAULT-MINUS))
 (81 81 (:REWRITE REDUCE-INTEGERP-+))
 (81 81
     (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (81 81 (:META META-INTEGERP-CORRECT))
 (77 45
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (77 45 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (77 45 (:REWRITE DEFAULT-LESS-THAN-1))
 (72 16 (:REWRITE |(- (* c x))|))
 (72 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (72 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (60 12 (:REWRITE RATIONALP-X))
 (55 39 (:REWRITE DEFAULT-FLOOR-1))
 (53 45
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (53 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (45 45 (:REWRITE THE-FLOOR-BELOW))
 (45 45 (:REWRITE THE-FLOOR-ABOVE))
 (45 45 (:REWRITE SIMPLIFY-SUMS-<))
 (45 45
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (45 45
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (45 45 (:REWRITE INTEGERP-<-CONSTANT))
 (45 45 (:REWRITE DEFAULT-LESS-THAN-2))
 (45 45 (:REWRITE CONSTANT-<-INTEGERP))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< c (- x))|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< (/ x) (/ y))|))
 (45 45 (:REWRITE |(< (- x) c)|))
 (45 45 (:REWRITE |(< (- x) (- y))|))
 (40 8 (:REWRITE FLOOR-ZERO . 2))
 (40 8 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (40 8 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (40 8
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (40 8 (:REWRITE FLOOR-CANCEL-*-CONST))
 (40 8
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (37 37 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31 (:REWRITE DEFAULT-EXPT-2))
 (31 31 (:REWRITE DEFAULT-EXPT-1))
 (31 31 (:REWRITE |(expt 1/c n)|))
 (31 31 (:REWRITE |(expt (- x) n)|))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (29 29 (:REWRITE |(< (/ x) 0)|))
 (29 29 (:REWRITE |(< (* x y) 0)|))
 (22 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:TYPE-PRESCRIPTION ABS))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12
     (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (12 12
     (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:META META-RATIONALP-CORRECT))
 (10 10 (:REWRITE ZP-OPEN))
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
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (8 8 (:REWRITE |(floor x 2)| . 2))
 (8 8 (:REWRITE |(floor x (- y))| . 2))
 (8 8 (:REWRITE |(floor x (- y))| . 1))
 (8 8
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (8 8
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (8 8 (:REWRITE |(floor (- x) y)| . 2))
 (8 8 (:REWRITE |(floor (- x) y)| . 1))
 (8 8
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (8 7 (:REWRITE DEFAULT-CDR))
 (8 7 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(RP::MULT-BYROW-SPEC-IS-MULT-SIMPLE-SPEC
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP)))
(RP::SUM-LST (257 3
                  (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
             (255 1 (:DEFINITION APPLY$-BADGEP))
             (177 1 (:DEFINITION SUBSETP-EQUAL))
             (164 14 (:DEFINITION MEMBER-EQUAL))
             (102 7
                  (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
             (96 96 (:REWRITE DEFAULT-CDR))
             (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
             (30 30 (:REWRITE DEFAULT-CAR))
             (21 21
                 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
             (20 2 (:DEFINITION NATP))
             (14 14
                 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
             (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
             (9 1 (:DEFINITION RP::SUM-LST))
             (7 7 (:TYPE-PRESCRIPTION LEN))
             (7 1 (:DEFINITION LEN))
             (6 3
                (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
             (6 1 (:DEFINITION ALL-NILS))
             (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
             (5 5
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (5 2 (:REWRITE DEFAULT-+-1))
             (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
             (4 4 (:LINEAR LEN-WHEN-PREFIXP))
             (4 2
                (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
             (4 2 (:REWRITE DEFAULT-+-2))
             (4 2
                (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
             (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
             (2 2
                (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
             (2 2 (:REWRITE DEFAULT-<-2))
             (2 2 (:REWRITE DEFAULT-<-1))
             (2 2
                (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
             (2 1
                (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
             (2 1
                (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
             (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::INTEGERP-OF-SUM-LST (277 7
                              (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                         (267 5 (:DEFINITION APPLY$-BADGEP))
                         (177 1 (:DEFINITION SUBSETP-EQUAL))
                         (164 14 (:DEFINITION MEMBER-EQUAL))
                         (103 103 (:REWRITE DEFAULT-CDR))
                         (102 7
                              (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                         (40 40 (:REWRITE DEFAULT-CAR))
                         (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                         (21 21
                             (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                         (20 20
                             (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                         (20 2 (:DEFINITION NATP))
                         (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                         (14 14
                             (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                         (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
                         (7 7 (:TYPE-PRESCRIPTION LEN))
                         (7 1 (:DEFINITION LEN))
                         (6 3
                            (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                         (6 1 (:DEFINITION ALL-NILS))
                         (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                         (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                         (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                         (4 2
                            (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                         (3 2 (:REWRITE DEFAULT-+-2))
                         (2 2 (:REWRITE DEFAULT-<-2))
                         (2 2 (:REWRITE DEFAULT-<-1))
                         (2 2 (:REWRITE DEFAULT-+-1))
                         (2 1
                            (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                         (2 1
                            (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                         (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::STRIP-LOGCARS (257 3
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (255 1 (:DEFINITION APPLY$-BADGEP))
                   (177 1 (:DEFINITION SUBSETP-EQUAL))
                   (164 14 (:DEFINITION MEMBER-EQUAL))
                   (102 7
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (94 94 (:REWRITE DEFAULT-CDR))
                   (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (29 29 (:REWRITE DEFAULT-CAR))
                   (21 21
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (20 2 (:DEFINITION NATP))
                   (14 14
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (7 7 (:TYPE-PRESCRIPTION LEN))
                   (7 1 (:DEFINITION LEN))
                   (6 6
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (6 3
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (6 1 (:DEFINITION ALL-NILS))
                   (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                   (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                   (4 2
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2 2 (:REWRITE DEFAULT-<-2))
                   (2 2 (:REWRITE DEFAULT-<-1))
                   (2 1 (:REWRITE DEFAULT-+-2))
                   (2 1
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (2 1
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (1 1 (:REWRITE DEFAULT-+-1)))
(RP::INTEGER-LISTP-OF-STRIP-LOGCARS
     (277 7
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (267 5 (:DEFINITION APPLY$-BADGEP))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (112 111 (:REWRITE DEFAULT-CDR))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (49 48 (:REWRITE DEFAULT-CAR))
     (32 2
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (22 22
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (20 2 (:DEFINITION NATP))
     (16 10 (:REWRITE DEFAULT-+-2))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (11 10 (:REWRITE DEFAULT-+-1))
     (8 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (7 7 (:TYPE-PRESCRIPTION LEN))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 1 (:DEFINITION LEN))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 2 (:DEFINITION NFIX))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (2 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1 1 (:REWRITE DEFAULT-NUMERATOR))
     (1 1 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::STRIP-LOGBITS (257 3
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (255 1 (:DEFINITION APPLY$-BADGEP))
                   (177 1 (:DEFINITION SUBSETP-EQUAL))
                   (164 14 (:DEFINITION MEMBER-EQUAL))
                   (102 7
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (94 94 (:REWRITE DEFAULT-CDR))
                   (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (29 29 (:REWRITE DEFAULT-CAR))
                   (21 21
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (14 14
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (7 7 (:TYPE-PRESCRIPTION LEN))
                   (7 7
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (7 1 (:DEFINITION LEN))
                   (6 3
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (6 1 (:DEFINITION ALL-NILS))
                   (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                   (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                   (4 2
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (3 3 (:REWRITE DEFAULT-<-2))
                   (3 3 (:REWRITE DEFAULT-<-1))
                   (2 1 (:REWRITE DEFAULT-+-2))
                   (2 1
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (2 1
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (1 1 (:REWRITE DEFAULT-+-1)))
(RP::INTEGER-LISTP-OF-STRIP-LOGBITS
     (277 7
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (267 5 (:DEFINITION APPLY$-BADGEP))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (116 115 (:REWRITE DEFAULT-CDR))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (53 52 (:REWRITE DEFAULT-CAR))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (26 26
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (20 2 (:DEFINITION NATP))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (14 1 (:DEFINITION EXPT))
     (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (12 4 (:REWRITE DEFAULT-*-2))
     (8 4 (:REWRITE DEFAULT-*-1))
     (7 7 (:TYPE-PRESCRIPTION LEN))
     (7 1 (:DEFINITION LEN))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (5 1 (:REWRITE DEFAULT-UNARY-/))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 3 (:REWRITE DEFAULT-+-2))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE COMMUTATIVITY-OF-+))
     (2 1 (:REWRITE ZIP-OPEN))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::STRIP-LOGCDRS (257 3
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (255 1 (:DEFINITION APPLY$-BADGEP))
                   (177 1 (:DEFINITION SUBSETP-EQUAL))
                   (164 14 (:DEFINITION MEMBER-EQUAL))
                   (102 7
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (94 94 (:REWRITE DEFAULT-CDR))
                   (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (29 29 (:REWRITE DEFAULT-CAR))
                   (21 21
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (20 2 (:DEFINITION NATP))
                   (14 14
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (7 7 (:TYPE-PRESCRIPTION LEN))
                   (7 1 (:DEFINITION LEN))
                   (6 6
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (6 3
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (6 1 (:DEFINITION ALL-NILS))
                   (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                   (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                   (4 2
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2 2 (:REWRITE DEFAULT-<-2))
                   (2 2 (:REWRITE DEFAULT-<-1))
                   (2 1 (:REWRITE DEFAULT-+-2))
                   (2 1
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (2 1
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (1 1 (:REWRITE DEFAULT-+-1)))
(RP::INTEGER-LISTP-OF-STRIP-LOGCDRS
     (277 7
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (267 5 (:DEFINITION APPLY$-BADGEP))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (112 111 (:REWRITE DEFAULT-CDR))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (49 48 (:REWRITE DEFAULT-CAR))
     (32 2
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (22 22
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (20 2 (:DEFINITION NATP))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (13 9 (:REWRITE DEFAULT-+-2))
     (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (10 9 (:REWRITE DEFAULT-+-1))
     (7 7 (:TYPE-PRESCRIPTION LEN))
     (7 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (7 1 (:DEFINITION LEN))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 2 (:DEFINITION NFIX))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (5 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (2 2 (:REWRITE DEFAULT-*-2))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (1 1 (:REWRITE DEFAULT-NUMERATOR))
     (1 1 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::STRIP-LOGTAIL (257 3
                        (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
                   (255 1 (:DEFINITION APPLY$-BADGEP))
                   (177 1 (:DEFINITION SUBSETP-EQUAL))
                   (164 14 (:DEFINITION MEMBER-EQUAL))
                   (102 7
                        (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
                   (94 94 (:REWRITE DEFAULT-CDR))
                   (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
                   (29 29 (:REWRITE DEFAULT-CAR))
                   (21 21
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
                   (14 14
                       (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
                   (10 10 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
                   (7 7 (:TYPE-PRESCRIPTION LEN))
                   (7 7
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (7 1 (:DEFINITION LEN))
                   (6 3
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
                   (6 1 (:DEFINITION ALL-NILS))
                   (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
                   (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
                   (4 4 (:REWRITE DEFAULT-<-2))
                   (4 4 (:REWRITE DEFAULT-<-1))
                   (4 4 (:LINEAR LEN-WHEN-PREFIXP))
                   (4 2
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
                   (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
                   (2 1 (:REWRITE DEFAULT-+-2))
                   (2 1
                      (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
                   (2 1
                      (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
                   (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                   (1 1 (:REWRITE DEFAULT-+-1)))
(RP::INTEGER-LISTP-OF-STRIP-LOGTAIL
     (277 7
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (267 5 (:DEFINITION APPLY$-BADGEP))
     (177 1 (:DEFINITION SUBSETP-EQUAL))
     (164 14 (:DEFINITION MEMBER-EQUAL))
     (116 115 (:REWRITE DEFAULT-CDR))
     (102 7
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (53 52 (:REWRITE DEFAULT-CAR))
     (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (26 26
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (21 21
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (20 2 (:DEFINITION NATP))
     (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (14 14
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (14 1 (:DEFINITION EXPT))
     (12 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (9 1 (:REWRITE DEFAULT-UNARY-/))
     (7 7 (:TYPE-PRESCRIPTION LEN))
     (7 1 (:DEFINITION LEN))
     (6 3
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (6 1 (:DEFINITION ALL-NILS))
     (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
     (5 2 (:REWRITE DEFAULT-*-2))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:LINEAR LEN-WHEN-PREFIXP))
     (4 3 (:REWRITE DEFAULT-+-2))
     (4 2
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (3 3
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (3 3
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 1 (:REWRITE COMMUTATIVITY-OF-+))
     (2 2 (:REWRITE DEFAULT-*-1))
     (2 1 (:REWRITE ZIP-OPEN))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
     (2 1
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (1 1 (:REWRITE O-INFP->NEQ-0))
     (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS)))
(RP::LEMMA1)
(RP::SUM-PPS-BY-COL (441 1 (:DEFINITION RP::SUM-PPS-BY-COL))
                    (111 26 (:REWRITE DEFAULT-+-1))
                    (100 5 (:REWRITE COMMUTATIVITY-OF-+))
                    (94 6 (:REWRITE COMMUTATIVITY-2-OF-+))
                    (91 26 (:REWRITE DEFAULT-+-2))
                    (60 19 (:REWRITE BITOPS::LOGCAR-OF-BIT))
                    (46 8 (:REWRITE BITOPS::LOGCDR-OF-BIT))
                    (20 20 (:TYPE-PRESCRIPTION BITP))
                    (19 17 (:REWRITE FOLD-CONSTS-IN-+))
                    (7 7 (:REWRITE DEFAULT-<-2))
                    (7 7 (:REWRITE DEFAULT-<-1))
                    (7 3 (:REWRITE ZP-WHEN-GT-0))
                    (5 5
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (3 3 (:REWRITE BITOPS::LOGXOR-FOLD-CONSTS))
                    (3 3 (:REWRITE DEFAULT-CDR))
                    (3 3 (:REWRITE DEFAULT-CAR))
                    (3 1 (:REWRITE UNICITY-OF-0))
                    (3 1 (:REWRITE NATP-WHEN-GTE-0))
                    (2 1 (:REWRITE NATP-WHEN-INTEGERP))
                    (2 1 (:DEFINITION FIX)))
(RP::INTEGERP-OF-SUM-PPS-BY-COL)
(RP::MULT-BYCOL-SPEC)
(RP::LOGHEAD-OF-0)
(RP::APPEND-OF-REPEAT-0 (22 10 (:REWRITE DEFAULT-CDR))
                        (20 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
                        (18 6 (:REWRITE ZP-WHEN-GT-0))
                        (13 10 (:REWRITE DEFAULT-CAR))
                        (12 6 (:REWRITE ZP-WHEN-INTEGERP))
                        (12 3 (:REWRITE CDR-OF-APPEND-WHEN-CONSP))
                        (6 6 (:REWRITE ZP-OPEN))
                        (6 6
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (6 6 (:REWRITE DEFAULT-<-2))
                        (6 6 (:REWRITE DEFAULT-<-1))
                        (4 4 (:REWRITE DEFAULT-+-2))
                        (4 4 (:REWRITE DEFAULT-+-1)))
(RP::FLOOR-IS-LOGCDR (64 4
                         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                     (22 16 (:REWRITE DEFAULT-+-2))
                     (18 16 (:REWRITE DEFAULT-+-1))
                     (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
                     (6 6 (:REWRITE DEFAULT-<-2))
                     (6 6 (:REWRITE DEFAULT-<-1))
                     (6 3
                        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                     (5 5 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
                     (4 4 (:REWRITE NFIX-WHEN-NATP))
                     (4 4 (:REWRITE DEFAULT-*-2))
                     (4 4 (:REWRITE DEFAULT-*-1))
                     (3 3 (:TYPE-PRESCRIPTION NATP))
                     (3 3
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (3 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                     (3 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                     (2 2 (:REWRITE DEFAULT-NUMERATOR))
                     (2 2 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::MOD-IS-LOGCAR
     (8 8 (:TYPE-PRESCRIPTION FLOOR))
     (6 4 (:REWRITE DEFAULT-*-2))
     (6 4 (:REWRITE DEFAULT-*-1))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 2 (:REWRITE DEFAULT-+-2))
     (2 2
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (2 2 (:REWRITE DEFAULT-+-1))
     (1 1
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(RP::INTEGER-LISTP-IMPLIES (1 1
                              (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                           (1 1 (:REWRITE DEFAULT-CDR))
                           (1 1 (:REWRITE DEFAULT-CAR)))
(RP::LEMMA1-LEMMA
     (1100 220 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (1100 220 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (1060 220
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (1060 220
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (1047 11 (:REWRITE DEFAULT-MOD-RATIO))
     (1012 15 (:REWRITE |(* y x)|))
     (917 917
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (917 917
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (917 917
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (898 110 (:REWRITE DEFAULT-TIMES-2))
     (745 3 (:LINEAR MOD-BOUNDS-3))
     (434 34 (:REWRITE DEFAULT-PLUS-2))
     (426 34 (:REWRITE DEFAULT-PLUS-1))
     (368 10 (:REWRITE SUM-IS-EVEN . 2))
     (282 110 (:REWRITE DEFAULT-TIMES-1))
     (245 245
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (245 245
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (245 245
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (220 220 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (220 220
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (220 220
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (220 220
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (220 220 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (142 6 (:LINEAR MOD-BOUNDS-2))
     (127 11 (:REWRITE DEFAULT-MOD-1))
     (93 93
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (39 39 (:REWRITE REDUCE-INTEGERP-+))
     (39 39 (:REWRITE INTEGERP-MINUS-X))
     (39 39
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (39 39 (:META META-INTEGERP-CORRECT))
     (29 1 (:REWRITE |(* (if a b c) x)|))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (22 22 (:REWRITE NORMALIZE-ADDENDS))
     (11 11
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (11 11
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (11 11 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (3 3
        (:REWRITE INTEGERP-+-REDUCE-CONSTANT)))
(RP::LEMMA1-LEMMA2 (2 2 (:REWRITE REDUCE-INTEGERP-+))
                   (2 2
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (2 2 (:REWRITE NORMALIZE-ADDENDS))
                   (2 2 (:REWRITE INTEGERP-MINUS-X))
                   (2 2
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (2 2 (:REWRITE DEFAULT-PLUS-2))
                   (2 2 (:REWRITE DEFAULT-PLUS-1))
                   (2 2 (:META META-INTEGERP-CORRECT))
                   (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(RP::LEMMA1-LEMMA3
     (650 130 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (650 130 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (602 130
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (602 130
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (562 562
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (562 562
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (562 562
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (170 10 (:REWRITE DEFAULT-MOD-RATIO))
     (130 130 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (130 130
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (130 130
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (130 130
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (130 130 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (108 12 (:REWRITE |(* y x)|))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (64 64 (:REWRITE DEFAULT-TIMES-2))
     (64 64 (:REWRITE DEFAULT-TIMES-1))
     (52 52
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (46 2 (:LINEAR MOD-BOUNDS-3))
     (44 12 (:REWRITE DEFAULT-PLUS-1))
     (42 4 (:REWRITE SUM-IS-EVEN . 2))
     (20 20 (:REWRITE REDUCE-INTEGERP-+))
     (20 20 (:REWRITE INTEGERP-MINUS-X))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (20 20 (:META META-INTEGERP-CORRECT))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (12 12 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-2))
     (10 10
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (10 10 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (4 4
        (:REWRITE REDUCE-INTEGERP-+-CONSTANT)))
(RP::LEMMA1-LEMMA4 (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                   (15 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                   (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                   (7 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                   (7 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                   (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                   (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                   (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                   (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                   (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                   (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                   (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD)))
(RP::LEMMA1
     (535 10
          (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
     (519 5 (:DEFINITION APPLY$-BADGEP))
     (354 2 (:DEFINITION SUBSETP-EQUAL))
     (328 28 (:DEFINITION MEMBER-EQUAL))
     (204 14
          (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
     (196 195 (:REWRITE DEFAULT-CDR))
     (66 65 (:REWRITE DEFAULT-CAR))
     (62 62 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (42 42
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
     (28 28
         (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
     (24 6 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (24 4 (:REWRITE NATP-WHEN-GTE-0))
     (23 23 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
     (20 10 (:REWRITE DEFAULT-+-2))
     (19 10 (:REWRITE DEFAULT-+-1))
     (14 14 (:TYPE-PRESCRIPTION LEN))
     (14 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
     (14 2 (:DEFINITION LEN))
     (13 13
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 6
         (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
     (12 4 (:REWRITE NATP-WHEN-INTEGERP))
     (12 4 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (12 2 (:DEFINITION ALL-NILS))
     (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
     (10 10
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (8 8 (:TYPE-PRESCRIPTION BITP))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (8 4
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 2
        (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
     (2 2
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 1
        (:REWRITE APPLY$-BADGEP-PROPERTIES . 2)))
(RP::LEMMA2-LEMMA1
     (576 576
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (576 576
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (576 576
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (171 19 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (171 19
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (171 19
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (171 19
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (171 19
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (120 24
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (120 24
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (95 19 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (95 19 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (95 19
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (72 46 (:REWRITE DEFAULT-TIMES-2))
     (67 5 (:REWRITE DEFAULT-MOD-RATIO))
     (58 46 (:REWRITE DEFAULT-TIMES-1))
     (56 2 (:LINEAR MOD-BOUNDS-3))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (51 51 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (39 3 (:REWRITE DEFAULT-FLOOR-RATIO))
     (33 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (29 29
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (28 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (24 24
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (24 24
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (24 4 (:LINEAR MOD-BOUNDS-2))
     (21 12 (:REWRITE DEFAULT-PLUS-2))
     (21 12 (:REWRITE DEFAULT-PLUS-1))
     (13 13 (:REWRITE REDUCE-INTEGERP-+))
     (13 13 (:REWRITE INTEGERP-MINUS-X))
     (13 13
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (13 13 (:META META-INTEGERP-CORRECT))
     (9 5 (:REWRITE DEFAULT-MOD-1))
     (8 4
        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (5 5
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-MOD-2))
     (5 5 (:REWRITE |(mod x 2)| . 2))
     (5 3 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (3 3 (:REWRITE DEFAULT-FLOOR-2))
     (3 3 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(RP::LEMMA2-LEMMA2
     (775 139 (:REWRITE DEFAULT-PLUS-1))
     (699 699
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (699 699
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (699 699
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (479 49 (:REWRITE ACL2-NUMBERP-X))
     (294 139 (:REWRITE DEFAULT-PLUS-2))
     (225 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (215 43 (:REWRITE RATIONALP-X))
     (179 117 (:REWRITE DEFAULT-TIMES-2))
     (135 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (135 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (135 27
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (135 27
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (127 117 (:REWRITE DEFAULT-TIMES-1))
     (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (125 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (125 10 (:REWRITE DEFAULT-MOD-RATIO))
     (125 10 (:REWRITE DEFAULT-FLOOR-RATIO))
     (103 103 (:REWRITE REDUCE-INTEGERP-+))
     (103 103 (:REWRITE INTEGERP-MINUS-X))
     (103 103
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (103 103 (:META META-INTEGERP-CORRECT))
     (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (95 95 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (90 20 (:REWRITE |(* y x)|))
     (88 88
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (79 79
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (78 3 (:REWRITE IFIX-EQUAL-TO-NONZERO))
     (74 70 (:REWRITE DEFAULT-CAR))
     (72 3 (:REWRITE ZIP-OPEN))
     (70 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (68 24 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (54 50 (:REWRITE DEFAULT-CDR))
     (49 49
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (43 43 (:REWRITE REDUCE-RATIONALP-+))
     (43 43 (:REWRITE REDUCE-RATIONALP-*))
     (43 43 (:REWRITE RATIONALP-MINUS-X))
     (43 43
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (43 43 (:META META-RATIONALP-CORRECT))
     (40 13
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (36 36 (:TYPE-PRESCRIPTION BITP))
     (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (27 27
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (27 27
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (27 27 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (27 9 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (27 9 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (22 11
         (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (15 10 (:REWRITE DEFAULT-MOD-1))
     (15 10 (:REWRITE DEFAULT-FLOOR-1))
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
     (12 12 (:REWRITE FOLD-CONSTS-IN-+))
     (11 11 (:TYPE-PRESCRIPTION NATP))
     (10 10
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (10 10 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:REWRITE DEFAULT-FLOOR-2))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (10 10 (:REWRITE |(floor x 2)| . 2))
     (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3 (:TYPE-PRESCRIPTION ZIP))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE O-INFP->NEQ-0))
     (3 3
        (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN)))
(RP::LEMMA2-LEMMA3 (223 17 (:REWRITE DEFAULT-PLUS-1))
                   (154 14 (:REWRITE ACL2-NUMBERP-X))
                   (70 14 (:REWRITE RATIONALP-X))
                   (34 17 (:REWRITE DEFAULT-PLUS-2))
                   (26 23 (:REWRITE DEFAULT-CAR))
                   (21 7 (:REWRITE BITOPS::LOGCAR-OF-BIT))
                   (21 4 (:REWRITE RP::LEMMA2-LEMMA2))
                   (19 16 (:REWRITE DEFAULT-CDR))
                   (18 18 (:REWRITE REDUCE-INTEGERP-+))
                   (18 18 (:REWRITE INTEGERP-MINUS-X))
                   (18 18
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (18 18 (:META META-INTEGERP-CORRECT))
                   (14 14 (:TYPE-PRESCRIPTION BITP))
                   (14 14 (:REWRITE REDUCE-RATIONALP-+))
                   (14 14 (:REWRITE REDUCE-RATIONALP-*))
                   (14 14 (:REWRITE RATIONALP-MINUS-X))
                   (14 14
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                   (14 14
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                   (14 14 (:META META-RATIONALP-CORRECT))
                   (10 10
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (10 10 (:REWRITE NORMALIZE-ADDENDS))
                   (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (9 3
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (9 3
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (4 4 (:TYPE-PRESCRIPTION LOGCAR-TYPE))
                   (4 4
                      (:REWRITE RP::INTEGER-LISTP-OF-STRIP-LOGCARS))
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
                   (3 3 (:REWRITE |(equal (- x) (- y))|)))
(RP::LEMMA2-LEMMA4
     (1451 1451
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (1451 1451
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (1451 1451
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (438 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (438 50
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (438 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (438 50
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (438 50
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (250 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (250 50 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (250 50
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (108 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (106 42 (:REWRITE DEFAULT-PLUS-2))
     (93 57 (:REWRITE DEFAULT-TIMES-2))
     (80 4 (:REWRITE |(* y x)|))
     (60 42 (:REWRITE DEFAULT-PLUS-1))
     (57 57 (:REWRITE DEFAULT-TIMES-1))
     (53 2 (:REWRITE |(floor (+ x r) i)|))
     (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (49 49 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (45 2
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (35 35
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (4 4 (:REWRITE DEFAULT-FLOOR-1))
     (4 4 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:TYPE-PRESCRIPTION ABS))
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
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
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
(RP::LEMMA2-LEMMA5 (4 4
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (4 4 (:REWRITE NORMALIZE-ADDENDS))
                   (4 4 (:REWRITE DEFAULT-PLUS-2))
                   (4 4 (:REWRITE DEFAULT-PLUS-1))
                   (2 2 (:REWRITE REDUCE-INTEGERP-+))
                   (2 2
                      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                   (2 2 (:REWRITE INTEGERP-MINUS-X))
                   (2 2
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                   (2 2 (:REWRITE DEFAULT-TIMES-2))
                   (2 2 (:REWRITE DEFAULT-TIMES-1))
                   (2 2 (:META META-INTEGERP-CORRECT)))
(RP::LEMMA2 (44 4 (:DEFINITION RP::SUM-PPS-BY-ROW))
            (26 9 (:REWRITE DEFAULT-+-1))
            (24 2 (:DEFINITION RP::STRIP-LOGCDRS))
            (18 9 (:REWRITE DEFAULT-+-2))
            (18 3 (:DEFINITION RP::STRIP-LOGCARS))
            (11 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
            (10 10 (:TYPE-PRESCRIPTION BITP))
            (10 10 (:REWRITE DEFAULT-CDR))
            (10 10 (:REWRITE DEFAULT-CAR))
            (9 3 (:REWRITE BITOPS::LOGCAR-OF-BIT))
            (8 4
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (6 6
               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (6 2 (:REWRITE BITOPS::LOGCDR-OF-BIT))
            (4 4
               (:TYPE-PRESCRIPTION RP::STRIP-LOGCDRS))
            (4 4
               (:TYPE-PRESCRIPTION RP::STRIP-LOGCARS))
            (4 4
               (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
            (4 4
               (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
            (4 2 (:REWRITE DEFAULT-*-2))
            (4 1 (:DEFINITION INTEGER-LISTP))
            (2 2 (:REWRITE DEFAULT-*-1)))
(RP::MULT-BYCOL-SPEC-IS-MULT-BYROW-SPEC-LEMMA
     (17503 32 (:REWRITE LOGHEAD-IDENTITY))
     (10527 72 (:DEFINITION UNSIGNED-BYTE-P**))
     (7578 144 (:REWRITE UNSIGNED-BYTE-P-PLUS))
     (7525 61 (:DEFINITION UNSIGNED-BYTE-P))
     (7332 55 (:DEFINITION INTEGER-RANGE-P))
     (2572 40 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (1780 387 (:REWRITE DEFAULT-+-1))
     (1662 387 (:REWRITE DEFAULT-+-2))
     (1632 1632 (:TYPE-PRESCRIPTION BITP-OF-B-AND))
     (1470 14 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (728 14 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (627 259 (:REWRITE DEFAULT-<-1))
     (570 570
          (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (538 71 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (486 486 (:TYPE-PRESCRIPTION BITP))
     (448 14 (:REWRITE NEGP-WHEN-INTEGERP))
     (403 39 (:DEFINITION RP::SUM-PPS-BY-ROW))
     (369 259 (:REWRITE DEFAULT-<-2))
     (363 33 (:DEFINITION RP::SUM-LST))
     (336 336 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (234 12 (:LINEAR LOGHEAD-LEQ))
     (224 112 (:LINEAR BITOPS::B-AND-BOUND))
     (208 33 (:DEFINITION RP::STRIP-LOGCDRS))
     (208 33 (:DEFINITION RP::STRIP-LOGCARS))
     (198 198
          (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (198 24 (:REWRITE BFIX-WHEN-NOT-1))
     (183 183
          (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (173 173
          (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (147 49 (:REWRITE ZP-WHEN-GT-0))
     (144 72
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (138 138 (:REWRITE DEFAULT-CDR))
     (138 138 (:REWRITE DEFAULT-CAR))
     (130 130
          (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (94 44 (:REWRITE O-INFP->NEQ-0))
     (72 72
         (:TYPE-PRESCRIPTION RP::STRIP-LOGCDRS))
     (72 72
         (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (72 72
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (66 66
         (:TYPE-PRESCRIPTION RP::STRIP-LOGCARS))
     (54 54
         (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (54 24 (:REWRITE BFIX-WHEN-NOT-BITP))
     (54 11 (:REWRITE NATP-WHEN-INTEGERP))
     (48 24 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (48 24 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (44 22 (:LINEAR BITOPS::B-XOR-BOUND))
     (18 6
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (16 16
         (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (14 14 (:TYPE-PRESCRIPTION NEGP))
     (12 6
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (6 6 (:TYPE-PRESCRIPTION POSP))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 4
        (:REWRITE BITOPS::B-AND-EQUAL-0-IN-CONCL))
     (4 2 (:DEFINITION FIX))
     (1 1
        (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT)))
(RP::MULT-BYCOL-SPEC-IS-MULT-BYROW-SPEC
     (85 4 (:REWRITE LOGHEAD-IDENTITY))
     (75 3 (:DEFINITION UNSIGNED-BYTE-P))
     (66 3 (:DEFINITION INTEGER-RANGE-P))
     (16 2 (:LINEAR LOGHEAD-LEQ))
     (15 9 (:REWRITE DEFAULT-<-2))
     (14 9 (:REWRITE DEFAULT-<-1))
     (10 10 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (9 3
        (:REWRITE RP::INTEGERP-OF-SUM-PPS-BY-ROW))
     (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (2 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(RP::LOGHEAD-OF-*-IS-MULT-BYCOL-SPEC
     (52 4 (:REWRITE LOGHEAD-IDENTITY))
     (42 3 (:DEFINITION UNSIGNED-BYTE-P))
     (33 3 (:DEFINITION INTEGER-RANGE-P))
     (15 9 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (9 9 (:REWRITE DEFAULT-<-1))
     (6 2 (:LINEAR LOGHEAD-LEQ))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP)))
(RP::SUM-COL-BYBIT (64 1 (:DEFINITION RP::SUM-COL-BYBIT))
                   (49 49 (:REWRITE DEFAULT-<-2))
                   (49 49 (:REWRITE DEFAULT-<-1))
                   (28 28
                       (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
                   (27 3 (:REWRITE LOGTAIL-IDENTITY))
                   (24 18 (:REWRITE ZP-WHEN-GT-0))
                   (21 7
                       (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
                   (18 6
                       (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
                   (18 3 (:DEFINITION UNSIGNED-BYTE-P))
                   (16 16 (:TYPE-PRESCRIPTION BITP))
                   (15 3 (:DEFINITION INTEGER-RANGE-P))
                   (14 14 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
                   (14 13 (:REWRITE DEFAULT-+-2))
                   (14 13 (:REWRITE DEFAULT-+-1))
                   (12 4 (:REWRITE NATP-WHEN-GTE-0))
                   (10 1 (:REWRITE BITOPS::LOGTAIL-OF-LOGTAIL))
                   (8 4 (:REWRITE FOLD-CONSTS-IN-+))
                   (8 1 (:REWRITE BITOPS::LOGBITP-OF-LOGTAIL))
                   (7 7
                      (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
                   (6 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
                   (6 1 (:REWRITE COMMUTATIVITY-2-OF-+))
                   (5 5
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                   (4 1
                      (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
                   (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                   (3 3
                      (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                   (2 1
                      (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)))
(RP::INTEGERP-OF-SUM-COL-BYBIT
     (1 1
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)))
(RP::LEMMA1
     (7 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (3 2 (:REWRITE DEFAULT-*-2))
     (3 2 (:REWRITE DEFAULT-*-1))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(RP::SUM-PPS-BYCOL-BYBIT
     (48 37 (:REWRITE DEFAULT-+-1))
     (45 37 (:REWRITE DEFAULT-+-2))
     (30 1 (:DEFINITION RP::SUM-PPS-BYCOL-BYBIT))
     (23 14 (:REWRITE DEFAULT-UNARY-MINUS))
     (18 18 (:REWRITE DEFAULT-<-2))
     (18 18 (:REWRITE DEFAULT-<-1))
     (15 9
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 8 (:REWRITE ZP-WHEN-GT-0))
     (9 9
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (8 4 (:REWRITE NATP-WHEN-INTEGERP))
     (7 5 (:REWRITE FOLD-CONSTS-IN-+))
     (7 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (3 3 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (3 1 (:REWRITE O<=-O-FINP-DEF))
     (2 2
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1 (:REWRITE O-INFP-O-FINP-O<=))
     (1 1 (:REWRITE AC-<)))
(RP::INTEGERP-OF-SUM-PPS-BYCOL-BYBIT)
(RP::MULT-BYCOL-BYBIT-SPEC)
(RP::LOGCAR-IS-LOGBIT-0
     (66 4
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (66 4 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (49 49 (:TYPE-PRESCRIPTION NATP))
     (46 23
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (46 23
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (46 23
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NEGP))
     (46 23
         (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
     (28 28 (:TYPE-PRESCRIPTION BITP))
     (23 23 (:TYPE-PRESCRIPTION POSP))
     (23 23 (:TYPE-PRESCRIPTION NEGP))
     (20 4 (:LINEAR BITOPS::LOGCAR-BOUND))
     (18 6 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (12 4
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (8 8 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (6 3
        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (4 4
        (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::STRIP-LOG-CARS-IS-STRIP-LOGBITS
     (20 20 (:TYPE-PRESCRIPTION BITP))
     (12 12 (:REWRITE DEFAULT-CAR))
     (12 4
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (12 4
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (12 4 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (8 8 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (6 6
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 2 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (4 4
        (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL)))
(RP::GET-COL (33 33 (:REWRITE DEFAULT-<-2))
             (33 33 (:REWRITE DEFAULT-<-1))
             (28 28
                 (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
             (21 17 (:REWRITE ZP-WHEN-GT-0))
             (12 4 (:REWRITE NATP-WHEN-GTE-0))
             (9 1 (:REWRITE LOGTAIL-IDENTITY))
             (6 6 (:TYPE-PRESCRIPTION BITP))
             (6 2
                (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
             (6 2
                (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
             (6 1 (:DEFINITION UNSIGNED-BYTE-P))
             (5 5
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
             (5 1 (:DEFINITION INTEGER-RANGE-P))
             (4 4 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
             (4 4 (:REWRITE DEFAULT-+-2))
             (4 4 (:REWRITE DEFAULT-+-1))
             (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
             (3 1 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
             (2 2
                (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
             (2 1
                (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
             (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
             (1 1
                (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR)))
(RP::STRIP-LOGBITS-OF-CREATE-PPS-IS-GET-COL
     (10817 134 (:DEFINITION BITMASKP**))
     (2794 1267
           (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (2302 753
           (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (1920 844 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (1885 179 (:REWRITE ZIP-OPEN))
     (1446 1446 (:TYPE-PRESCRIPTION BITP))
     (1258 238 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (792 19 (:DEFINITION ASH**))
     (366 366
          (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (360 109 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (352 32 (:REWRITE ASH-0))
     (330 330 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (259 111 (:REWRITE FOLD-CONSTS-IN-+))
     (245 4 (:REWRITE BFIX-WHEN-NOT-1))
     (225 225 (:REWRITE DEFAULT-<-2))
     (225 225 (:REWRITE DEFAULT-<-1))
     (225 4 (:REWRITE EQUAL-1-OF-BOOL->BIT))
     (205 103
          (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
     (191 191 (:REWRITE DEFAULT-+-2))
     (191 191 (:REWRITE DEFAULT-+-1))
     (165 55 (:REWRITE ZP-WHEN-GT-0))
     (111 6 (:REWRITE BOOL->BIT-OF-NOT))
     (110 55
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (110 55
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (110 55
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NEGP))
     (110 55
          (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
     (105 3 (:REWRITE BITOPS::B-NOT-B-NOT))
     (92 92 (:TYPE-PRESCRIPTION ZIP))
     (76 76
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (66 39 (:REWRITE DEFAULT-*-2))
     (60 10 (:REWRITE COMMUTATIVITY-2-OF-+))
     (55 55 (:TYPE-PRESCRIPTION POSP))
     (55 55 (:TYPE-PRESCRIPTION NEGP))
     (48 39 (:REWRITE DEFAULT-*-1))
     (40 19 (:REWRITE NATP-WHEN-INTEGERP))
     (40 10
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (32 32 (:REWRITE ASH-GOES-TO-0))
     (27 9 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (24 4
         (:REWRITE BITOPS::LOGCDR-OF-LEFT-SHIFT))
     (23 23 (:REWRITE DEFAULT-UNARY-MINUS))
     (20 14 (:REWRITE DEFAULT-CDR))
     (20 14 (:REWRITE DEFAULT-CAR))
     (18 9 (:DEFINITION BIT->BOOL$INLINE))
     (13 7 (:REWRITE NFIX-WHEN-NOT-NATP))
     (12 6 (:REWRITE UNICITY-OF-0))
     (8 8 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (8 4
        (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BITP))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (8 4 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (6 1 (:REWRITE O-INFP->NEQ-0))
     (3 3 (:TYPE-PRESCRIPTION O-FINP))
     (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
     (3 1 (:REWRITE BITOPS::LOGCDR-OF-LOGCONS))
     (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(RP::LEMMA1 (34 34 (:REWRITE DEFAULT-<-2))
            (34 34 (:REWRITE DEFAULT-<-1))
            (22 11 (:REWRITE NATP-WHEN-INTEGERP))
            (22 2 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
            (20 20
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (18 6 (:REWRITE ZP-WHEN-GT-0))
            (18 2 (:REWRITE LOGTAIL-IDENTITY))
            (12 12 (:TYPE-PRESCRIPTION BITP))
            (12 2 (:DEFINITION UNSIGNED-BYTE-P))
            (10 2 (:DEFINITION INTEGER-RANGE-P))
            (9 3
               (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
            (9 3
               (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
            (9 3 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
            (6 6 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
            (6 6 (:REWRITE DEFAULT-+-2))
            (6 6 (:REWRITE DEFAULT-+-1))
            (3 3
               (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
            (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
            (2 2
               (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
            (1 1
               (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)))
(RP::LEMMA2 (23 23 (:REWRITE DEFAULT-<-2))
            (23 23 (:REWRITE DEFAULT-<-1))
            (22 11 (:REWRITE NATP-WHEN-INTEGERP))
            (20 20
                (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
            (14 5 (:REWRITE DEFAULT-+-1))
            (12 4 (:REWRITE ZP-WHEN-GT-0))
            (8 5 (:REWRITE DEFAULT-+-2))
            (6 3
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (6 3 (:REWRITE O-INFP->NEQ-0))
            (5 4 (:REWRITE DEFAULT-CDR))
            (5 4 (:REWRITE DEFAULT-CAR))
            (3 3
               (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
            (3 3
               (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)))
(RP::SUM-LST-OF-GET-COL-IS-SUM-BY-COL
     (4072 343
           (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (3885 50 (:DEFINITION BITMASKP**))
     (1022 496
           (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (781 290
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (669 321 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (572 572 (:TYPE-PRESCRIPTION BITP))
     (537 53 (:REWRITE ZIP-OPEN))
     (518 110 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (488 488
          (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (145 145
          (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (132 132 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (112 83 (:REWRITE DEFAULT-+-1))
     (109 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (94 83 (:REWRITE DEFAULT-+-2))
     (89 45 (:REWRITE FOLD-CONSTS-IN-+))
     (68 68 (:REWRITE DEFAULT-<-2))
     (68 68 (:REWRITE DEFAULT-<-1))
     (57 19 (:REWRITE ZP-WHEN-GT-0))
     (36 6 (:REWRITE COMMUTATIVITY-2-OF-+))
     (31 31 (:TYPE-PRESCRIPTION ZIP))
     (24 6
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (20 20
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (16 8 (:REWRITE NATP-WHEN-INTEGERP))
     (12 3
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (9 5 (:REWRITE DEFAULT-CDR))
     (9 5 (:REWRITE DEFAULT-CAR))
     (8 8 (:TYPE-PRESCRIPTION BITP-OF-B-AND))
     (7 7
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
     (3 3
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (3 3
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (2 1 (:REWRITE O-INFP->NEQ-0)))
(RP::SUM-PPS-BY-COL2 (19 10 (:REWRITE DEFAULT-+-1))
                     (16 10 (:REWRITE DEFAULT-+-2))
                     (15 9
                         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (13 4 (:REWRITE DEFAULT-UNARY-MINUS))
                     (9 9
                        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                     (7 3 (:REWRITE NFIX-WHEN-NOT-NATP))
                     (6 6
                        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                     (5 5 (:TYPE-PRESCRIPTION NATP))
                     (4 4 (:REWRITE DEFAULT-<-2))
                     (4 4 (:REWRITE DEFAULT-<-1))
                     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
                     (4 2 (:REWRITE NATP-WHEN-GTE-0))
                     (3 3 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
                     (3 3
                        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                     (3 1 (:REWRITE ZP-WHEN-INTEGERP))
                     (3 1 (:REWRITE ZP-WHEN-GT-0))
                     (3 1 (:REWRITE O<=-O-FINP-DEF))
                     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
                     (2 1
                        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                     (1 1 (:REWRITE O-INFP-O-FINP-O<=))
                     (1 1 (:REWRITE AC-<)))
(RP::SUM-PPS-BY-COL-OF-NIL
     (1522 8 (:REWRITE LOGHEAD-IDENTITY))
     (941 18 (:DEFINITION UNSIGNED-BYTE-P**))
     (878 428
          (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (713 16 (:DEFINITION UNSIGNED-BYTE-P))
     (680 43 (:DEFINITION LOGBITP**))
     (670 36 (:REWRITE UNSIGNED-BYTE-P-PLUS))
     (663 14 (:DEFINITION INTEGER-RANGE-P))
     (248 2 (:REWRITE BFIX-WHEN-NOT-1))
     (220 101
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (190 34 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (186 186 (:TYPE-PRESCRIPTION BITP))
     (141 141
          (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (114 81 (:REWRITE DEFAULT-<-2))
     (110 110 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (100 81 (:REWRITE DEFAULT-<-1))
     (54 54
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (53 27 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (51 17 (:REWRITE ZP-WHEN-GT-0))
     (50 50
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (35 32 (:REWRITE DEFAULT-+-2))
     (35 32 (:REWRITE DEFAULT-+-1))
     (34 2 (:LINEAR LOGHEAD-LEQ))
     (32 32 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (18 5 (:REWRITE NATP-WHEN-INTEGERP))
     (12 12
         (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (10 10 (:TYPE-PRESCRIPTION ZIP))
     (8 8
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (6 6 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (6 2
        (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
     (4 2
        (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
     (4 2 (:REWRITE BFIX-WHEN-NOT-BITP))
     (4 2 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (4 2 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
     (1 1
        (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT)))
(RP::STRIP-LOGCARS-OF-STRIP-LOGTAIL-IS-STRIP-LOGBITS
     (1455 54
           (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (1420 11 (:DEFINITION BITMASKP**))
     (1335 9 (:REWRITE LOGTAIL-IDENTITY))
     (1272 5 (:DEFINITION LOGTAIL**))
     (895 16 (:DEFINITION UNSIGNED-BYTE-P**))
     (754 14 (:DEFINITION LOGBITP**))
     (697 16 (:DEFINITION UNSIGNED-BYTE-P))
     (651 14 (:DEFINITION INTEGER-RANGE-P))
     (649 310
          (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (567 1 (:REWRITE BITOPS::LOGCDR-OF-LOGTAIL))
     (515 32 (:REWRITE UNSIGNED-BYTE-P-PLUS))
     (276 276 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
     (272 23 (:REWRITE BIT->BOOL-OF-BOOL->BIT))
     (249 35 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (175 11 (:REWRITE ZIP-OPEN))
     (170 26 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (156 156 (:TYPE-PRESCRIPTION BITP))
     (156 39
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (135 135
          (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (109 76 (:REWRITE DEFAULT-<-1))
     (104 104
          (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (104 76 (:REWRITE DEFAULT-<-2))
     (102 102 (:TYPE-PRESCRIPTION LOGBITP))
     (94 94 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (92 40 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (79 20 (:REWRITE ZP-WHEN-INTEGERP))
     (60 20 (:REWRITE ZP-WHEN-GT-0))
     (51 51
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (51 51
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (49 1 (:REWRITE LOGTAIL-EQUAL-0))
     (47 47
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (40 19 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (40 19 (:REWRITE IFIX-WHEN-INTEGERP))
     (35 35
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (28 28 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (28 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (27 27 (:REWRITE DEFAULT-+-2))
     (27 27 (:REWRITE DEFAULT-+-1))
     (26 13
         (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
     (17 5 (:REWRITE FOLD-CONSTS-IN-+))
     (16 16
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (15 14 (:REWRITE DEFAULT-CAR))
     (15 5 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (12 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (11 10 (:REWRITE DEFAULT-CDR))
     (9 3 (:LINEAR LOGTAIL-LEQ))
     (8 8 (:TYPE-PRESCRIPTION IFIX))
     (8 4 (:REWRITE NEGP-WHEN-INTEGERP))
     (8 4 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (4 4 (:TYPE-PRESCRIPTION NEGP))
     (4 2 (:DEFINITION BIT->BOOL$INLINE))
     (3 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (2 2 (:TYPE-PRESCRIPTION LOGCAR-TYPE)))
(RP::STRIP-LOGCDRS-STRIP-LOGTAIL-IS-STRIP-LOGTAIL
     (3784 20 (:REWRITE LOGTAIL-IDENTITY))
     (2542 32 (:DEFINITION UNSIGNED-BYTE-P**))
     (2070 33 (:DEFINITION UNSIGNED-BYTE-P))
     (1977 28 (:DEFINITION INTEGER-RANGE-P))
     (1838 797
           (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (1286 64 (:REWRITE UNSIGNED-BYTE-P-PLUS))
     (719 719 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
     (584 68 (:REWRITE BITOPS::LOGCDR-<-CONST))
     (528 47 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (261 261
          (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (246 118 (:REWRITE DEFAULT-<-1))
     (198 198 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
     (174 118 (:REWRITE DEFAULT-<-2))
     (139 50 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (139 50 (:REWRITE IFIX-WHEN-INTEGERP))
     (112 28 (:REWRITE ZP-WHEN-INTEGERP))
     (94 94 (:TYPE-PRESCRIPTION BITP))
     (92 92
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (89 89
         (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (89 89
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (84 28 (:REWRITE ZP-WHEN-GT-0))
     (84 12 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (56 56 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (50 50
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (43 43 (:REWRITE DEFAULT-+-2))
     (43 43 (:REWRITE DEFAULT-+-1))
     (36 12 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (24 24 (:TYPE-PRESCRIPTION IFIX))
     (24 12 (:REWRITE NEGP-WHEN-INTEGERP))
     (20 19 (:REWRITE DEFAULT-CAR))
     (12 12 (:TYPE-PRESCRIPTION NEGP))
     (12 11 (:REWRITE DEFAULT-CDR))
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (8 4 (:REWRITE NATP-WHEN-INTEGERP))
     (5 5
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (1 1 (:REWRITE NFIX-WHEN-NOT-NATP)))
(RP::SUM-PPS-BY-COL2-IS-SUM-PPS-BY-COL
     (292 114 (:REWRITE DEFAULT-+-1))
     (251 114 (:REWRITE DEFAULT-+-2))
     (250 26 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (188 6 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (104 104 (:TYPE-PRESCRIPTION BITP))
     (83 34
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (83 34 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (73 57 (:REWRITE FOLD-CONSTS-IN-+))
     (62 34
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (57 19 (:REWRITE NATP-WHEN-GTE-0))
     (48 48
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (38 19 (:REWRITE NATP-WHEN-INTEGERP))
     (36 36 (:REWRITE DEFAULT-<-2))
     (36 36 (:REWRITE DEFAULT-<-1))
     (34 34
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (28 28 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (24 8 (:REWRITE ZP-WHEN-GT-0))
     (22 22
         (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 4 (:REWRITE DEFAULT-CAR))
     (3 3 (:REWRITE DEFAULT-CDR)))
(RP::STUPID-LEMMA1)
(RP::SUM-PPS-BYCOL-BYBIT-IS-SUM-BY-COL-OF-CREATE-PPS
     (150 15 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (136 11
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (136 11 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (120 79 (:REWRITE DEFAULT-+-2))
     (100 79 (:REWRITE DEFAULT-+-1))
     (58 58 (:TYPE-PRESCRIPTION BITP))
     (54 6 (:REWRITE COMMUTATIVITY-2-OF-+))
     (36 12 (:REWRITE NATP-WHEN-GTE-0))
     (30 18 (:REWRITE FOLD-CONSTS-IN-+))
     (29 29 (:REWRITE DEFAULT-<-2))
     (29 29 (:REWRITE DEFAULT-<-1))
     (29 11
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (24 12 (:REWRITE NATP-WHEN-INTEGERP))
     (24 8 (:REWRITE ZP-WHEN-GT-0))
     (24 6
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (21 21
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 18 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
     (11 11
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL)))
(RP::SUM-PPS-BYCOL-BYBIT-IS-SUM-PPS-BY-COL
     (12 4 (:REWRITE NATP-WHEN-GTE-0))
     (8 4 (:REWRITE NATP-WHEN-INTEGERP))
     (7 7
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::STRIP-LOGTAIL-OF-0 (9 9 (:REWRITE DEFAULT-CAR))
                        (8 8
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (5 5 (:REWRITE DEFAULT-CDR))
                        (5 3 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(RP::MULT-BYCOL-BYBIT-SPEC-MULT-BYCOL-SPEC
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(RP::LOGHEAD-OF-*-IS-MULT-BYCOL-BYBIT-SPEC
     (52 4 (:REWRITE LOGHEAD-IDENTITY))
     (42 3 (:DEFINITION UNSIGNED-BYTE-P))
     (33 3 (:DEFINITION INTEGER-RANGE-P))
     (15 9 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (9 9 (:REWRITE DEFAULT-<-1))
     (6 2 (:LINEAR LOGHEAD-LEQ))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP)))
(RP::SUM-COL-BYBIT-SIMPLE (2 2
                             (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)))
(RP::INTEGERP-OF-SUM-COL-BYBIT-SIMPLE
     (1 1
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)))
(RP::SUM-PPS-BYCOL-BYBIT-SIMPLE
     (44 33 (:REWRITE DEFAULT-+-1))
     (41 33 (:REWRITE DEFAULT-+-2))
     (30 1
         (:DEFINITION RP::SUM-PPS-BYCOL-BYBIT-SIMPLE))
     (21 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (15 15 (:REWRITE DEFAULT-<-2))
     (15 15 (:REWRITE DEFAULT-<-1))
     (15 9
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 6 (:REWRITE ZP-WHEN-GT-0))
     (11 11
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9
        (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (7 5 (:REWRITE FOLD-CONSTS-IN-+))
     (7 3 (:REWRITE NFIX-WHEN-NOT-NATP))
     (7 3 (:REWRITE NATP-WHEN-INTEGERP))
     (6 6
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 3 (:REWRITE RP::STUPID-LEMMA1))
     (3 3 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
     (3 1 (:REWRITE O<=-O-FINP-DEF))
     (2 2
        (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
     (1 1 (:REWRITE O-INFP-O-FINP-O<=))
     (1 1 (:REWRITE AC-<)))
(RP::INTEGERP-OF-SUM-PPS-BYCOL-BYBIT-SIMPLE)
(RP::MULT-FINAL-SPEC)
(RP::SUM-COL-BYBIT2 (7 4 (:REWRITE DEFAULT-<-1))
                    (7 3 (:REWRITE NFIX-WHEN-NOT-NATP))
                    (4 4 (:REWRITE DEFAULT-<-2))
                    (4 2 (:REWRITE NATP-WHEN-GTE-0))
                    (3 2 (:REWRITE NATP-WHEN-INTEGERP))
                    (3 1 (:REWRITE ZP-WHEN-GT-0))
                    (3 1 (:REWRITE O<=-O-FINP-DEF))
                    (2 2
                       (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
                    (2 2
                       (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                    (2 1 (:REWRITE ZP-WHEN-INTEGERP))
                    (2 1
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                    (1 1 (:REWRITE ZP-OPEN))
                    (1 1
                       (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
                    (1 1 (:REWRITE O-INFP-O-FINP-O<=))
                    (1 1 (:REWRITE DEFAULT-+-2))
                    (1 1 (:REWRITE DEFAULT-+-1))
                    (1 1
                       (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
                    (1 1 (:REWRITE AC-<)))
(RP::INTEGERP-OF-SUM-COL-BYBIT2
     (1 1
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)))
(RP::|(< (+ -1 col-index) (+ -1 shift-amount))|
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (3 3 (:REWRITE CONSTANT-<-INTEGERP))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< c (- x))|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3 3
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(RP::SUM-COL-BYBIT-SHIFT-AMOUNT+1
     (32 29 (:REWRITE DEFAULT-+-2))
     (32 29 (:REWRITE DEFAULT-+-1))
     (30 3 (:REWRITE LOGTAIL-IDENTITY))
     (21 7
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (21 3 (:DEFINITION UNSIGNED-BYTE-P))
     (18 18 (:REWRITE DEFAULT-<-2))
     (18 18 (:REWRITE DEFAULT-<-1))
     (18 6
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (18 3 (:DEFINITION INTEGER-RANGE-P))
     (16 16 (:TYPE-PRESCRIPTION BITP))
     (14 14 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 4 (:REWRITE ZP-WHEN-GT-0))
     (11 1 (:REWRITE BITOPS::LOGTAIL-OF-LOGTAIL))
     (10 4 (:REWRITE ZP-WHEN-INTEGERP))
     (8 1 (:REWRITE BITOPS::LOGBITP-OF-LOGTAIL))
     (7 7
        (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (6 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (3 3 (:TYPE-PRESCRIPTION BITP-OF-B-AND))
     (3 3 (:REWRITE ZP-OPEN))
     (3 3
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (3 3 (:REWRITE DEFAULT-UNARY-MINUS)))
(RP::SUM-COL-BYBIT-IS-SUM-COL-BYBIT2
     (74 10 (:REWRITE LOGTAIL-IDENTITY))
     (54 18
         (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (48 8 (:DEFINITION UNSIGNED-BYTE-P))
     (42 14
         (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (41 41 (:REWRITE DEFAULT-<-2))
     (41 41 (:REWRITE DEFAULT-<-1))
     (40 8 (:DEFINITION INTEGER-RANGE-P))
     (37 30 (:REWRITE DEFAULT-+-2))
     (37 30 (:REWRITE DEFAULT-+-1))
     (36 36 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (34 34 (:TYPE-PRESCRIPTION BITP))
     (21 7 (:REWRITE ZP-WHEN-GT-0))
     (18 18
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (9 9
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
     (9 3 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (8 8
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (7 7 (:TYPE-PRESCRIPTION BITP-OF-B-AND))
     (2 1
        (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP)))
(RP::SUM-COL-BYBIT2-IS-SUM-COL-BYBIT-SIMPLE
     (181 63
          (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (148 52
          (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (146 146 (:TYPE-PRESCRIPTION BITP))
     (138 18 (:REWRITE LOGTAIL-IDENTITY))
     (118 118
          (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (90 15 (:DEFINITION UNSIGNED-BYTE-P))
     (79 29 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (75 15 (:DEFINITION INTEGER-RANGE-P))
     (67 67 (:REWRITE DEFAULT-<-2))
     (67 67 (:REWRITE DEFAULT-<-1))
     (66 44 (:REWRITE DEFAULT-+-2))
     (65 44 (:REWRITE DEFAULT-+-1))
     (63 63
         (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
     (50 5 (:REWRITE BITOPS::LOGTAIL-OF-LOGTAIL))
     (30 10 (:REWRITE ZP-WHEN-GT-0))
     (18 18
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (18 6 (:REWRITE FOLD-CONSTS-IN-+))
     (15 15
         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (8 8
        (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
     (2 1
        (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE BITOPS::B-AND-EQUAL-0-IN-CONCL)))
(RP::SUM-PPS-BYCOL-BYBIT-SIMPLE-IS-SUM-PPS-BYCOL-BYBIT
     (99 71 (:REWRITE DEFAULT-+-2))
     (93 71 (:REWRITE DEFAULT-+-1))
     (45 5 (:REWRITE COMMUTATIVITY-2-OF-+))
     (25 15 (:REWRITE FOLD-CONSTS-IN-+))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (21 7 (:REWRITE ZP-WHEN-GT-0))
     (20 5
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (18 6 (:REWRITE NATP-WHEN-GTE-0))
     (15 10
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 12
         (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (12 6 (:REWRITE NATP-WHEN-INTEGERP))
     (10 10
         (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (10 10
         (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
     (5 5 (:TYPE-PRESCRIPTION FLOOR))
     (5 5
        (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
     (4 4
        (:TYPE-PRESCRIPTION RP::SUM-COL-BYBIT2)))
(RP::MULT-FINAL-SPEC-MULT-BYCOL-BYBIT-SPEC
     (6 2 (:REWRITE NATP-WHEN-GTE-0))
     (4 4
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (4 2 (:REWRITE NATP-WHEN-INTEGERP))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(RP::LOGHEAD-OF-*-IS-MULT-FINAL-SPEC
     (52 4 (:REWRITE LOGHEAD-IDENTITY))
     (42 3 (:DEFINITION UNSIGNED-BYTE-P))
     (33 3 (:DEFINITION INTEGER-RANGE-P))
     (15 9 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
     (9 9 (:REWRITE DEFAULT-<-1))
     (6 2 (:LINEAR LOGHEAD-LEQ))
     (4 4 (:REWRITE DEFAULT-*-2))
     (4 4 (:REWRITE DEFAULT-*-1))
     (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
     (3 3
        (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
     (3 3
        (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2
        (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
     (2 1 (:REWRITE NATP-WHEN-INTEGERP)))
