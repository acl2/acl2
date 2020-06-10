(ACL2S::ALLP)
(ACL2S::ALLP-ALIASES-TABLE)
(ACL2S::CONS-CONSTRUCTOR-PRED)
(ACL2S::CONS-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::CONS-ELIM-RULE (1 1 (:REWRITE DEFAULT-CDR))
                       (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CONSTRUCTOR-DESTRUCTORS-PROPER)
(ACL2S::INTERN$-CONSTRUCTOR-PRED)
(ACL2S::INTERN$-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::/-CONSTRUCTOR-PRED)
(ACL2S::/-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::COMPLEX-CONSTRUCTOR-PRED)
(ACL2S::COMPLEX-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::COMPLEX-ELIM-RULE (1 1
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (1 1 (:REWRITE DEFAULT-REALPART))
                          (1 1 (:REWRITE DEFAULT-IMAGPART))
                          (1 1 (:REWRITE DEFAULT-COMPLEX-2))
                          (1 1 (:REWRITE DEFAULT-COMPLEX-1)))
(ACL2S::COMPLEX-CONSTRUCTOR-DESTRUCTORS-PROPER
     (2 2 (:REWRITE DEFAULT-COMPLEX-2))
     (2 2 (:REWRITE DEFAULT-COMPLEX-1))
     (1 1 (:REWRITE DEFAULT-REALPART))
     (1 1 (:REWRITE DEFAULT-IMAGPART)))
(ACL2S::INTEGERP-MOD (32 2
                         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                     (14 9 (:REWRITE DEFAULT-+-2))
                     (10 9 (:REWRITE DEFAULT-+-1))
                     (8 5 (:REWRITE DEFAULT-UNARY-MINUS))
                     (6 2 (:DEFINITION NFIX))
                     (5 5 (:REWRITE DEFAULT-<-2))
                     (5 5 (:REWRITE DEFAULT-<-1))
                     (5 3 (:REWRITE DEFAULT-*-2))
                     (5 3 (:REWRITE DEFAULT-*-1))
                     (2 2 (:DEFINITION IFIX))
                     (1 1 (:REWRITE DEFAULT-UNARY-/))
                     (1 1 (:REWRITE DEFAULT-NUMERATOR))
                     (1 1 (:REWRITE DEFAULT-DENOMINATOR)))
(ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS
     (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (5 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (5 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(ACL2S::GET-CHARACTER-LIST-FROM-POSITIONS
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (299 191 (:REWRITE DEFAULT-TIMES-2))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (218 114 (:REWRITE DEFAULT-PLUS-2))
     (191 191 (:REWRITE DEFAULT-TIMES-1))
     (186 29 (:REWRITE RATIONALP-X))
     (159 3 (:REWRITE CANCEL-MOD-+))
     (109 40 (:REWRITE INTEGERP-MINUS-X))
     (106 106
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (105 3 (:REWRITE MOD-X-Y-=-X . 4))
     (105 3 (:REWRITE MOD-X-Y-=-X . 3))
     (102 82
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (102 82
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (102 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (93 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (82 82
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (82 82
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (82 82
         (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (77 77 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (66 3 (:REWRITE MOD-ZERO . 3))
     (59 29 (:REWRITE DEFAULT-LESS-THAN-1))
     (58 58
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (54 3 (:REWRITE MOD-ZERO . 4))
     (51 6 (:REWRITE |(* (- x) y)|))
     (48 6 (:REWRITE ACL2-NUMBERP-X))
     (37 37 (:REWRITE REDUCE-INTEGERP-+))
     (37 37 (:META META-INTEGERP-CORRECT))
     (33 29 (:REWRITE DEFAULT-LESS-THAN-2))
     (31 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (31 27 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30 (:REWRITE THE-FLOOR-BELOW))
     (30 30 (:REWRITE THE-FLOOR-ABOVE))
     (30 6 (:REWRITE DEFAULT-MINUS))
     (29 29 (:REWRITE RATIONALP-MINUS-X))
     (29 27
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (27 27 (:REWRITE INTEGERP-<-CONSTANT))
     (27 27 (:REWRITE CONSTANT-<-INTEGERP))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< c (- x))|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< (/ x) (/ y))|))
     (27 27 (:REWRITE |(< (- x) c)|))
     (27 27 (:REWRITE |(< (- x) (- y))|))
     (27 6 (:REWRITE |(- (* c x))|))
     (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (16 16 (:REWRITE DEFAULT-CAR))
     (16 16 (:REWRITE |(< (/ x) 0)|))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE MOD-CANCEL-*-CONST))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 3
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (9 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8
        (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (7 7 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE DEFAULT-CDR))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 1
        (:REWRITE ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(ACL2S::GET-STANDARD-CHAR-LIST-FROM-POSITIONS
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (474 474
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (299 191 (:REWRITE DEFAULT-TIMES-2))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (223 223
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (218 114 (:REWRITE DEFAULT-PLUS-2))
     (191 191 (:REWRITE DEFAULT-TIMES-1))
     (186 29 (:REWRITE RATIONALP-X))
     (159 3 (:REWRITE CANCEL-MOD-+))
     (109 40 (:REWRITE INTEGERP-MINUS-X))
     (106 106
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (105 3 (:REWRITE MOD-X-Y-=-X . 4))
     (105 3 (:REWRITE MOD-X-Y-=-X . 3))
     (102 82
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (102 82
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (102 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (93 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (82 82 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (82 82
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (82 82
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (82 82
         (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (77 77 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (66 3 (:REWRITE MOD-ZERO . 3))
     (59 29 (:REWRITE DEFAULT-LESS-THAN-1))
     (58 58
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (54 3 (:REWRITE MOD-ZERO . 4))
     (51 6 (:REWRITE |(* (- x) y)|))
     (48 6 (:REWRITE ACL2-NUMBERP-X))
     (37 37 (:REWRITE REDUCE-INTEGERP-+))
     (37 37 (:META META-INTEGERP-CORRECT))
     (33 29 (:REWRITE DEFAULT-LESS-THAN-2))
     (31 27
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (31 27 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30 (:REWRITE THE-FLOOR-BELOW))
     (30 30 (:REWRITE THE-FLOOR-ABOVE))
     (30 6 (:REWRITE DEFAULT-MINUS))
     (29 29 (:REWRITE RATIONALP-MINUS-X))
     (29 27
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 27
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (27 27
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (27 27 (:REWRITE INTEGERP-<-CONSTANT))
     (27 27 (:REWRITE CONSTANT-<-INTEGERP))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< c (- x))|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (27 27
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (27 27 (:REWRITE |(< (/ x) (/ y))|))
     (27 27 (:REWRITE |(< (- x) c)|))
     (27 27 (:REWRITE |(< (- x) (- y))|))
     (27 6 (:REWRITE |(- (* c x))|))
     (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (17 17 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (16 16 (:REWRITE DEFAULT-CAR))
     (16 16 (:REWRITE |(< (/ x) 0)|))
     (16 16 (:REWRITE |(< (* x y) 0)|))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (15 3 (:REWRITE MOD-X-Y-=-X . 2))
     (15 3
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (15 3 (:REWRITE MOD-CANCEL-*-CONST))
     (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 3
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (15 3
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (9 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (8 8
        (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (7 7 (:REWRITE DEFAULT-MOD-2))
     (7 7 (:REWRITE |(+ c (+ d x))|))
     (6 6 (:REWRITE DEFAULT-CDR))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|))
     (4 1
        (:REWRITE ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
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
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
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
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE MOD-NEGATIVE . 3))
     (1 1 (:REWRITE MOD-NEGATIVE . 2))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE |(< y (+ (- c) x))|))
     (1 1 (:REWRITE |(< x (+ c/d y))|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(ACL2S::GET-CHARACTER-LIST-FROM-POSITIONS--CHARACTER-LISTP
     (2446 22 (:REWRITE DEFAULT-MOD-1))
     (2360 16 (:REWRITE DEFAULT-MOD-RATIO))
     (2102 8 (:DEFINITION NTH))
     (1134 8 (:REWRITE ZP-OPEN))
     (558 12 (:REWRITE |(< x (if a b c))|))
     (530 10 (:REWRITE CANCEL-MOD-+))
     (444 26 (:REWRITE DEFAULT-PLUS-2))
     (432 12 (:REWRITE |(+ x (if a b c))|))
     (406 406
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (406 406
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (406 406
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (406 406
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (350 10 (:REWRITE MOD-X-Y-=-X . 4))
     (330 10 (:REWRITE MOD-X-Y-=-X . 3))
     (321 91 (:REWRITE INTEGERP-MINUS-X))
     (310 10 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (300 60 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (300 60
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (300 60
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (288 36 (:REWRITE RATIONALP-X))
     (252 36 (:REWRITE REDUCE-RATIONALP-*))
     (241 61 (:REWRITE DEFAULT-LESS-THAN-2))
     (224 10 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (220 10 (:REWRITE MOD-ZERO . 3))
     (208 52 (:REWRITE |(* y x)|))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (200 200
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (194 146 (:REWRITE DEFAULT-TIMES-2))
     (184 8 (:REWRITE MOD-POSITIVE . 1))
     (180 10 (:REWRITE MOD-ZERO . 4))
     (170 20 (:REWRITE |(* (- x) y)|))
     (146 146 (:REWRITE DEFAULT-TIMES-1))
     (108 12 (:REWRITE ACL2-NUMBERP-X))
     (100 20 (:REWRITE DEFAULT-MINUS))
     (90 20 (:REWRITE |(- (* c x))|))
     (81 81 (:REWRITE REDUCE-INTEGERP-+))
     (81 81 (:META META-INTEGERP-CORRECT))
     (72 72
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (69 69 (:REWRITE THE-FLOOR-BELOW))
     (69 69 (:REWRITE THE-FLOOR-ABOVE))
     (61 61 (:REWRITE DEFAULT-LESS-THAN-1))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (60 60 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (60 60
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (60 60
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (60 60 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (50 10 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (50 10 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (50 10 (:REWRITE MOD-X-Y-=-X . 2))
     (50 10 (:REWRITE MOD-CANCEL-*-CONST))
     (50 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (50 10
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (49 49 (:REWRITE SIMPLIFY-SUMS-<))
     (49 49
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (49 49
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (49 49
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (49 49
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (49 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (49 49 (:REWRITE INTEGERP-<-CONSTANT))
     (49 49 (:REWRITE CONSTANT-<-INTEGERP))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< c (- x))|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (49 49
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (49 49 (:REWRITE |(< (/ x) (/ y))|))
     (49 49 (:REWRITE |(< (- x) c)|))
     (49 49 (:REWRITE |(< (- x) (- y))|))
     (44 2 (:LINEAR MOD-BOUNDS-3))
     (42 42
         (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
     (42 10
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (42 10
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (36 36 (:REWRITE RATIONALP-MINUS-X))
     (27 25 (:REWRITE DEFAULT-CAR))
     (26 26 (:REWRITE DEFAULT-PLUS-1))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:META META-RATIONALP-CORRECT))
     (23 21 (:REWRITE DEFAULT-CDR))
     (22 22 (:REWRITE DEFAULT-MOD-2))
     (20 4 (:LINEAR MOD-BOUNDS-2))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (19 19 (:REWRITE |(< (/ x) 0)|))
     (19 19 (:REWRITE |(< (* x y) 0)|))
     (18 10
         (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (18 10
         (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (16 16 (:REWRITE |(< 0 (/ x))|))
     (16 16 (:REWRITE |(< 0 (* x y))|))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE |(* a (/ a) b)|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (10 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(mod x (- y))| . 3))
     (10 10 (:REWRITE |(mod x (- y))| . 2))
     (10 10 (:REWRITE |(mod x (- y))| . 1))
     (10 10
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (10 10
         (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (10 10 (:REWRITE |(mod (- x) y)| . 3))
     (10 10 (:REWRITE |(mod (- x) y)| . 2))
     (10 10 (:REWRITE |(mod (- x) y)| . 1))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE MOD-POSITIVE . 3))
     (8 8 (:REWRITE MOD-POSITIVE . 2)))
(ACL2S::NTH-BOOLEAN-BUILTIN)
(ACL2S::NTH-NAT-BUILTIN (1 1
                           (:TYPE-PRESCRIPTION ACL2S::NTH-NAT-BUILTIN)))
(ACL2S::NAT-INDEX (1 1
                     (:TYPE-PRESCRIPTION ACL2S::NAT-INDEX)))
(ACL2S::NTH-POS-BUILTIN)
(ACL2S::NTH-POS-BUILTIN-GUARD-IMPLIES-TEST)
(ACL2S::NTH-POS-BUILTIN)
(ACL2S::NTH-POS-BUILTIN-IS-POSP (1 1 (:REWRITE DEFAULT-<-2))
                                (1 1 (:REWRITE DEFAULT-<-1))
                                (1 1 (:REWRITE DEFAULT-+-2))
                                (1 1 (:REWRITE DEFAULT-+-1)))
(ACL2S::POS-INDEX)
(ACL2S::POS-INDEX-GUARD-IMPLIES-TEST)
(ACL2S::POS-INDEX)
(ACL2S::NEGP)
(ACL2S::NTH-NEG-BUILTIN)
(ACL2S::NON-POS-INTEGERP)
(ACL2S::NTH-NON-POS-INTEGER-BUILTIN)
(ACL2S::NON-0-INTEGERP)
(ACL2S::NTH-NON-0-INTEGER-BUILTIN)
(ACL2S::NTH-INTEGER-BUILTIN)
(ACL2S::SIMPLE-HASH (5 5
                       (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-INTEGER-BETWEEN (3 3 (:REWRITE DEFAULT-<-2))
                            (3 3 (:REWRITE DEFAULT-<-1))
                            (2 2 (:REWRITE DEFAULT-+-2))
                            (2 2 (:REWRITE DEFAULT-+-1))
                            (2 2 (:REWRITE DEFAULT-*-2))
                            (2 2 (:REWRITE DEFAULT-*-1))
                            (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                            (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(ACL2S::BITSIZE-AUX
     (680 3 (:REWRITE O<=-O-FINP-DEF))
     (231 7 (:REWRITE |(< (+ (- c) x) y)|))
     (186 18 (:REWRITE SIMPLIFY-SUMS-<))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (160 160
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (153 153
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (153 153
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (153 153
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (153 153
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (116 41 (:REWRITE DEFAULT-LESS-THAN-1))
     (103 27
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (86 20
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (66 43 (:REWRITE DEFAULT-PLUS-1))
     (65 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (57 43 (:REWRITE DEFAULT-PLUS-2))
     (56 56 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (56 56
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (56 56
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (56 56
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (56 56
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (56 26 (:REWRITE NORMALIZE-ADDENDS))
     (56 4 (:REWRITE |(+ y (+ x z))|))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (45 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (41 41 (:REWRITE THE-FLOOR-BELOW))
     (41 41 (:REWRITE THE-FLOOR-ABOVE))
     (41 41 (:REWRITE DEFAULT-LESS-THAN-2))
     (37 37 (:REWRITE DEFAULT-TIMES-2))
     (37 37 (:REWRITE DEFAULT-TIMES-1))
     (30 1 (:REWRITE O-FIRST-EXPT-<))
     (29 27
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 27
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (29 3 (:REWRITE O-INFP-O-FINP-O<=))
     (29 3 (:REWRITE AC-<))
     (28 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (25 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (25 5
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (22 22
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
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
     (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 5 (:REWRITE |(* y x)|))
     (19 19
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (14 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (14 2 (:REWRITE |(* y (* x z))|))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 4 (:REWRITE DEFAULT-MINUS))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 8 (:DEFINITION FIX))
     (8 2 (:REWRITE |(+ c (+ d x))|))
     (8 2 (:REWRITE |(+ (- x) (* c x))|))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (4 4 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(* a (/ a))|))
     (3 3 (:REWRITE |a < b & b < c  =>  a < c|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (2 2
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (2 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (2 2 (:REWRITE |(+ x (- x))|))
     (2 2 (:REWRITE |(+ 0 x)|))
     (2 2 (:REWRITE |(* 1 x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE O-FIRST-COEFF-<))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::BITSIZE-AUX-POSP
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (280 280
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (104 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (72 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (66 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (48 46 (:REWRITE DEFAULT-LESS-THAN-2))
     (46 46 (:REWRITE THE-FLOOR-BELOW))
     (46 46 (:REWRITE THE-FLOOR-ABOVE))
     (46 46 (:REWRITE DEFAULT-LESS-THAN-1))
     (46 45
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (46 45
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (45 45 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (45 45
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (45 45
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (45 45 (:REWRITE INTEGERP-<-CONSTANT))
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
     (42 40
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (42 40 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (40 40 (:REWRITE SIMPLIFY-SUMS-<))
     (40 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (40 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (40 8
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (36 36 (:REWRITE DEFAULT-TIMES-2))
     (36 36 (:REWRITE DEFAULT-TIMES-1))
     (33 33 (:REWRITE REDUCE-INTEGERP-+))
     (33 33 (:REWRITE INTEGERP-MINUS-X))
     (33 33 (:META META-INTEGERP-CORRECT))
     (28 28
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 6 (:REWRITE |(* y x)|))
     (17 17 (:REWRITE |(< (/ x) 0)|))
     (17 17 (:REWRITE |(< (* x y) 0)|))
     (16 16
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (16 16 (:REWRITE NORMALIZE-ADDENDS))
     (16 16 (:REWRITE DEFAULT-PLUS-2))
     (16 16 (:REWRITE DEFAULT-PLUS-1))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (15 15
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (15 15 (:REWRITE |(< 0 (/ x))|))
     (15 15 (:REWRITE |(< 0 (* x y))|))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-1))
     (6 6 (:REWRITE |(floor x 2)| . 2))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(ACL2S::BITSIZE)
(ACL2S::ROUNDS)
(ACL2S::NTH-INTEGER-BETWEEN-BITS-MID
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1044 1044
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (672 279 (:REWRITE DEFAULT-PLUS-2))
 (632
   632
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (632
  632
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (632
     632
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (632 632
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (564 36 (:REWRITE INTEGERP-MINUS-X))
 (538 279 (:REWRITE DEFAULT-PLUS-1))
 (500 2 (:REWRITE CANCEL-MOD-+))
 (471 55
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (432 432
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (384 30 (:META META-INTEGERP-CORRECT))
 (376 18
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (360 316 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (360 316
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (350 4 (:REWRITE INTEGERP-/))
 (328 8 (:REWRITE DEFAULT-FLOOR-RATIO))
 (242 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (242 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (220 188 (:REWRITE DEFAULT-TIMES-2))
 (220 52 (:REWRITE DEFAULT-MINUS))
 (188 188 (:REWRITE DEFAULT-TIMES-1))
 (184 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (182 30 (:REWRITE REDUCE-INTEGERP-+))
 (180 2 (:REWRITE MOD-X-Y-=-X . 3))
 (167 8 (:REWRITE |(floor (+ x r) i)|))
 (162 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (160 2 (:REWRITE MOD-X-Y-=-X . 2))
 (142 142
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (138 45 (:REWRITE |(< (- x) c)|))
 (109 55 (:REWRITE DEFAULT-LESS-THAN-2))
 (103 103
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (88 2 (:REWRITE MOD-ZERO . 3))
 (85 77 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (85 77 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (85 77
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (85 77
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (77 77 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (77 77
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (77 77 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (77 77
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (77 77 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (76 40
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (76 2 (:REWRITE MOD-X-Y-=-X . 4))
 (75 75
     (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
 (74 6 (:REWRITE |(* (* x y) z)|))
 (57 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 55
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 29 (:REWRITE SIMPLIFY-SUMS-<))
 (55 55 (:REWRITE THE-FLOOR-BELOW))
 (55 55 (:REWRITE THE-FLOOR-ABOVE))
 (55 55 (:REWRITE DEFAULT-LESS-THAN-1))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (50 18 (:REWRITE |(equal (+ (- c) x) y)|))
 (50 2 (:REWRITE DEFAULT-MOD-RATIO))
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
 (45 45 (:REWRITE |(< (- x) (- y))|))
 (43 27 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (42 42
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (42 42 (:REWRITE INTEGERP-<-CONSTANT))
 (42 42 (:REWRITE CONSTANT-<-INTEGERP))
 (40 2 (:REWRITE MOD-ZERO . 4))
 (34 34 (:REWRITE |(* (- x) y)|))
 (24 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (21 21 (:REWRITE |(< (+ c/d x) y)|))
 (18 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (18 18
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(equal (- x) (- y))|))
 (18 18 (:REWRITE |(< x (+ c/d y))|))
 (17 17 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (10 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (10 2 (:REWRITE MOD-CANCEL-*-CONST))
 (10 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (10 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (10 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE DEFAULT-FLOOR-2))
 (8 8 (:REWRITE DEFAULT-FLOOR-1))
 (8 8 (:REWRITE |(floor x 2)| . 2))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(* c (* d x))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (6 6 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(- (- x))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-MOD-1))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(ACL2S::NTH-INTEGER-BETWEEN-BITS-LO
 (459 2 (:REWRITE CANCEL-MOD-+))
 (357 3 (:REWRITE DEFAULT-MOD-RATIO))
 (327 11 (:REWRITE INTEGERP-MINUS-X))
 (299 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (287 2 (:REWRITE MOD-X-Y-=-X . 3))
 (261
   261
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (261
  261
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (261
     261
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (261 261
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (232 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (222 29 (:REWRITE DEFAULT-TIMES-2))
 (204 9 (:META META-INTEGERP-CORRECT))
 (200 101 (:REWRITE DEFAULT-PLUS-2))
 (198 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (189 10
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (175 2 (:REWRITE INTEGERP-/))
 (172 2 (:REWRITE MOD-ZERO . 3))
 (170 8 (:REWRITE |(* (* x y) z)|))
 (146 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (146 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (111 101 (:REWRITE DEFAULT-PLUS-1))
 (105 2 (:REWRITE MOD-X-Y-=-X . 2))
 (87 2 (:REWRITE MOD-X-Y-=-X . 4))
 (83 1 (:REWRITE |(* x (if a b c))|))
 (82 12
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (81 9 (:REWRITE DEFAULT-DIVIDE))
 (70 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 8 (:REWRITE |(< y (+ (- c) x))|))
 (64 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (61 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (54 54 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (51 2 (:REWRITE MOD-ZERO . 4))
 (48 3 (:REWRITE DEFAULT-MOD-2))
 (46 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (46 1 (:REWRITE |(/ (if a b c))|))
 (40 13 (:REWRITE SIMPLIFY-SUMS-<))
 (39 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (39 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (37 27 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (37 27 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (37 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (37 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (32 7 (:REWRITE DEFAULT-MINUS))
 (30 4
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (30 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (29 29 (:REWRITE DEFAULT-TIMES-1))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (28 2 (:LINEAR EXPT->-1-ONE))
 (27 27 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (27 27
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (27 27
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (27 2 (:REWRITE |(- (* c x))|))
 (26 26 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (26 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (24 4 (:REWRITE |(/ (expt x n))|))
 (21 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (21 2 (:REWRITE MOD-CANCEL-*-CONST))
 (21 2
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (21 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (20 20
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (20 20
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20 (:REWRITE INTEGERP-<-CONSTANT))
 (20 20 (:REWRITE CONSTANT-<-INTEGERP))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< c (- x))|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (20 20
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (20 20 (:REWRITE |(< (/ x) (/ y))|))
 (20 20 (:REWRITE |(< (- x) c)|))
 (20 20 (:REWRITE |(< (- x) (- y))|))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (14 14
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (14 12
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (10 10 (:REWRITE |(* c (* d x))|))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (9 9
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (9 9 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE DEFAULT-MOD-1))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(mod (- x) y)| . 3))
 (2 2 (:REWRITE |(mod (- x) y)| . 2))
 (2 2 (:REWRITE |(mod (- x) y)| . 1))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:LINEAR EXPT-X->=-X))
 (2 2 (:LINEAR EXPT-X->-X))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(ACL2S::INTEGER-INDEX)
(ACL2S::NEG-RATIOP)
(ACL2S::BASE-DEFDATA-INSERT
     (2 2 (:REWRITE DEFAULT-CAR))
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
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE DEFAULT-CDR))
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
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::BASE-DEFDATA-ISORT
     (2034 175 (:REWRITE DEFAULT-LESS-THAN-2))
     (882 98 (:REWRITE ACL2-NUMBERP-X))
     (392 98 (:REWRITE RATIONALP-X))
     (175 175 (:REWRITE THE-FLOOR-BELOW))
     (175 175 (:REWRITE THE-FLOOR-ABOVE))
     (163 163 (:REWRITE REDUCE-INTEGERP-+))
     (163 163 (:REWRITE INTEGERP-MINUS-X))
     (163 163 (:META META-INTEGERP-CORRECT))
     (128 119 (:REWRITE DEFAULT-CAR))
     (126 126 (:REWRITE SIMPLIFY-SUMS-<))
     (126 126
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (126 126 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (126 126
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (126 126
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (126 126
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (126 126
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (126 126 (:REWRITE INTEGERP-<-CONSTANT))
     (126 126 (:REWRITE CONSTANT-<-INTEGERP))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< c (- x))|))
     (126 126
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (126 126
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (126 126
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (126 126 (:REWRITE |(< (/ x) (/ y))|))
     (126 126 (:REWRITE |(< (- x) c)|))
     (126 126 (:REWRITE |(< (- x) (- y))|))
     (98 98 (:REWRITE REDUCE-RATIONALP-+))
     (98 98 (:REWRITE REDUCE-RATIONALP-*))
     (98 98 (:REWRITE RATIONALP-MINUS-X))
     (98 98 (:META META-RATIONALP-CORRECT))
     (90 81 (:REWRITE DEFAULT-CDR))
     (78 78
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (78 78
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (78 78 (:REWRITE |(< (/ x) 0)|))
     (78 78 (:REWRITE |(< (* x y) 0)|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (23 23 (:REWRITE |(< 0 (/ x))|))
     (23 23 (:REWRITE |(< 0 (* x y))|)))
(ACL2S::POS-RATIOP)
(ACL2S::NTH-POS-RATIO-BUILTIN (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                              (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B)))
(ACL2S::NTH-NEG-RATIO-BUILTIN)
(ACL2S::NEG-RATIONALP)
(ACL2S::NTH-NEG-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::POS-RATIONALP)
(ACL2S::NTH-POS-RATIONAL-BUILTIN
     (9 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-NEG-RATIONALP)
(ACL2S::NTH-NON-NEG-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1 (:REWRITE DEFAULT-PLUS-2))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-PLUS-1))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-POS-RATIONALP)
(ACL2S::NTH-NON-POS-RATIONAL-BUILTIN
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (4 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1 (:REWRITE DEFAULT-MINUS))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NON-0-RATIONALP)
(ACL2S::NTH-NON-0-RATIONAL-BUILTIN
     (13 8 (:REWRITE DEFAULT-TIMES-2))
     (12 5 (:REWRITE DEFAULT-PLUS-2))
     (11 8 (:REWRITE DEFAULT-TIMES-1))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE DEFAULT-MINUS))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-RATIONAL-BUILTIN
     (30 18 (:REWRITE DEFAULT-TIMES-2))
     (24 18 (:REWRITE DEFAULT-TIMES-1))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (21 5 (:REWRITE DEFAULT-PLUS-2))
     (18 2 (:REWRITE DEFAULT-MOD-RATIO))
     (14 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 1 (:REWRITE O-INFP->NEQ-0))
     (2 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-RAT-IS-RATP
     (73 31 (:REWRITE DEFAULT-TIMES-2))
     (58 31 (:REWRITE DEFAULT-TIMES-1))
     (56 6 (:REWRITE DEFAULT-PLUS-2))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (41 41 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (22 22 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (18 18
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (18 2 (:REWRITE DEFAULT-MOD-RATIO))
     (15 15
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (15 6 (:REWRITE DEFAULT-PLUS-1))
     (14 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (11 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (9 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 3 (:REWRITE DEFAULT-LESS-THAN-1))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE NORMALIZE-ADDENDS))
     (4 3
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (4 2
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3G))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2G))
     (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1G))
     (3 3 (:REWRITE THE-FLOOR-BELOW))
     (3 3 (:REWRITE THE-FLOOR-ABOVE))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3 3 (:REWRITE INTEGERP-<-CONSTANT))
     (3 3 (:REWRITE DEFAULT-MINUS))
     (3 3 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (/ x) (/ y))|))
     (3 3 (:REWRITE |(< (- x) c)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(* (- x) y)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 2 (:REWRITE DEFAULT-MOD-2))
     (2 2 (:REWRITE |(mod x 2)| . 2))
     (2 2 (:REWRITE |(* c (* d x))|))
     (2 1 (:REWRITE DEFAULT-FLOOR-1))
     (2 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* x (- y))|)))
(ACL2S::NTH-RATIONAL-BETWEEN
     (261 30 (:REWRITE DEFAULT-TIMES-1))
     (249 30 (:REWRITE DEFAULT-TIMES-2))
     (198 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (191 1 (:REWRITE CANCEL-MOD-+))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (158 158
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (147 7 (:REWRITE INTEGERP-MINUS-X))
     (124 14
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (115 23 (:REWRITE DEFAULT-PLUS-2))
     (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (105 21 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (105 21
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (105 21
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (98 6 (:META META-INTEGERP-CORRECT))
     (85 2 (:REWRITE INTEGERP-/))
     (82 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (82 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (69 1 (:REWRITE MOD-X-Y-=-X . 2))
     (68 23 (:REWRITE DEFAULT-PLUS-1))
     (68 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (68 1 (:REWRITE MOD-X-Y-=-X . 3))
     (61 1 (:REWRITE MOD-ZERO . 3))
     (59 5 (:REWRITE DEFAULT-MINUS))
     (55 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (53 1 (:REWRITE MOD-X-Y-=-X . 4))
     (52 7
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (49 16
         (:LINEAR DEFDATA::NTH-WEIGHTED-SPLIT-NAT--BOUND))
     (45 3 (:REWRITE |(+ y (+ x z))|))
     (37 1 (:REWRITE MOD-ZERO . 4))
     (34 1 (:REWRITE DEFAULT-MOD-RATIO))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (25 14 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (23 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (21 21
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (21 21 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (21 21
         (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (21 21 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (21 21
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (21 21 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (17 17
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (17 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (16 14
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (16 14
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (16 12 (:REWRITE SIMPLIFY-SUMS-<))
     (15 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (15 1
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (13 3 (:REWRITE |(- (* c x))|))
     (12 12
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
     (10 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (10 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (9 9 (:REWRITE NORMALIZE-ADDENDS))
     (9 6 (:REWRITE DEFAULT-DIVIDE))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 4
        (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (8 2 (:REWRITE RATIONALP-X))
     (7 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (7 1 (:REWRITE MOD-CANCEL-*-CONST))
     (7 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (7 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(* c (* d x))|))
     (5 5 (:TYPE-PRESCRIPTION ABS))
     (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3 3 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 1 (:REWRITE DEFAULT-MOD-2))
     (2 1 (:REWRITE DEFAULT-MOD-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE O-INFP->NEQ-0))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(equal (* x y) 0)|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-COMPLEX-RATIONAL-BUILTIN
     (60 60
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (34 34 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (25 13
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 13 (:REWRITE DEFAULT-LESS-THAN-1))
     (22 6 (:REWRITE DEFAULT-PLUS-2))
     (18 9
         (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (13 13 (:REWRITE THE-FLOOR-BELOW))
     (13 13 (:REWRITE THE-FLOOR-ABOVE))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13 13
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (13 13 (:REWRITE SIMPLIFY-SUMS-<))
     (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13 13
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13 13
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (13 13
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (13 13
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (13 13 (:REWRITE INTEGERP-<-CONSTANT))
     (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
     (13 13 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< c (- x))|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13 13
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13 13 (:REWRITE |(< (/ x) 0)|))
     (13 13 (:REWRITE |(< (/ x) (/ y))|))
     (13 13 (:REWRITE |(< (- x) c)|))
     (13 13 (:REWRITE |(< (- x) (- y))|))
     (13 13 (:REWRITE |(< (* x y) 0)|))
     (12 6 (:REWRITE DEFAULT-TIMES-2))
     (10 6 (:REWRITE DEFAULT-TIMES-1))
     (8 6 (:REWRITE DEFAULT-PLUS-1))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE NORMALIZE-ADDENDS))
     (4 4
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (4 2 (:REWRITE DEFAULT-DIVIDE))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-COMPLEX-RATIONAL-BETWEEN
     (466 56 (:REWRITE DEFAULT-TIMES-1))
     (460 2 (:REWRITE CANCEL-MOD-+))
     (452 56 (:REWRITE DEFAULT-TIMES-2))
     (402 48 (:REWRITE DEFAULT-PLUS-2))
     (367 9 (:REWRITE INTEGERP-MINUS-X))
     (320 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (269 7 (:META META-INTEGERP-CORRECT))
     (248 4 (:REWRITE INTEGERP-/))
     (245 25
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (224 224
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (196 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (190 38
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (190 38
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (164 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (164 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (156 36
          (:LINEAR DEFDATA::NTH-WEIGHTED-SPLIT-NAT--BOUND))
     (144 48 (:REWRITE DEFAULT-PLUS-1))
     (138 2 (:REWRITE MOD-X-Y-=-X . 2))
     (136 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (122 2 (:REWRITE MOD-ZERO . 3))
     (122 2 (:REWRITE MOD-X-Y-=-X . 3))
     (120 8 (:REWRITE DEFAULT-MINUS))
     (112 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (106 2 (:REWRITE MOD-X-Y-=-X . 4))
     (102 12
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (90 6 (:REWRITE |(+ y (+ x z))|))
     (74 2 (:REWRITE MOD-ZERO . 4))
     (68 2 (:REWRITE DEFAULT-MOD-RATIO))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (64 64 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
     (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
     (48 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
     (46 46
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (43 25 (:REWRITE DEFAULT-LESS-THAN-1))
     (39 19
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (38 38
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (38 38 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (38 38
         (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (38 38 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (38 38
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (32 32
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (31 25 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (30 2
         (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (29 25
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (29 25
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (27 19 (:REWRITE SIMPLIFY-SUMS-<))
     (26 6 (:REWRITE |(- (* c x))|))
     (25 25 (:REWRITE THE-FLOOR-BELOW))
     (25 25 (:REWRITE THE-FLOOR-ABOVE))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
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
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (18 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (18 10
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
     (16 8 (:REWRITE DEFAULT-DIVIDE))
     (14 12
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (14 2
         (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 2 (:REWRITE MOD-CANCEL-*-CONST))
     (14 2
         (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (14 2
         (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (12 12 (:REWRITE |(* c (* d x))|))
     (12 6
         (:DEFINITION DEFDATA::NTHCDR-WEIGHTED-SPLIT-NAT--DEFLIKE))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:TYPE-PRESCRIPTION ABS))
     (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (10 10
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (10 10 (:REWRITE |(equal c (/ x))|))
     (10 10 (:REWRITE |(equal c (- x))|))
     (10 10 (:REWRITE |(equal (/ x) c)|))
     (10 10 (:REWRITE |(equal (/ x) (/ y))|))
     (10 10 (:REWRITE |(equal (- x) c)|))
     (10 10 (:REWRITE |(equal (- x) (- y))|))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE DEFAULT-REALPART))
     (4 4 (:REWRITE DEFAULT-IMAGPART))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 2 (:REWRITE DEFAULT-MOD-2))
     (4 2 (:REWRITE DEFAULT-MOD-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE |(mod x (- y))| . 3))
     (2 2 (:REWRITE |(mod x (- y))| . 2))
     (2 2 (:REWRITE |(mod x (- y))| . 1))
     (2 2
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(mod (- x) y)| . 3))
     (2 2 (:REWRITE |(mod (- x) y)| . 2))
     (2 2 (:REWRITE |(mod (- x) y)| . 1))
     (2 2
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(equal (* x y) 0)|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2
        (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(* (- x) y)|)))
(ACL2S::NTH-ACL2-NUMBER-BUILTIN
     (13 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 5
         (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
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
     (6 2 (:REWRITE O-INFP->NEQ-0))
     (6 2 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE DEFDATA::MY-MV-NTH--REDUCE1))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-ACL2-NUMBER-BETWEEN)
(ACL2S::NTH-NUMBER-BETWEEN-FN)
(ACL2S::NTH-STRING-BUILTIN
   (716 1
        (:DEFINITION ACL2S::GET-CHARACTER-LIST-FROM-POSITIONS))
   (414 5 (:REWRITE DEFAULT-MOD-1))
   (413 4 (:REWRITE DEFAULT-MOD-RATIO))
   (298 1 (:DEFINITION NTH))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
   (236 10 (:REWRITE DEFAULT-PLUS-2))
   (231 2 (:REWRITE ZP-OPEN))
   (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
   (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
   (197 45
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
   (197 45
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
   (159 3 (:REWRITE CANCEL-MOD-+))
   (92 2 (:REWRITE |(< x (if a b c))|))
   (89 20 (:REWRITE INTEGERP-MINUS-X))
   (72 3 (:REWRITE MOD-X-Y-=-X . 4))
   (70 2 (:REWRITE |(+ x (if a b c))|))
   (67 3 (:REWRITE MOD-X-Y-=-X . 3))
   (64 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
   (51 6 (:REWRITE |(* (- x) y)|))
   (51 1
       (:REWRITE DEFDATA::WEIGHTED-SPLIT-NAT--TO--NTHCDR-WEIGHTED-SPLIT-NAT))
   (48 12 (:REWRITE |(* y x)|))
   (48 6 (:REWRITE RATIONALP-X))
   (48 1 (:DEFINITION DEFDATA::POS-LISTP))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
   (46 2 (:REWRITE MOD-POSITIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
   (45 45 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
   (45 45
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
   (45 45
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
   (45 3 (:REWRITE MOD-ZERO . 3))
   (45 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
   (43 35 (:REWRITE DEFAULT-TIMES-2))
   (42 6 (:REWRITE REDUCE-RATIONALP-*))
   (41 12 (:REWRITE DEFAULT-LESS-THAN-2))
   (38 3 (:REWRITE MOD-ZERO . 4))
   (37 1 (:DEFINITION POSP))
   (35 35 (:REWRITE DEFAULT-TIMES-1))
   (30 6 (:REWRITE DEFAULT-MINUS))
   (27 6 (:REWRITE |(- (* c x))|))
   (18 18
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
   (18 2 (:REWRITE ACL2-NUMBERP-X))
   (17 17 (:REWRITE REDUCE-INTEGERP-+))
   (17 17 (:META META-INTEGERP-CORRECT))
   (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
   (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
   (15 3 (:REWRITE MOD-X-Y-=-X . 2))
   (15 3
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
   (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
   (15 3
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
   (15 3
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
   (14 14
       (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
   (14 14 (:REWRITE THE-FLOOR-BELOW))
   (14 14 (:REWRITE THE-FLOOR-ABOVE))
   (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
   (11 3 (:REWRITE MOD-CANCEL-*-CONST))
   (10 10 (:REWRITE SIMPLIFY-SUMS-<))
   (10 10
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
   (10 10
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
   (10 10
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
   (10 10
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
   (10 10
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
   (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
   (10 10 (:REWRITE INTEGERP-<-CONSTANT))
   (10 10 (:REWRITE DEFAULT-PLUS-1))
   (10 10 (:REWRITE CONSTANT-<-INTEGERP))
   (10 10
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
   (10 10
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
   (10 10
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
   (10 10
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
   (10 10 (:REWRITE |(< c (- x))|))
   (10 10
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
   (10 10
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
   (10 10
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
   (10 10
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
   (10 10 (:REWRITE |(< (/ x) (/ y))|))
   (10 10 (:REWRITE |(< (- x) c)|))
   (10 10 (:REWRITE |(< (- x) (- y))|))
   (9 9 (:TYPE-PRESCRIPTION MAKE-LIST-AC))
   (7 7 (:TYPE-PRESCRIPTION RATIONALP-MOD))
   (7 7
      (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
   (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
   (6 6 (:REWRITE RATIONALP-MINUS-X))
   (5 5
      (:TYPE-PRESCRIPTION DEFDATA::POS-LISTP))
   (5 5
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
   (5 5 (:REWRITE NORMALIZE-ADDENDS))
   (5 5 (:REWRITE DEFAULT-MOD-2))
   (4 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
   (4 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
   (4 4 (:REWRITE REDUCE-RATIONALP-+))
   (4 4 (:REWRITE |(< 0 (/ x))|))
   (4 4 (:REWRITE |(< 0 (* x y))|))
   (4 4 (:META META-RATIONALP-CORRECT))
   (3 3
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
   (3 3
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
   (3 3
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
   (3 3 (:REWRITE |(< (/ x) 0)|))
   (3 3 (:REWRITE |(< (* x y) 0)|))
   (3 2 (:REWRITE DEFAULT-CDR))
   (3 2 (:REWRITE DEFAULT-CAR))
   (2 2
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
   (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
   (2 2
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
   (2 2
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
   (2 2
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
   (2 2
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
   (2 2 (:REWRITE MOD-POSITIVE . 3))
   (2 2 (:REWRITE MOD-POSITIVE . 2))
   (2 2
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
   (2 2 (:REWRITE |(equal c (/ x))|))
   (2 2 (:REWRITE |(equal c (- x))|))
   (2 2 (:REWRITE |(equal (/ x) c)|))
   (2 2 (:REWRITE |(equal (/ x) (/ y))|))
   (2 2 (:REWRITE |(equal (- x) c)|))
   (2 2 (:REWRITE |(equal (- x) (- y))|))
   (2 2 (:REWRITE |(* a (/ a) b)|)))
(ACL2S::NTH-STRING-IS-STRINGP)
(ACL2S::STANDARD-STRINGP)
(ACL2S::NTH-STANDARD-STRING-BUILTIN
   (716 1
        (:DEFINITION ACL2S::GET-STANDARD-CHAR-LIST-FROM-POSITIONS))
   (414 5 (:REWRITE DEFAULT-MOD-1))
   (413 4 (:REWRITE DEFAULT-MOD-RATIO))
   (298 1 (:DEFINITION NTH))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (243 243
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
   (236 10 (:REWRITE DEFAULT-PLUS-2))
   (231 2 (:REWRITE ZP-OPEN))
   (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
   (225 45 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
   (197 45
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
   (197 45
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
   (159 3 (:REWRITE CANCEL-MOD-+))
   (92 2 (:REWRITE |(< x (if a b c))|))
   (89 20 (:REWRITE INTEGERP-MINUS-X))
   (72 3 (:REWRITE MOD-X-Y-=-X . 4))
   (70 2 (:REWRITE |(+ x (if a b c))|))
   (67 3 (:REWRITE MOD-X-Y-=-X . 3))
   (64 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
   (51 6 (:REWRITE |(* (- x) y)|))
   (51 1
       (:REWRITE DEFDATA::WEIGHTED-SPLIT-NAT--TO--NTHCDR-WEIGHTED-SPLIT-NAT))
   (48 12 (:REWRITE |(* y x)|))
   (48 6 (:REWRITE RATIONALP-X))
   (48 1 (:DEFINITION DEFDATA::POS-LISTP))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
   (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
   (46 2 (:REWRITE MOD-POSITIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
   (45 45 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
   (45 45
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
   (45 45
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
   (45 45 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
   (45 3 (:REWRITE MOD-ZERO . 3))
   (45 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
   (43 35 (:REWRITE DEFAULT-TIMES-2))
   (42 6 (:REWRITE REDUCE-RATIONALP-*))
   (41 12 (:REWRITE DEFAULT-LESS-THAN-2))
   (38 3 (:REWRITE MOD-ZERO . 4))
   (37 1 (:DEFINITION POSP))
   (35 35 (:REWRITE DEFAULT-TIMES-1))
   (30 6 (:REWRITE DEFAULT-MINUS))
   (27 6 (:REWRITE |(- (* c x))|))
   (18 18
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
   (18 2 (:REWRITE ACL2-NUMBERP-X))
   (17 17 (:REWRITE REDUCE-INTEGERP-+))
   (17 17 (:META META-INTEGERP-CORRECT))
   (15 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
   (15 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
   (15 3 (:REWRITE MOD-X-Y-=-X . 2))
   (15 3
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
   (15 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
   (15 3
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
   (15 3
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
   (14 14
       (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
   (14 14 (:REWRITE THE-FLOOR-BELOW))
   (14 14 (:REWRITE THE-FLOOR-ABOVE))
   (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
   (11 3 (:REWRITE MOD-CANCEL-*-CONST))
   (10 10 (:REWRITE SIMPLIFY-SUMS-<))
   (10 10
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
   (10 10
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
   (10 10
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
   (10 10
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
   (10 10
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
   (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
   (10 10 (:REWRITE INTEGERP-<-CONSTANT))
   (10 10 (:REWRITE DEFAULT-PLUS-1))
   (10 10 (:REWRITE CONSTANT-<-INTEGERP))
   (10 10
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
   (10 10
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
   (10 10
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
   (10 10
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
   (10 10 (:REWRITE |(< c (- x))|))
   (10 10
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
   (10 10
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
   (10 10
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
   (10 10
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
   (10 10 (:REWRITE |(< (/ x) (/ y))|))
   (10 10 (:REWRITE |(< (- x) c)|))
   (10 10 (:REWRITE |(< (- x) (- y))|))
   (9 9 (:TYPE-PRESCRIPTION MAKE-LIST-AC))
   (7 7 (:TYPE-PRESCRIPTION RATIONALP-MOD))
   (7 7
      (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
   (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
   (6 6 (:REWRITE RATIONALP-MINUS-X))
   (5 5
      (:TYPE-PRESCRIPTION DEFDATA::POS-LISTP))
   (5 5
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
   (5 5 (:REWRITE NORMALIZE-ADDENDS))
   (5 5 (:REWRITE DEFAULT-MOD-2))
   (4 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
   (4 4
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
   (4 4 (:REWRITE REDUCE-RATIONALP-+))
   (4 4 (:REWRITE |(< 0 (/ x))|))
   (4 4 (:REWRITE |(< 0 (* x y))|))
   (4 4 (:META META-RATIONALP-CORRECT))
   (3 3
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
   (3 3
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
   (3 3
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
   (3 3 (:REWRITE |(< (/ x) 0)|))
   (3 3 (:REWRITE |(< (* x y) 0)|))
   (3 2 (:REWRITE DEFAULT-CDR))
   (3 2 (:REWRITE DEFAULT-CAR))
   (2 2
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
   (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
   (2 2
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
   (2 2
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
   (2 2
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
   (2 2
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
   (2 2 (:REWRITE MOD-POSITIVE . 3))
   (2 2 (:REWRITE MOD-POSITIVE . 2))
   (2 2
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
   (2 2 (:REWRITE |(equal c (/ x))|))
   (2 2 (:REWRITE |(equal c (- x))|))
   (2 2 (:REWRITE |(equal (/ x) c)|))
   (2 2 (:REWRITE |(equal (/ x) (/ y))|))
   (2 2 (:REWRITE |(equal (- x) c)|))
   (2 2 (:REWRITE |(equal (- x) (- y))|))
   (2 2 (:REWRITE |(* a (/ a) b)|)))
(ACL2S::NTH-SYMBOL-BUILTIN)
(ACL2S::NTH-CHARACTER-BUILTIN
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (14 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-ALPHA-NUM-CHARACTER
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (14 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-CHARACTER-LIST-BUILTIN
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (45 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (45 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (13 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (13 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (5 5
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (5 5
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-STANDARD-CHAR-LIST-BUILTIN
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (65 13 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (45 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (45 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (13 13 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (13 13
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (13 13
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (13 13 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (5 5
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (5 5
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NEG)
(ACL2S::NTH-NEG/ACC-BUILTIN)
(ACL2S::NTH-NEG/ACC)
(ACL2S::NTH-POS)
(ACL2S::NTH-POS/ACC-BUILTIN)
(ACL2S::NTH-POS/ACC)
(ACL2S::NTH-NAT)
(ACL2S::NTH-NAT/ACC-BUILTIN)
(ACL2S::NTH-NAT/ACC)
(ACL2S::NTH-NON-POS-INTEGER)
(ACL2S::NTH-NON-POS-INTEGER/ACC-BUILTIN)
(ACL2S::NTH-NON-POS-INTEGER/ACC)
(ACL2S::NTH-NON-0-INTEGER)
(ACL2S::NTH-NON-0-INTEGER/ACC-BUILTIN)
(ACL2S::NTH-NON-0-INTEGER/ACC)
(ACL2S::NTH-INTEGER)
(ACL2S::NTH-INTEGER/ACC-BUILTIN)
(ACL2S::NTH-INTEGER/ACC)
(ACL2S::NTH-NEG-RATIO)
(ACL2S::NTH-NEG-RATIO/ACC-BUILTIN)
(ACL2S::NTH-NEG-RATIO/ACC)
(ACL2S::NTH-POS-RATIO)
(ACL2S::NTH-POS-RATIO/ACC-BUILTIN)
(ACL2S::NTH-POS-RATIO/ACC)
(ACL2S::RATIOP)
(DEF=>RATIO)
(RATIO=>DEF)
(ACL2S::NTH-RATIO-BUILTIN)
(ACL2S::NTH-RATIO/ACC-BUILTIN)
(ACL2S::NTH-RATIO)
(ACL2S::NTH-RATIO/ACC)
(ACL2S::NTH-NEG-RATIONAL)
(ACL2S::NTH-NEG-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-NEG-RATIONAL/ACC)
(ACL2S::NTH-POS-RATIONAL)
(ACL2S::NTH-POS-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-POS-RATIONAL/ACC)
(ACL2S::NTH-NON-NEG-RATIONAL)
(ACL2S::NTH-NON-NEG-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-NON-NEG-RATIONAL/ACC)
(ACL2S::NTH-NON-POS-RATIONAL)
(ACL2S::NTH-NON-POS-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-NON-POS-RATIONAL/ACC)
(ACL2S::NTH-NON-0-RATIONAL)
(ACL2S::NTH-NON-0-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-NON-0-RATIONAL/ACC)
(ACL2S::NTH-RATIONAL)
(ACL2S::NTH-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-RATIONAL/ACC)
(ACL2S::NTH-COMPLEX-RATIONAL)
(ACL2S::NTH-COMPLEX-RATIONAL/ACC-BUILTIN)
(ACL2S::NTH-COMPLEX-RATIONAL/ACC)
(ACL2S::NTH-ACL2-NUMBER)
(ACL2S::NTH-ACL2-NUMBER/ACC-BUILTIN)
(ACL2S::NTH-ACL2-NUMBER/ACC)
(ACL2S::NTH-NEG-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-POS-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (10 5
         (:TYPE-PRESCRIPTION ACL2S::NTH-POS-BUILTIN-IS-POSP))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NAT-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NON-POS-INTEGER-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NON-0-INTEGER-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-INTEGER-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NEG-RATIO-TESTING
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-POS-RATIO-TESTING
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-RATIO-TESTING)
(ACL2S::NTH-NEG-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-POS-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NON-NEG-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NON-POS-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-NON-0-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (10 5
         (:TYPE-PRESCRIPTION ACL2S::NTH-RAT-IS-RATP))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-COMPLEX-RATIONAL-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-ACL2-NUMBER-TESTING
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (35 7 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (11 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (11 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (7 7 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (7 7 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (7 7 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (6 6 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (6 6
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-BOOLEAN)
(ACL2S::NTH-BOOLEAN/ACC-BUILTIN)
(ACL2S::NTH-BOOLEAN/ACC)
(ACL2S::NTH-SYMBOL)
(ACL2S::NTH-SYMBOL/ACC-BUILTIN)
(ACL2S::NTH-SYMBOL/ACC)
(ACL2S::PROPER-SYMBOLP)
(ACL2S::NTH-PROPER-SYMBOL-BUILTIN
     (34 18 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (34 18 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (18 18 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (18 18
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (18 18
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (18 18 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (18 18
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (18 18
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (18 18 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (16 16
         (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-PROPER-SYMBOL)
(ACL2S::NTH-PROPER-SYMBOL/ACC-BUILTIN)
(ACL2S::NTH-PROPER-SYMBOL/ACC)
(ACL2S::NTH-CHARACTER-UNIFORM-BUILTIN
     (7 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE DEFAULT-CDR))
     (2 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::NTH-CHARACTER)
(ACL2S::NTH-CHARACTER/ACC)
(ACL2S::NTH-STANDARD-CHAR-BUILTIN
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (14 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-STANDARD-CHAR)
(ACL2S::NTH-STANDARD-CHAR/ACC-BUILTIN)
(ACL2S::NTH-STANDARD-CHAR/ACC)
(ACL2S::NTH-STRING)
(ACL2S::NTH-STRING/ACC-BUILTIN)
(ACL2S::NTH-STRING/ACC)
(ACL2S::NTH-STANDARD-STRING)
(ACL2S::NTH-STANDARD-STRING/ACC-BUILTIN)
(ACL2S::NTH-STANDARD-STRING/ACC)
(ACL2S::NTH-ATOM-BUILTIN
     (33 17
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (33 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (25 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (25 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (25 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (17 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< c (- x))|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (6 2 (:REWRITE DEFAULT-CAR))
     (3 1 (:REWRITE O-INFP->NEQ-0))
     (2 1 (:REWRITE DEFAULT-CDR))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE DEFDATA::MY-MV-NTH--REDUCE1))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-ATOM)
(ACL2S::NTH-ATOM/ACC-BUILTIN)
(ACL2S::NTH-ATOM/ACC)
(ACL2S::NTH-Z-BUILTIN
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (30 6 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (14 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (14 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (6 6 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (6 6 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (6 6 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (6 6 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
     (4 4
        (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD)))
(ACL2S::NTH-Z-UNIFORM-BUILTIN
     (7 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE DEFAULT-CDR))
     (2 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::NTH-Z)
(ACL2S::NTH-Z/ACC)
(ACL2S::NEG-IS-SUBTYPE-OF-NON-POS-INTEGER)
(ACL2S::NEG-IS-SUBTYPE-OF-NON-0-INTEGER)
(ACL2S::NEG-IS-SUBTYPE-OF-NEG-RATIONAL)
(ACL2S::POS-IS-SUBTYPE-OF-NAT)
(ACL2S::POS-IS-SUBTYPE-OF-NON-0-INTEGER)
(ACL2S::POS-IS-SUBTYPE-OF-POS-RATIONAL)
(ACL2S::NON-POS-INTEGER-IS-SUBTYPE-OF-INTEGER)
(ACL2S::NON-0-INTEGER-IS-SUBTYPE-OF-INTEGER)
(ACL2S::NAT-IS-SUBTYPE-OF-INTEGER)
(ACL2S::INTEGER-IS-SUBTYPE-OF-RATIONAL)
(ACL2S::NEG-RATIO-IS-SUBTYPE-OF-NON-POS-RATIONAL)
(ACL2S::POS-RATIO-IS-SUBTYPE-OF-NON-NEG-RATIONAL)
(ACL2S::RATIO-IS-SUBTYPE-OF-RATIONAL)
(ACL2S::NEG-RATIONAL-IS-SUBTYPE-OF-NON-POS-RATIONAL)
(ACL2S::NEG-RATIONAL-IS-SUBTYPE-OF-NON-0-RATIONAL)
(ACL2S::POS-RATIONAL-IS-SUBTYPE-OF-NON-NEG-RATIONAL)
(ACL2S::POS-RATIONAL-IS-SUBTYPE-OF-NON-0-RATIONAL)
(ACL2S::NON-NEG-RATIONAL-IS-SUBTYPE-OF-RATIONAL)
(ACL2S::NON-POS-RATIONAL-IS-SUBTYPE-OF-RATIONAL)
(ACL2S::NON-0-RATIONAL-IS-SUBTYPE-OF-RATIONAL)
(ACL2S::RATIONAL-IS-SUBTYPE-OF-ACL2-NUMBER)
(ACL2S::COMPLEX-RATIONAL-IS-SUBTYPE-OF-ACL2-NUMBER)
(ACL2S::ACL2-NUMBER-IS-SUBTYPE-OF-ATOM)
(ACL2S::NON-POS-RATIONAL-IS-SUBTYPE-OF-Z)
(ACL2S::RATIO-IS-SUBTYPE-OF-Z)
(ACL2S::COMPLEX-RATIONAL-IS-SUBTYPE-OF-Z)
(ACL2S::SYMBOL-IS-SUBTYPE-OF-Z)
(ACL2S::CHARACTER-IS-SUBTYPE-OF-Z)
(ACL2S::STRING-IS-SUBTYPE-OF-Z)
(ACL2S::NEG-IS-DISJOINT-WITH-NAT)
(ACL2S::POS-IS-DISJOINT-WITH-NON-POS-INTEGER)
(ACL2S::INTEGER-IS-DISJOINT-WITH-RATIO)
(ACL2S::NEG-RATIO-IS-DISJOINT-WITH-NON-NEG-RATIONAL)
(ACL2S::POS-RATIO-IS-DISJOINT-WITH-NON-POS-RATIONAL)
(ACL2S::NEG-RATIONAL-IS-DISJOINT-WITH-NON-NEG-RATIONAL)
(ACL2S::POS-RATIONAL-IS-DISJOINT-WITH-NON-POS-RATIONAL)
(ACL2S::RATIONAL-IS-DISJOINT-WITH-COMPLEX-RATIONAL)
(ACL2S::POS-IS-DISJOINT-WITH-Z)
(ACL2S::BOOLEAN-IS-SUBTYPE-OF-SYMBOL)
(ACL2S::PROPER-SYMBOL-IS-SUBTYPE-OF-SYMBOL)
(ACL2S::STANDARD-CHAR-IS-SUBTYPE-OF-CHARACTER)
(ACL2S::CHARACTER-IS-SUBTYPE-OF-ATOM)
(ACL2S::STRING-IS-SUBTYPE-OF-ATOM)
(ACL2S::SYMBOL-IS-SUBTYPE-OF-ATOM)
(ACL2S::STANDARD-STRING-IS-SUBTYPE-OF-STRING)
(ACL2S::ACL2-NUMBER-IS-DISJOINT-WITH-CHARACTER)
(ACL2S::ACL2-NUMBER-IS-DISJOINT-WITH-SYMBOL)
(ACL2S::CHARACTER-IS-DISJOINT-WITH-STRING)
(ACL2S::CHARACTER-IS-DISJOINT-WITH-SYMBOL)
(ACL2S::STRING-IS-DISJOINT-WITH-SYMBOL)
(ACL2S::BOOLEAN-IS-DISJOINT-WITH-PROPER-SYMBOL)
(ACL2S::TERMINATION-TREE-ENUM-CDR
     (630 12 (:DEFINITION INTEGER-ABS))
     (258 95 (:REWRITE DEFAULT-PLUS-1))
     (241 95 (:REWRITE DEFAULT-PLUS-2))
     (210 6 (:REWRITE |(+ (if a b c) x)|))
     (186 6 (:REWRITE NUMERATOR-NEGATIVE))
     (60 6 (:DEFINITION LENGTH))
     (54 54 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (54 22 (:REWRITE DEFAULT-LESS-THAN-1))
     (53 53
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (42 12 (:REWRITE DEFAULT-MINUS))
     (42 6 (:DEFINITION LEN))
     (28 22 (:REWRITE DEFAULT-LESS-THAN-2))
     (24 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (24 6 (:REWRITE RATIONALP-X))
     (23 16
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (22 22 (:REWRITE THE-FLOOR-BELOW))
     (22 22 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (22 22
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (22 22
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (22 22
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (22 22
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (22 22 (:REWRITE INTEGERP-<-CONSTANT))
     (22 22 (:REWRITE CONSTANT-<-INTEGERP))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< c (- x))|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (22 22
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (22 22 (:REWRITE |(< (/ x) (/ y))|))
     (22 22 (:REWRITE |(< (- x) c)|))
     (22 22 (:REWRITE |(< (- x) (- y))|))
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (17 17 (:REWRITE DEFAULT-CDR))
     (17 17 (:REWRITE |(+ c (+ d x))|))
     (16 16 (:REWRITE FOLD-CONSTS-IN-+))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (12 3 (:REWRITE O-P-O-INFP-CAR))
     (11 11 (:REWRITE DEFAULT-CAR))
     (8 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (6 6 (:TYPE-PRESCRIPTION O-P))
     (6 6 (:TYPE-PRESCRIPTION LEN))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (6 6 (:REWRITE DEFAULT-REALPART))
     (6 6 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (6 6
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (6 6 (:REWRITE DEFAULT-IMAGPART))
     (6 6 (:REWRITE DEFAULT-COERCE-2))
     (6 6 (:REWRITE DEFAULT-COERCE-1))
     (6 6 (:META META-RATIONALP-CORRECT))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|)))
(ACL2S::TERMINATION-TREE-ENUM-DEC
     (3990 76 (:DEFINITION INTEGER-ABS))
     (1330 38 (:REWRITE |(+ (if a b c) x)|))
     (1298 422 (:REWRITE DEFAULT-PLUS-1))
     (1178 38 (:REWRITE NUMERATOR-NEGATIVE))
     (1112 422 (:REWRITE DEFAULT-PLUS-2))
     (1026 114 (:REWRITE |(+ y x)|))
     (380 38 (:DEFINITION LENGTH))
     (342 342 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (342 342
          (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (342 133 (:REWRITE DEFAULT-LESS-THAN-1))
     (270 270
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (270 270 (:REWRITE NORMALIZE-ADDENDS))
     (266 76 (:REWRITE DEFAULT-MINUS))
     (266 38 (:DEFINITION LEN))
     (161 133
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (152 38 (:REWRITE RATIONALP-X))
     (142 133 (:REWRITE DEFAULT-LESS-THAN-2))
     (133 133 (:REWRITE THE-FLOOR-BELOW))
     (133 133 (:REWRITE THE-FLOOR-ABOVE))
     (133 133 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (133 133
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (133 133
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (133 133
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (133 133 (:REWRITE INTEGERP-<-CONSTANT))
     (133 133 (:REWRITE CONSTANT-<-INTEGERP))
     (133 133
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (133 133
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (133 133
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (133 133
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (133 133 (:REWRITE |(< c (- x))|))
     (133 133
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (133 133
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (133 133
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (133 133
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (133 133 (:REWRITE |(< (/ x) (/ y))|))
     (133 133 (:REWRITE |(< (- x) c)|))
     (133 133 (:REWRITE |(< (- x) (- y))|))
     (123 95 (:REWRITE SIMPLIFY-SUMS-<))
     (123 95
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (123 95 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (114 114 (:REWRITE |(< (/ x) 0)|))
     (114 114 (:REWRITE |(< (* x y) 0)|))
     (78 78 (:REWRITE FOLD-CONSTS-IN-+))
     (78 78 (:REWRITE |(+ c (+ d x))|))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (76 76
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (76 76 (:REWRITE REDUCE-INTEGERP-+))
     (76 76 (:REWRITE INTEGERP-MINUS-X))
     (76 76 (:META META-INTEGERP-CORRECT))
     (38 38 (:TYPE-PRESCRIPTION LEN))
     (38 38 (:REWRITE REDUCE-RATIONALP-+))
     (38 38 (:REWRITE REDUCE-RATIONALP-*))
     (38 38 (:REWRITE RATIONALP-MINUS-X))
     (38 38 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (38 38
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (38 38 (:REWRITE DEFAULT-REALPART))
     (38 38
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (38 38
         (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (38 38 (:REWRITE DEFAULT-IMAGPART))
     (38 38 (:REWRITE DEFAULT-COERCE-2))
     (38 38 (:REWRITE DEFAULT-COERCE-1))
     (38 38 (:META META-RATIONALP-CORRECT))
     (18 3 (:REWRITE O-P-O-INFP-CAR))
     (9 3 (:REWRITE O-P-DEF-O-FINP-1))
     (6 6 (:TYPE-PRESCRIPTION O-P))
     (6 6 (:TYPE-PRESCRIPTION O-FINP))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(< (+ c/d x) y)|))
     (2 2 (:REWRITE |(< (+ (- c) x) y)|)))
(ACL2S::TERMININATION-TREE-ENUM-NTH
     (996 32 (:DEFINITION NAT-LISTP))
     (934 2
          (:REWRITE ACL2S::TERMINATION-TREE-ENUM-DEC))
     (816 24 (:DEFINITION NATP))
     (544 16
          (:REWRITE DEFDATA::NAT-LISTP--NTH-->=0))
     (540 16
          (:REWRITE DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (444 145 (:REWRITE DEFAULT-PLUS-1))
     (387 145 (:REWRITE DEFAULT-PLUS-2))
     (353 13 (:REWRITE RATIONALP-X))
     (174 79 (:REWRITE DEFAULT-LESS-THAN-1))
     (164 164 (:TYPE-PRESCRIPTION NAT-LISTP))
     (135 135 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (103 64
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (93 79 (:REWRITE DEFAULT-LESS-THAN-2))
     (90 90
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (89 63 (:REWRITE SIMPLIFY-SUMS-<))
     (86 74 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (85 25 (:REWRITE DEFAULT-MINUS))
     (84 12 (:DEFINITION LEN))
     (82 77 (:REWRITE |(< (- x) (- y))|))
     (79 79 (:REWRITE THE-FLOOR-BELOW))
     (79 79 (:REWRITE THE-FLOOR-ABOVE))
     (77 77
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (77 77
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (77 77
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (77 77
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (77 77
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (77 77
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (77 77
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (77 77 (:REWRITE |(< c (- x))|))
     (77 77
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (77 77
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (77 77
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (77 77
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (77 77 (:REWRITE |(< (/ x) (/ y))|))
     (76 76
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (76 76 (:REWRITE INTEGERP-<-CONSTANT))
     (76 76 (:REWRITE CONSTANT-<-INTEGERP))
     (72 36
         (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (66 66 (:REWRITE |(< (/ x) 0)|))
     (66 66 (:REWRITE |(< (* x y) 0)|))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (49 49 (:REWRITE REDUCE-INTEGERP-+))
     (49 49 (:REWRITE INTEGERP-MINUS-X))
     (49 49 (:REWRITE DEFAULT-CDR))
     (49 49 (:META META-INTEGERP-CORRECT))
     (38 38 (:REWRITE DEFAULT-CAR))
     (28 8 (:REWRITE O-P-O-INFP-CAR))
     (26 26 (:REWRITE FOLD-CONSTS-IN-+))
     (26 26 (:REWRITE |(+ c (+ d x))|))
     (14 14 (:TYPE-PRESCRIPTION O-P))
     (13 13 (:REWRITE REDUCE-RATIONALP-+))
     (13 13 (:REWRITE REDUCE-RATIONALP-*))
     (13 13 (:REWRITE RATIONALP-MINUS-X))
     (13 13 (:META META-RATIONALP-CORRECT))
     (12 12 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (12 12
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (12 12
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (12 12
         (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (12 12 (:REWRITE DEFAULT-COERCE-2))
     (12 12 (:REWRITE DEFAULT-COERCE-1))
     (11 11 (:REWRITE DEFAULT-REALPART))
     (11 11 (:REWRITE DEFAULT-IMAGPART))
     (6 6 (:REWRITE O-P-DEF-O-FINP-1))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (6 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (3 3 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(- (if a b c))|)))
(ACL2S::TERMINATION-TREE-ENUM-DEC2
     (610 2 (:DEFINITION ACL2-COUNT))
     (296 4 (:DEFINITION INTEGER-ABS))
     (160 4 (:DEFINITION NAT-LISTP))
     (136 4 (:DEFINITION NATP))
     (105 2 (:REWRITE NUMERATOR-NEGATIVE))
     (86 2
         (:REWRITE DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (86 2
         (:REWRITE DEFDATA::NAT-LISTP--NTH-->=0))
     (70 2 (:REWRITE |(+ (if a b c) x)|))
     (68 22 (:REWRITE DEFAULT-PLUS-1))
     (58 22 (:REWRITE DEFAULT-PLUS-2))
     (55 2 (:REWRITE RATIONALP-X))
     (54 6 (:REWRITE |(+ y x)|))
     (24 24 (:TYPE-PRESCRIPTION NAT-LISTP))
     (20 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (20 2 (:DEFINITION LENGTH))
     (18 18 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (18 18
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (18 18
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (18 18
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (18 18
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (14 14
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (14 14 (:REWRITE NORMALIZE-ADDENDS))
     (14 4 (:REWRITE DEFAULT-MINUS))
     (14 2 (:DEFINITION LEN))
     (10 10 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE THE-FLOOR-ABOVE))
     (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (10 10
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (10 10
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (10 10
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (10 10 (:REWRITE INTEGERP-<-CONSTANT))
     (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 10 (:REWRITE CONSTANT-<-INTEGERP))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< c (- x))|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (10 10
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (10 10 (:REWRITE |(< (/ x) 0)|))
     (10 10 (:REWRITE |(< (/ x) (/ y))|))
     (10 10 (:REWRITE |(< (- x) c)|))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (10 10 (:REWRITE |(< (* x y) 0)|))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:META META-INTEGERP-CORRECT))
     (8 4
        (:TYPE-PRESCRIPTION DEFDATA::NAT-LISTP--NTH--INTEGERP))
     (6 6 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (2 2 (:TYPE-PRESCRIPTION LEN))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (2 2 (:REWRITE DEFAULT-REALPART))
     (2 2 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (2 2
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (2 2 (:REWRITE DEFAULT-IMAGPART))
     (2 2 (:REWRITE DEFAULT-COERCE-2))
     (2 2 (:REWRITE DEFAULT-COERCE-1))
     (2 2 (:META META-RATIONALP-CORRECT)))
(ACL2S::CONS-ATOMP)
(ACL2S::DEF=>CONS-ATOM (1 1 (:REWRITE DEFAULT-CDR))
                       (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-ATOM=>DEF)
(ACL2S::NTH-CONS-ATOM-BUILTIN)
(ACL2S::NTH-CONS-ATOM/ACC-BUILTIN)
(ACL2S::NTH-CONS-ATOM)
(ACL2S::NTH-CONS-ATOM/ACC)
(ACL2S::CONS-ATOM-IS-DISJOINT-WITH-ATOM)
(ACL2S::CONS-CA-CAP)
(ACL2S::DEF=>CONS-CA-CA (1 1 (:REWRITE DEFAULT-CDR))
                        (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CA-CA=>DEF)
(ACL2S::NTH-CONS-CA-CA-BUILTIN)
(ACL2S::NTH-CONS-CA-CA/ACC-BUILTIN)
(ACL2S::NTH-CONS-CA-CA)
(ACL2S::NTH-CONS-CA-CA/ACC)
(ACL2S::CONS-CCA-CCAP)
(ACL2S::DEF=>CONS-CCA-CCA (1 1 (:REWRITE DEFAULT-CDR))
                          (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CCA-CCA=>DEF)
(ACL2S::NTH-CONS-CCA-CCA-BUILTIN)
(ACL2S::NTH-CONS-CCA-CCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-CCA-CCA)
(ACL2S::NTH-CONS-CCA-CCA/ACC)
(ACL2S::NTH-PROPER-CONS-BUILTIN)
(ACL2S::NTH-PROPER-CONS-UNIFORM-BUILTIN)
(ACL2S::NTH-PROPER-CONS)
(ACL2S::NTH-PROPER-CONS/ACC)
(ACL2S::NAT-LISTP-TESTTHM
     (6 6 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE THE-FLOOR-BELOW))
     (5 5 (:REWRITE THE-FLOOR-ABOVE))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
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
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::NAT-LISTP-IMPLIES-TLP)
(ACL2S::NAT-LISTP-SUBTYPE-OF-ATOM-LIST (20 5 (:REWRITE O-P-O-INFP-CAR))
                                       (11 11 (:REWRITE DEFAULT-CAR))
                                       (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                                       (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>NAT-LIST (2 2 (:REWRITE DEFAULT-CDR))
                      (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::NAT-LIST=>DEF (3 3 (:REWRITE ACL2S::DEF=>NAT-LIST))
                      (2 2 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-NAT-LIST-BUILTIN)
(ACL2S::NTH-NAT-LIST/ACC-BUILTIN)
(ACL2S::NTH-NAT-LIST)
(ACL2S::NTH-NAT-LIST/ACC)
(ACL2S::NON-EMPTY-NAT-LISTP)
(ACL2S::DEF=>NON-EMPTY-NAT-LIST (1 1 (:REWRITE DEFAULT-CDR))
                                (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::NON-EMPTY-NAT-LIST=>DEF)
(ACL2S::NTH-NON-EMPTY-NAT-LIST-BUILTIN)
(ACL2S::NTH-NON-EMPTY-NAT-LIST/ACC-BUILTIN)
(ACL2S::NTH-NON-EMPTY-NAT-LIST)
(ACL2S::NTH-NON-EMPTY-NAT-LIST/ACC)
(ACL2S::NON-EMPTY-NAT-LIST-THM
     (10 10 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal x (if a b c))|))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (if a b c) x)|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ACL2S::LEXP-TESTTHM
     (10 10 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< c (- x))|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (- x) c)|))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::DEF=>LEX)
(ACL2S::LEX=>DEF (8 2 (:DEFINITION NAT-LISTP))
                 (4 4 (:REWRITE ACL2S::DEF=>NAT-LIST))
                 (4 4 (:REWRITE ACL2S::DEF=>LEX))
                 (2 2 (:REWRITE DEFAULT-CDR))
                 (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::NTH-LEX-BUILTIN)
(ACL2S::NTH-LEX/ACC-BUILTIN)
(ACL2S::NTH-LEX)
(ACL2S::NTH-LEX/ACC)
(ACL2S::POS-LISTP)
(ACL2S::POS-LISTP-IMPLIES-TLP
     (328 8 (:DEFINITION NAT-LISTP))
     (272 8 (:DEFINITION NATP))
     (184 2 (:DEFINITION TRUE-LISTP))
     (180 4
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (180 4
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (40 40 (:TYPE-PRESCRIPTION NAT-LISTP))
     (16 16 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (14 14 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (8 8 (:REWRITE THE-FLOOR-ABOVE))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE SIMPLIFY-SUMS-<))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE REDUCE-INTEGERP-+))
     (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (8 8 (:REWRITE INTEGERP-MINUS-X))
     (8 8 (:REWRITE INTEGERP-<-CONSTANT))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
     (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8 (:REWRITE CONSTANT-<-INTEGERP))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< c (- x))|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (8 8
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (/ x) (/ y))|))
     (8 8 (:REWRITE |(< (- x) c)|))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (8 8 (:META META-INTEGERP-CORRECT)))
(ACL2S::POS-LISTP-SUBTYPE-OF-ATOM-LIST (20 5 (:REWRITE O-P-O-INFP-CAR))
                                       (11 11 (:REWRITE DEFAULT-CAR))
                                       (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                                       (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>POS-LIST (2 2 (:REWRITE DEFAULT-CDR))
                      (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::POS-LIST=>DEF (3 3 (:REWRITE ACL2S::DEF=>POS-LIST))
                      (2 2 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-POS-LIST-BUILTIN)
(ACL2S::NTH-POS-LIST/ACC-BUILTIN)
(ACL2S::NTH-POS-LIST)
(ACL2S::NTH-POS-LIST/ACC)
(ACL2S::INTEGER-LISTP-TESTTHM
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::INTEGER-LISTP-IMPLIES-TLP)
(ACL2S::INTEGER-LISTP-SUBTYPE-OF-ATOM-LIST (20 5 (:REWRITE O-P-O-INFP-CAR))
                                           (11 11 (:REWRITE DEFAULT-CAR))
                                           (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                                           (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>INTEGER-LIST (2 2 (:REWRITE DEFAULT-CDR))
                          (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::INTEGER-LIST=>DEF (3 3 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
                          (2 2 (:REWRITE DEFAULT-CAR))
                          (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-INTEGER-LIST-BUILTIN)
(ACL2S::NTH-INTEGER-LIST/ACC-BUILTIN)
(ACL2S::NTH-INTEGER-LIST)
(ACL2S::NTH-INTEGER-LIST/ACC)
(ACL2S::RATIONAL-LISTP-TESTTHM
     (20 5 (:REWRITE RATIONALP-X))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::RATIONAL-LISTP-IMPLIES-TLP)
(ACL2S::RATIONAL-LISTP-SUBTYPE-OF-ATOM-LIST (20 5 (:REWRITE O-P-O-INFP-CAR))
                                            (11 11 (:REWRITE DEFAULT-CAR))
                                            (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                                            (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>RATIONAL-LIST (2 2 (:REWRITE DEFAULT-CDR))
                           (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::RATIONAL-LIST=>DEF (3 3 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
                           (2 2 (:REWRITE DEFAULT-CAR))
                           (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-RATIONAL-LIST-BUILTIN)
(ACL2S::NTH-RATIONAL-LIST/ACC-BUILTIN)
(ACL2S::NTH-RATIONAL-LIST)
(ACL2S::NTH-RATIONAL-LIST/ACC)
(ACL2S::COMPLEX-RATIONAL-LISTP)
(ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP
     (332 2 (:DEFINITION TRUE-LISTP))
     (328 8 (:DEFINITION NAT-LISTP))
     (272 8 (:DEFINITION NATP))
     (180 4
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (180 4
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (176 4
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (160 4 (:DEFINITION ACL2S::POS-LISTP))
     (132 4 (:DEFINITION POSP))
     (64 4
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (56 4
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (48 4 (:DEFINITION RATIONAL-LISTP))
     (40 40 (:TYPE-PRESCRIPTION NAT-LISTP))
     (40 4 (:DEFINITION INTEGER-LISTP))
     (26 26 (:REWRITE DEFAULT-CAR))
     (24 24 (:REWRITE DEFAULT-CDR))
     (20 20 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (20 20 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (16 16 (:META META-INTEGERP-CORRECT))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
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
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>POS-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT)))
(ACL2S::COMPLEX-RATIONAL-LISTP-SUBTYPE-OF-ATOM-LIST
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (11 11 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>COMPLEX-RATIONAL-LIST (2 2 (:REWRITE DEFAULT-CDR))
                                   (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::COMPLEX-RATIONAL-LIST=>DEF
     (3 3
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-COMPLEX-RATIONAL-LIST-BUILTIN)
(ACL2S::NTH-COMPLEX-RATIONAL-LIST/ACC-BUILTIN)
(ACL2S::NTH-COMPLEX-RATIONAL-LIST)
(ACL2S::NTH-COMPLEX-RATIONAL-LIST/ACC)
(ACL2S::ACL2-NUMBER-LISTP-TESTTHM
     (45 5 (:REWRITE ACL2-NUMBERP-X))
     (20 5 (:REWRITE RATIONALP-X))
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP)
(ACL2S::ACL2-NUMBER-LISTP-SUBTYPE-OF-ATOM-LIST
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (11 11 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>ACL2-NUMBER-LIST (2 2 (:REWRITE DEFAULT-CDR))
                              (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::ACL2-NUMBER-LIST=>DEF (3 3
                                 (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
                              (2 2 (:REWRITE DEFAULT-CAR))
                              (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-ACL2-NUMBER-LIST-BUILTIN)
(ACL2S::NTH-ACL2-NUMBER-LIST/ACC-BUILTIN)
(ACL2S::NTH-ACL2-NUMBER-LIST)
(ACL2S::NTH-ACL2-NUMBER-LIST/ACC)
(ACL2S::BOOLEAN-LISTP-TESTTHM
     (53 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (50 10 (:REWRITE ACL2-NUMBERP-X))
     (20 5 (:REWRITE RATIONALP-X))
     (13 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (11 11 (:REWRITE DEFAULT-CDR))
     (11 11 (:REWRITE DEFAULT-CAR))
     (8 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
     (5 5 (:REWRITE REDUCE-RATIONALP-+))
     (5 5 (:REWRITE REDUCE-RATIONALP-*))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE RATIONALP-MINUS-X))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:META META-RATIONALP-CORRECT))
     (5 5 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|)))
(ACL2S::BOOLEAN-LISTP-IMPLIES-TLP)
(ACL2S::BOOLEAN-LISTP-SUBTYPE-OF-ATOM-LIST
     (40 8 (:REWRITE ACL2-NUMBERP-X))
     (40 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (17 17 (:REWRITE DEFAULT-CAR))
     (16 4 (:REWRITE RATIONALP-X))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT)))
(ACL2S::DEF=>BOOLEAN-LIST
     (20 4 (:REWRITE ACL2-NUMBERP-X))
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (8 2 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::BOOLEAN-LIST=>DEF
     (10 2 (:REWRITE ACL2-NUMBERP-X))
     (10 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
     (4 1 (:REWRITE RATIONALP-X))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1 (:REWRITE REDUCE-RATIONALP-+))
     (1 1 (:REWRITE REDUCE-RATIONALP-*))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE RATIONALP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:META META-RATIONALP-CORRECT))
     (1 1 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-BOOLEAN-LIST-BUILTIN)
(ACL2S::NTH-BOOLEAN-LIST/ACC-BUILTIN)
(ACL2S::NTH-BOOLEAN-LIST)
(ACL2S::NTH-BOOLEAN-LIST/ACC)
(ACL2S::SYMBOL-LISTP-TESTTHM
     (18 6
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (12 12
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::SYMBOL-LISTP-IMPLIES-TLP)
(ACL2S::SYMBOL-LISTP-SUBTYPE-OF-ATOM-LIST
     (24 8
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (16 16
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (11 11 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>SYMBOL-LIST
     (12 4
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (8 8
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::SYMBOL-LIST=>DEF
     (9 3
        (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (6 6
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (3 3 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-SYMBOL-LIST-BUILTIN)
(ACL2S::NTH-SYMBOL-LIST/ACC-BUILTIN)
(ACL2S::NTH-SYMBOL-LIST)
(ACL2S::NTH-SYMBOL-LIST/ACC)
(ACL2S::PROPER-SYMBOL-LISTP)
(ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP
     (464 2 (:DEFINITION TRUE-LISTP))
     (328 8 (:DEFINITION NAT-LISTP))
     (272 8 (:DEFINITION NATP))
     (180 4
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (180 4
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (176 4
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (160 4 (:DEFINITION ACL2S::POS-LISTP))
     (132 4 (:DEFINITION POSP))
     (112 4
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (96 4 (:DEFINITION BOOLEAN-LISTP))
     (64 4
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (60 4
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (56 4
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (48 4
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (48 4 (:DEFINITION RATIONAL-LISTP))
     (46 46 (:REWRITE DEFAULT-CAR))
     (44 44 (:REWRITE DEFAULT-CDR))
     (44 4
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (40 40 (:TYPE-PRESCRIPTION NAT-LISTP))
     (40 4 (:DEFINITION INTEGER-LISTP))
     (36 4 (:DEFINITION SYMBOL-LISTP))
     (32 4 (:DEFINITION ACL2-NUMBER-LISTP))
     (28 28 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (28 4
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (20 20 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (20 20 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (16 16 (:META META-INTEGERP-CORRECT))
     (16 8
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
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
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
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
     (8 8
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>POS-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (8 8
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (8 8
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT)))
(ACL2S::PROPER-SYMBOL-LISTP-SUBTYPE-OF-ATOM-LIST
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (13 13 (:REWRITE DEFAULT-CAR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>PROPER-SYMBOL-LIST (2 2 (:REWRITE DEFAULT-CDR))
                                (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::PROPER-SYMBOL-LIST=>DEF (3 3
                                   (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
                                (2 2 (:REWRITE DEFAULT-CAR))
                                (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-PROPER-SYMBOL-LIST-BUILTIN)
(ACL2S::NTH-PROPER-SYMBOL-LIST/ACC-BUILTIN)
(ACL2S::NTH-PROPER-SYMBOL-LIST)
(ACL2S::NTH-PROPER-SYMBOL-LIST/ACC)
(ACL2S::NTH-CHARACTER-LIST)
(ACL2S::NTH-CHARACTER-LIST/ACC-BUILTIN)
(ACL2S::NTH-CHARACTER-LIST/ACC)
(ACL2S::NTH-STANDARD-CHAR-LIST)
(ACL2S::NTH-STANDARD-CHAR-LIST/ACC-BUILTIN)
(ACL2S::NTH-STANDARD-CHAR-LIST/ACC)
(ACL2S::DEF=>STANDARD-CHAR-LIST (4 4 (:REWRITE DEFAULT-CAR))
                                (2 2 (:REWRITE DEFAULT-CDR)))
(ACL2S::STANDARD-CHAR-LIST=>DEF (2 2 (:REWRITE DEFAULT-CAR))
                                (2 2
                                   (:REWRITE ACL2S::DEF=>STANDARD-CHAR-LIST))
                                (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::STRING-LISTP-TESTTHM
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::STRING-LISTP-IMPLIES-TLP
     (540 2 (:DEFINITION TRUE-LISTP))
     (328 8 (:DEFINITION NAT-LISTP))
     (272 8 (:DEFINITION NATP))
     (180 4
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (180 4
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (176 4
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (160 4 (:DEFINITION ACL2S::POS-LISTP))
     (152 4
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (136 4
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (132 4 (:DEFINITION POSP))
     (112 4
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (100 4 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (96 4 (:DEFINITION BOOLEAN-LISTP))
     (80 4 (:DEFINITION KEYWORDP))
     (64 4
         (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (60 4
         (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (56 4
         (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (48 48 (:REWRITE DEFAULT-CDR))
     (48 4
         (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (48 4 (:DEFINITION RATIONAL-LISTP))
     (47 47 (:REWRITE DEFAULT-CAR))
     (44 4
         (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (40 40 (:TYPE-PRESCRIPTION NAT-LISTP))
     (40 4 (:DEFINITION INTEGER-LISTP))
     (36 4 (:DEFINITION SYMBOL-LISTP))
     (32 32
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (32 4 (:DEFINITION ACL2-NUMBER-LISTP))
     (28 28 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (28 4
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (20 20 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (20 20 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (20 20
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (16 16 (:META META-INTEGERP-CORRECT))
     (16 8
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (12 12 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (12 12 (:REWRITE THE-FLOOR-BELOW))
     (12 12 (:REWRITE THE-FLOOR-ABOVE))
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
     (12 12 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 12 (:REWRITE DEFAULT-LESS-THAN-1))
     (12 12 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
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
     (12 8
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 8
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 8
        (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (8 8
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (8 8
        (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>POS-LIST))
     (8 8 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (8 8
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (8 8
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4 (:REWRITE RATIONALP-X))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4
        (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (4 4 (:REWRITE ACL2-NUMBERP-X))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (4 4 (:META META-RATIONALP-CORRECT)))
(ACL2S::STRING-LISTP-SUBTYPE-OF-ATOM-LIST (20 5 (:REWRITE O-P-O-INFP-CAR))
                                          (11 11 (:REWRITE DEFAULT-CAR))
                                          (5 5 (:REWRITE O-P-DEF-O-FINP-1))
                                          (4 4 (:REWRITE DEFAULT-CDR)))
(ACL2S::DEF=>STRING-LIST (2 2 (:REWRITE DEFAULT-CDR))
                         (2 2 (:REWRITE DEFAULT-CAR)))
(ACL2S::STRING-LIST=>DEF (3 3 (:REWRITE ACL2S::DEF=>STRING-LIST))
                         (2 2 (:REWRITE DEFAULT-CAR))
                         (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-STRING-LIST-BUILTIN)
(ACL2S::NTH-STRING-LIST/ACC-BUILTIN)
(ACL2S::NTH-STRING-LIST)
(ACL2S::NTH-STRING-LIST/ACC)
(ACL2S::ATOM-LISTP-TESTTHM
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (10 10 (:TYPE-PRESCRIPTION O-P))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::ATOM-LISTP-IMPLIES-TLP)
(ACL2S::ATOM-LISTP-SUBTYPE-OF-ATOM-LIST)
(ACL2S::DEF=>ATOM-LIST (4 1 (:REWRITE O-P-O-INFP-CAR))
                       (2 2 (:TYPE-PRESCRIPTION O-P))
                       (2 2 (:REWRITE DEFAULT-CDR))
                       (2 2 (:REWRITE DEFAULT-CAR))
                       (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::ATOM-LIST=>DEF (4 1 (:REWRITE O-P-O-INFP-CAR))
                       (3 3 (:REWRITE ACL2S::DEF=>ATOM-LIST))
                       (2 2 (:TYPE-PRESCRIPTION O-P))
                       (2 2 (:REWRITE DEFAULT-CAR))
                       (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                       (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-ATOM-LIST-BUILTIN)
(ACL2S::NTH-ATOM-LIST/ACC-BUILTIN)
(ACL2S::NTH-ATOM-LIST)
(ACL2S::NTH-ATOM-LIST/ACC)
(ACL2S::POS-LIST-IS-SUBTYPE-OF-NAT-LIST
     (8 8 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (6 6 (:REWRITE CONSTANT-<-INTEGERP))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< c (- x))|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (6 6
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (6 6 (:REWRITE |(< (/ x) (/ y))|))
     (6 6 (:REWRITE |(< (- x) c)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE ACL2S::DEF=>POS-LIST))
     (5 5 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE DEFAULT-CDR))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:REWRITE |(< (/ x) 0)|))
     (3 3 (:REWRITE |(< (* x y) 0)|)))
(ACL2S::NAT-LIST-IS-SUBTYPE-OF-INTEGER-LIST)
(ACL2S::INTEGER-LIST-IS-SUBTYPE-OF-RATIONAL-LIST)
(ACL2S::COMPLEX-RATIONAL-LIST-IS-SUBTYPE-OF-ACL2-NUMBER-LIST
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (8 2 (:REWRITE RATIONALP-X))
     (7 7 (:REWRITE DEFAULT-CAR))
     (5 5
        (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (5 5
        (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (4 4 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::RATIONAL-LIST-IS-SUBTYPE-OF-ACL2-NUMBER-LIST)
(ACL2S::ACL2-NUMBER-LIST-IS-SUBTYPE-OF-ATOM-LIST)
(ACL2S::BOOLEAN-LIST-IS-SUBTYPE-OF-SYMBOL-LIST)
(ACL2S::STANDARD-CHAR-LIST-IS-SUBTYPE-OF-CHARACTER-LIST)
(ACL2S::CHARACTER-LIST-IS-SUBTYPE-OF-ATOM-LIST)
(ACL2S::STRING-LIST-IS-SUBTYPE-OF-ATOM-LIST)
(ACL2S::SYMBOL-LIST-IS-SUBTYPE-OF-ATOM-LIST)
(ACL2S::NTH-ALL-BUILTIN)
(ACL2S::NTH-ALL-UNIFORM-BUILTIN)
(ACL2S::NTH-ALL)
(ACL2S::NTH-ALL/ACC)
(ACL2S::NTH-QUOTE-BUILTIN)
(ACL2S::NTH-QUOTE-UNIFORM-BUILTIN)
(ACL2S::NTH-QUOTE)
(ACL2S::NTH-QUOTE/ACC)
(ACL2S::NTH-EMPTY)
(ACL2S::NTH-EMPTY/ACC)
(ACL2S::EMPTYP)
(ACL2S::EMPTYP-IS-TAU-PREDICATE)
(ACL2S::CONSP-TESTTHM (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                      (1 1
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                      (1 1
                         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                      (1 1
                         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                      (1 1
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                      (1 1
                         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                      (1 1 (:REWRITE DEFAULT-CDR))
                      (1 1 (:REWRITE DEFAULT-CAR))
                      (1 1 (:REWRITE |(equal x (if a b c))|))
                      (1 1 (:REWRITE |(equal c (/ x))|))
                      (1 1 (:REWRITE |(equal c (- x))|))
                      (1 1 (:REWRITE |(equal (if a b c) x)|))
                      (1 1 (:REWRITE |(equal (/ x) c)|))
                      (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                      (1 1 (:REWRITE |(equal (- x) c)|))
                      (1 1 (:REWRITE |(equal (- x) (- y))|)))
(DEF=>CONS)
(CONS=>DEF)
(ACL2S::NTH-CONS-BUILTIN)
(ACL2S::NTH-CONS/ACC-BUILTIN)
(ACL2S::NTH-CONS)
(ACL2S::NTH-CONS/ACC)
(ACONSP)
(ACONS=>DEF)
(ACL2S::NTH-ACONS-BUILTIN)
(ACL2S::NTH-ACONS/ACC-BUILTIN)
(ACL2S::NTH-ACONS)
(ACL2S::NTH-ACONS/ACC)
(ACL2S::ACONS-CAAR)
(ACL2S::ACONS-CDAR)
(ACL2S::ACONS-CDR)
(ACL2S::ACONS-ACL2-COUNT-LEMMA
     (630 12 (:DEFINITION INTEGER-ABS))
     (233 84 (:REWRITE DEFAULT-PLUS-1))
     (225 84 (:REWRITE DEFAULT-PLUS-2))
     (210 6 (:REWRITE |(+ (if a b c) x)|))
     (186 6 (:REWRITE NUMERATOR-NEGATIVE))
     (60 6 (:DEFINITION LENGTH))
     (55 55
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (55 55 (:REWRITE NORMALIZE-ADDENDS))
     (54 54 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
     (54 54
         (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
     (48 18 (:REWRITE DEFAULT-LESS-THAN-1))
     (42 12 (:REWRITE DEFAULT-MINUS))
     (42 6 (:DEFINITION LEN))
     (24 6 (:REWRITE RATIONALP-X))
     (20 20 (:REWRITE FOLD-CONSTS-IN-+))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 18
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 18
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (18 18 (:REWRITE INTEGERP-<-CONSTANT))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (/ x) (/ y))|))
     (18 18 (:REWRITE |(< (- x) c)|))
     (18 18 (:REWRITE |(< (- x) (- y))|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (14 14 (:REWRITE DEFAULT-CDR))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (12 12
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (12 12 (:REWRITE SIMPLIFY-SUMS-<))
     (12 12
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 12 (:REWRITE REDUCE-INTEGERP-+))
     (12 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (12 12 (:REWRITE INTEGERP-MINUS-X))
     (12 12 (:META META-INTEGERP-CORRECT))
     (8 8 (:REWRITE DEFAULT-CAR))
     (6 6 (:TYPE-PRESCRIPTION LEN))
     (6 6 (:REWRITE REDUCE-RATIONALP-+))
     (6 6 (:REWRITE REDUCE-RATIONALP-*))
     (6 6 (:REWRITE RATIONALP-MINUS-X))
     (6 6 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (6 6 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (6 6 (:REWRITE DEFAULT-REALPART))
     (6 6 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (6 6
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (6 6 (:REWRITE DEFAULT-IMAGPART))
     (6 6 (:REWRITE DEFAULT-COERCE-2))
     (6 6 (:REWRITE DEFAULT-COERCE-1))
     (6 6 (:META META-RATIONALP-CORRECT)))
(ACL2S::ACONS-CONSTRUCTOR-PRED)
(ACL2S::ACONS-CONSTRUCTOR-DESTRUCTORS)
(ACL2S::ACONS-ELIM-RULE (4 4 (:REWRITE DEFAULT-CAR))
                        (4 1 (:REWRITE O-P-O-INFP-CAR))
                        (2 2 (:REWRITE DEFAULT-CDR))
                        (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::ACONS-CONSTRUCTOR-DESTRUCTORS-PROPER)
(ACL2S::ACONS-ALIST-LEMMA (4 1 (:REWRITE O-P-O-INFP-CAR))
                          (2 2 (:TYPE-PRESCRIPTION O-P))
                          (2 2 (:REWRITE DEFAULT-CDR))
                          (2 2 (:REWRITE DEFAULT-CAR))
                          (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::LISTP-TESTTHM)
(DEF=>LIST)
(LIST=>DEF)
(ACL2S::NTH-LIST-BUILTIN)
(ACL2S::NTH-LIST/ACC-BUILTIN)
(ACL2S::NTH-LIST)
(ACL2S::NTH-LIST/ACC)
(ACL2S::NTH-TL-BUILTIN)
(ACL2S::NTH-TL/ACC-BUILTIN)
(ACL2S::NTH-TRUE-LIST-BUILTIN)
(ACL2S::NTH-TRUE-LIST-UNIFORM-BUILTIN)
(ACL2S::NTH-TRUE-LIST)
(ACL2S::NTH-TRUE-LIST/ACC)
(ACL2S::ALISTP-TESTTHM
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (8 8 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::ALISTP-IMPLIES-ALISTP)
(ACL2S::ALISTP-IMPLIES-TLP)
(ACL2S::DEF=>ALIST)
(ACL2S::ALIST=>DEF (4 1 (:REWRITE O-P-O-INFP-CAR))
                   (3 3 (:REWRITE ACL2S::DEF=>ALIST))
                   (2 2 (:REWRITE DEFAULT-CAR))
                   (1 1 (:REWRITE O-P-DEF-O-FINP-1))
                   (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-ALIST-BUILTIN)
(ACL2S::NTH-ALIST/ACC-BUILTIN)
(ACL2S::NTH-ALIST)
(ACL2S::NTH-ALIST/ACC)
(ACL2S::SYMBOL-ALISTP-TESTTHM
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::SYMBOL-ALISTP-IMPLIES-ALISTP)
(ACL2S::SYMBOL-ALISTP-IMPLIES-TLP)
(ACL2S::DEF=>SYMBOL-ALIST (6 6 (:REWRITE DEFAULT-CAR))
                          (4 1 (:REWRITE O-P-O-INFP-CAR))
                          (2 2 (:REWRITE DEFAULT-CDR))
                          (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::SYMBOL-ALIST=>DEF (16 4 (:REWRITE O-P-O-INFP-CAR))
                          (14 14 (:REWRITE DEFAULT-CAR))
                          (7 7 (:REWRITE ACL2S::DEF=>SYMBOL-ALIST))
                          (4 4 (:REWRITE O-P-DEF-O-FINP-1))
                          (3 3 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-SYMBOL-ALIST-BUILTIN)
(ACL2S::NTH-SYMBOL-ALIST/ACC-BUILTIN)
(ACL2S::NTH-SYMBOL-ALIST)
(ACL2S::NTH-SYMBOL-ALIST/ACC)
(ACL2S::CHARACTER-ALISTP-TESTTHM
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::CHARACTER-ALISTP-IMPLIES-ALISTP)
(ACL2S::CHARACTER-ALISTP-IMPLIES-TLP)
(ACL2S::DEF=>CHARACTER-ALIST (6 6 (:REWRITE DEFAULT-CAR))
                             (4 1 (:REWRITE O-P-O-INFP-CAR))
                             (2 2 (:REWRITE DEFAULT-CDR))
                             (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::CHARACTER-ALIST=>DEF (16 4 (:REWRITE O-P-O-INFP-CAR))
                             (14 14 (:REWRITE DEFAULT-CAR))
                             (7 7
                                (:REWRITE ACL2S::DEF=>CHARACTER-ALIST))
                             (4 4 (:REWRITE O-P-DEF-O-FINP-1))
                             (3 3 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-CHARACTER-ALIST-BUILTIN)
(ACL2S::NTH-CHARACTER-ALIST/ACC-BUILTIN)
(ACL2S::NTH-CHARACTER-ALIST)
(ACL2S::NTH-CHARACTER-ALIST/ACC)
(ACL2S::R-SYMBOL-ALISTP-TESTTHM
     (20 5 (:REWRITE O-P-O-INFP-CAR))
     (12 12 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
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
(ACL2S::R-SYMBOL-ALISTP-IMPLIES-ALISTP (32 8 (:REWRITE O-P-O-INFP-CAR))
                                       (21 21 (:REWRITE DEFAULT-CAR))
                                       (12 12 (:REWRITE DEFAULT-CDR))
                                       (8 8 (:REWRITE O-P-DEF-O-FINP-1))
                                       (5 5 (:REWRITE ACL2S::DEF=>ALIST)))
(ACL2S::R-SYMBOL-ALISTP-IMPLIES-TLP)
(ACL2S::DEF=>R-SYMBOL-ALIST (4 4 (:REWRITE DEFAULT-CDR))
                            (4 4 (:REWRITE DEFAULT-CAR))
                            (4 1 (:REWRITE O-P-O-INFP-CAR))
                            (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::R-SYMBOL-ALIST=>DEF (16 4 (:REWRITE O-P-O-INFP-CAR))
                            (10 10 (:REWRITE DEFAULT-CAR))
                            (7 7 (:REWRITE DEFAULT-CDR))
                            (7 7 (:REWRITE ACL2S::DEF=>R-SYMBOL-ALIST))
                            (4 4 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::NTH-R-SYMBOL-ALIST-BUILTIN)
(ACL2S::NTH-R-SYMBOL-ALIST/ACC-BUILTIN)
(ACL2S::NTH-R-SYMBOL-ALIST)
(ACL2S::NTH-R-SYMBOL-ALIST/ACC)
(ACL2S::SYMBOL-ALIST-IS-SUBTYPE-OF-ALIST)
(ACL2S::CHARACTER-ALIST-IS-SUBTYPE-OF-ALIST)
(ACL2S::R-SYMBOL-ALIST-IS-SUBTYPE-OF-ALIST)
(ACL2S::TRUE-LIST-LISTP-TESTTHM
     (1490 5 (:DEFINITION TRUE-LISTP))
     (850 20 (:DEFINITION NAT-LISTP))
     (680 20 (:DEFINITION NATP))
     (470 10
          (:REWRITE DEFDATA::NAT-LISTP--TRUE-LISTP))
     (460 10
          (:REWRITE ACL2S::NAT-LISTP-IMPLIES-TLP))
     (450 10
          (:REWRITE ACL2S::POS-LISTP-IMPLIES-TLP))
     (410 10 (:DEFINITION ACL2S::POS-LISTP))
     (390 10
          (:REWRITE ACL2S::PROPER-SYMBOL-LISTP-IMPLIES-TLP))
     (350 10
          (:DEFINITION ACL2S::PROPER-SYMBOL-LISTP))
     (330 10 (:DEFINITION POSP))
     (290 10
          (:REWRITE ACL2S::BOOLEAN-LISTP-IMPLIES-TLP))
     (250 10 (:DEFINITION ACL2S::PROPER-SYMBOLP))
     (250 10 (:DEFINITION BOOLEAN-LISTP))
     (200 10 (:DEFINITION KEYWORDP))
     (170 75 (:REWRITE O-P-O-INFP-CAR))
     (170 10
          (:REWRITE ACL2S::RATIONAL-LISTP-IMPLIES-TLP))
     (160 10
          (:REWRITE ACL2S::SYMBOL-LISTP-IMPLIES-TLP))
     (150 10
          (:REWRITE ACL2S::INTEGER-LISTP-IMPLIES-TLP))
     (140 140 (:REWRITE DEFAULT-CDR))
     (140 10
          (:REWRITE ACL2S::ATOM-LISTP-IMPLIES-TLP))
     (135 135 (:REWRITE DEFAULT-CAR))
     (130 10
          (:REWRITE ACL2S::ACL2-NUMBER-LISTP-IMPLIES-TLP))
     (130 10 (:DEFINITION RATIONAL-LISTP))
     (120 10
          (:REWRITE ACL2S::STRING-LISTP-IMPLIES-TLP))
     (120 10
          (:REWRITE ACL2S::COMPLEX-RATIONAL-LISTP-IMPLIES-TLP))
     (110 10 (:DEFINITION INTEGER-LISTP))
     (100 100 (:TYPE-PRESCRIPTION NAT-LISTP))
     (100 10 (:DEFINITION SYMBOL-LISTP))
     (100 10 (:DEFINITION ATOM-LISTP))
     (90 10 (:DEFINITION ACL2-NUMBER-LISTP))
     (85 85 (:TYPE-PRESCRIPTION O-P))
     (80 80
         (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
     (80 10 (:DEFINITION STRING-LISTP))
     (80 10
         (:DEFINITION ACL2S::COMPLEX-RATIONAL-LISTP))
     (70 70 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
     (50 50 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (50 50 (:TYPE-PRESCRIPTION STRING-LISTP))
     (50 50 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (50 50
         (:TYPE-PRESCRIPTION ACL2S::PROPER-SYMBOL-LISTP))
     (50 50
         (:TYPE-PRESCRIPTION ACL2S::POS-LISTP))
     (50 50 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (50 50
         (:TYPE-PRESCRIPTION ACL2S::COMPLEX-RATIONAL-LISTP))
     (50 50 (:TYPE-PRESCRIPTION ATOM-LISTP))
     (50 50
         (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (40 40 (:REWRITE REDUCE-INTEGERP-+))
     (40 40 (:REWRITE INTEGERP-MINUS-X))
     (40 40 (:REWRITE ACL2S::DEF=>NAT-LIST))
     (40 40 (:META META-INTEGERP-CORRECT))
     (40 20
         (:REWRITE DEFDATA::PROPER-SYMBOL-LISTP-IS-SYMBOL-LIST))
     (32 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (32 21
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (30 30 (:TYPE-PRESCRIPTION LEGAL-CONSTANTP))
     (30 30 (:REWRITE THE-FLOOR-BELOW))
     (30 30 (:REWRITE THE-FLOOR-ABOVE))
     (30 30 (:REWRITE SIMPLIFY-SUMS-<))
     (30 30
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (30 30
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (30 30
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (30 30
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (30 30
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (30 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (30 30 (:REWRITE INTEGERP-<-CONSTANT))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-2))
     (30 30 (:REWRITE DEFAULT-LESS-THAN-1))
     (30 30 (:REWRITE ACL2S::DEF=>BOOLEAN-LIST))
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
     (22 21 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (21 21
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (21 21 (:REWRITE |(equal c (/ x))|))
     (21 21 (:REWRITE |(equal c (- x))|))
     (21 21 (:REWRITE |(equal (/ x) c)|))
     (21 21 (:REWRITE |(equal (/ x) (/ y))|))
     (21 21 (:REWRITE |(equal (- x) c)|))
     (21 21 (:REWRITE |(equal (- x) (- y))|))
     (20 20
         (:TYPE-PRESCRIPTION DEFDATA::PROPER-SYMBOL-LISTP))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (20 20
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (20 20 (:REWRITE ACL2S::DEF=>SYMBOL-LIST))
     (20 20 (:REWRITE ACL2S::DEF=>STRING-LIST))
     (20 20 (:REWRITE ACL2S::DEF=>RATIONAL-LIST))
     (20 20
         (:REWRITE ACL2S::DEF=>PROPER-SYMBOL-LIST))
     (20 20 (:REWRITE ACL2S::DEF=>POS-LIST))
     (20 20 (:REWRITE ACL2S::DEF=>INTEGER-LIST))
     (20 20
         (:REWRITE ACL2S::DEF=>COMPLEX-RATIONAL-LIST))
     (20 20 (:REWRITE ACL2S::DEF=>ATOM-LIST))
     (20 20
         (:REWRITE ACL2S::DEF=>ACL2-NUMBER-LIST))
     (20 20 (:REWRITE |(< (/ x) 0)|))
     (20 20 (:REWRITE |(< (* x y) 0)|))
     (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (10 10 (:REWRITE REDUCE-RATIONALP-+))
     (10 10 (:REWRITE REDUCE-RATIONALP-*))
     (10 10 (:REWRITE RATIONALP-X))
     (10 10 (:REWRITE RATIONALP-MINUS-X))
     (10 10 (:REWRITE O-P-DEF-O-FINP-1))
     (10 10
         (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
     (10 10 (:REWRITE ACL2-NUMBERP-X))
     (10 10 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE |(< 0 (* x y))|))
     (10 10 (:META META-RATIONALP-CORRECT))
     (2 2 (:REWRITE |(equal (if a b c) x)|)))
(ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP)
(ACL2S::DEF=>TRUE-LIST-LIST
     (16 3
         (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR)))
(ACL2S::TRUE-LIST-LIST=>DEF (5 1
                               (:REWRITE ACL2S::TRUE-LIST-LISTP-IMPLIES-TLP))
                            (4 4 (:REWRITE ACL2S::DEF=>TRUE-LIST-LIST))
                            (2 2 (:REWRITE DEFAULT-CAR))
                            (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::NTH-TRUE-LIST-LIST-BUILTIN)
(ACL2S::NTH-TRUE-LIST-LIST/ACC-BUILTIN)
(ACL2S::NTH-TRUE-LIST-LIST)
(ACL2S::NTH-TRUE-LIST-LIST/ACC)
(ACL2S::TRUE-LIST-LIST-IS-SUBTYPE-OF-TRUE-LIST)
(ACL2S::CONS-IS-SUBTYPE-OF-Z)
(ACL2S::LIST-IS-SUBTYPE-OF-Z)
(ACL2S::ALL-BUT-ZERO-NIL-TP)
(ACL2S::NTH-ALL-BUT-ZERO-NIL-T-BUILTIN)
(ACL2S::NTH-ALL-BUT-ZERO-NIL-T-UNIFORM-BUILTIN)
(ACL2S::NTH-ALL-BUT-ZERO-NIL-T)
(ACL2S::NTH-ALL-BUT-ZERO-NIL-T/ACC)
(ACL2S::NTH-WF-KEY-BUILTIN)
(ACL2S::NTH-WF-KEY)
(ACL2S::NTH-WF-KEY/ACC-BUILTIN)
(ACL2S::NTH-WF-KEY/ACC)
(ACL2S::ALL-BUT-NILP)
(ACL2S::MSET-CONSTRUCTOR-PRED
     (71 1 (:DEFINITION GOOD-MAP))
     (20 4 (:REWRITE ACL2-NUMBERP-X))
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (19 5 (:REWRITE <<-TRICHOTOMY))
     (17 3 (:REWRITE <<-ASYMMETRIC))
     (14 8 (:REWRITE DEFAULT-CAR))
     (11 11 (:TYPE-PRESCRIPTION <<))
     (10 2 (:REWRITE O-P-O-INFP-CAR))
     (8 2 (:REWRITE RATIONALP-X))
     (5 5 (:REWRITE <<-TRANSITIVE))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 2 (:REWRITE O-P-DEF-O-FINP-1))
     (2 2 (:TYPE-PRESCRIPTION O-FINP))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT)))
(ACL2S::MSET-CONSTRUCTOR-DESTRUCTORS
     (76 20 (:REWRITE <<-TRICHOTOMY))
     (68 12 (:REWRITE <<-ASYMMETRIC))
     (62 38 (:REWRITE DEFAULT-CAR))
     (40 8 (:REWRITE O-P-O-INFP-CAR))
     (40 8 (:REWRITE ACL2-NUMBERP-X))
     (40 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 20 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE <<-TRANSITIVE))
     (16 8 (:REWRITE O-P-DEF-O-FINP-1))
     (16 4 (:REWRITE RATIONALP-X))
     (8 8 (:TYPE-PRESCRIPTION O-FINP))
     (8 4
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4 (:REWRITE REDUCE-RATIONALP-+))
     (4 4 (:REWRITE REDUCE-RATIONALP-*))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4 (:REWRITE RATIONALP-MINUS-X))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (4 4 (:META META-RATIONALP-CORRECT))
     (4 4 (:META META-INTEGERP-CORRECT)))
(ACL2S::NTH-ALL-BUT-NIL-BUILTIN)
(ACL2S::NTH-ALL-BUT-NIL)
(ACL2S::NTH-ALL-BUT-NIL/ACC-BUILTIN)
(ACL2S::NTH-ALL-BUT-NIL/ACC)
(ACL2S::ALL-BUT-ZERO-NIL-T-IS-SUBTYPE-OF-ALL)
(ACL2S::ALL-BUT-NIL-IS-SUBTYPE-OF-ALL)
(ACL2S::ACONS-IS-SUBTYPE-OF-CONS)
(ACL2S::CONS-IS-SUBTYPE-OF-ALL-BUT-NIL)
(ACL2S::ATOM-IS-SUBTYPE-OF-ALL)
(ACL2S::ATOM-LIST-IS-SUBTYPE-OF-TRUE-LIST)
(ACL2S::ALIST-IS-SUBTYPE-OF-TRUE-LIST)
(ACL2S::LIST-IS-SUBTYPE-OF-ALL)
(ACL2S::TRUE-LIST-IS-SUBTYPE-OF-LIST)
(ACL2S::CONS-CCCCA-CCCCAP)
(ACL2S::DEF=>CONS-CCCCA-CCCCA (1 1 (:REWRITE DEFAULT-CDR))
                              (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CCCCA-CCCCA=>DEF)
(ACL2S::NTH-CONS-CCCCA-CCCCA-BUILTIN)
(ACL2S::NTH-CONS-CCCCA-CCCCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-CCCCA-CCCCA)
(ACL2S::NTH-CONS-CCCCA-CCCCA/ACC)
(ACL2S::CONS-A-CAP)
(ACL2S::DEF=>CONS-A-CA (1 1 (:REWRITE DEFAULT-CDR))
                       (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-A-CA=>DEF)
(ACL2S::NTH-CONS-A-CA-BUILTIN)
(ACL2S::NTH-CONS-A-CA/ACC-BUILTIN)
(ACL2S::NTH-CONS-A-CA)
(ACL2S::NTH-CONS-A-CA/ACC)
(ACL2S::CONS-A-CCAP)
(ACL2S::DEF=>CONS-A-CCA (1 1 (:REWRITE DEFAULT-CDR))
                        (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-A-CCA=>DEF)
(ACL2S::NTH-CONS-A-CCA-BUILTIN)
(ACL2S::NTH-CONS-A-CCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-A-CCA)
(ACL2S::NTH-CONS-A-CCA/ACC)
(ACL2S::CONS-A-CCCCAP)
(ACL2S::DEF=>CONS-A-CCCCA (1 1 (:REWRITE DEFAULT-CDR))
                          (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-A-CCCCA=>DEF)
(ACL2S::NTH-CONS-A-CCCCA-BUILTIN)
(ACL2S::NTH-CONS-A-CCCCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-A-CCCCA)
(ACL2S::NTH-CONS-A-CCCCA/ACC)
(ACL2S::CONS-CA-CCAP)
(ACL2S::DEF=>CONS-CA-CCA (1 1 (:REWRITE DEFAULT-CDR))
                         (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CA-CCA=>DEF)
(ACL2S::NTH-CONS-CA-CCA-BUILTIN)
(ACL2S::NTH-CONS-CA-CCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-CA-CCA)
(ACL2S::NTH-CONS-CA-CCA/ACC)
(ACL2S::CONS-CA-CCCCAP)
(ACL2S::DEF=>CONS-CA-CCCCA (1 1 (:REWRITE DEFAULT-CDR))
                           (1 1 (:REWRITE DEFAULT-CAR)))
(ACL2S::CONS-CA-CCCCA=>DEF)
(ACL2S::NTH-CONS-CA-CCCCA-BUILTIN)
(ACL2S::NTH-CONS-CA-CCCCA/ACC-BUILTIN)
(ACL2S::NTH-CONS-CA-CCCCA)
(ACL2S::NTH-CONS-CA-CCCCA/ACC)
(ACL2S::CONS-ALL-ALL-BUT-ZERO-NIL-TP)
(ACL2S::DEF=>CONS-ALL-ALL-BUT-ZERO-NIL-T (1 1 (:REWRITE DEFAULT-CDR)))
(ACL2S::CONS-ALL-ALL-BUT-ZERO-NIL-T=>DEF)
(ACL2S::NTH-CONS-ALL-ALL-BUT-ZERO-NIL-T-BUILTIN)
(ACL2S::NTH-CONS-ALL-ALL-BUT-ZERO-NIL-T/ACC-BUILTIN)
(ACL2S::NTH-CONS-ALL-ALL-BUT-ZERO-NIL-T)
(ACL2S::NTH-CONS-ALL-ALL-BUT-ZERO-NIL-T/ACC)
(ACL2S::NTH-IMPROPER-CONS-BUILTIN)
(ACL2S::NTH-IMPROPER-CONS-UNIFORM-BUILTIN)
(ACL2S::NTH-IMPROPER-CONS)
(ACL2S::NTH-IMPROPER-CONS/ACC)
(ACL2S::IMPROPER-CONS-IS-SUBTYPE-OF-CONS)
(ACL2S::PROPER-CONS-IS-SUBTYPE-OF-CONS)
(ACL2S::PROPER-CONS-IS-SUBTYPE-OF-TRUE-LIST)
(ACL2S::PROPER-CONS-IS-DISJOINT-WITH-IMPROPER-CONS)
(ACL2S::ATOM-IS-DISJOINT-WITH-CONS)
(ACL2S::NTH-EVEN-BUILTIN)
(ACL2S::NTH-EVEN)
(ACL2S::NTH-EVEN/ACC-BUILTIN)
(ACL2S::NTH-EVEN/ACC)
(ACL2S::NTH-ODD-BUILTIN)
(ACL2S::NTH-ODD)
(ACL2S::NTH-ODD/ACC-BUILTIN)
(ACL2S::NTH-ODD/ACC)
(ACL2S::VAR-IS-SUBTYPE-OF-SYMBOL)
(DEFDATA::SYM-AALISTP)
(ACL2S::SYM-AALISTP-IMPLIES-ALISTP (28 7 (:REWRITE O-P-O-INFP-CAR))
                                   (23 23 (:REWRITE DEFAULT-CAR))
                                   (8 8 (:REWRITE DEFAULT-CDR))
                                   (7 7 (:REWRITE O-P-DEF-O-FINP-1))
                                   (5 5 (:REWRITE ACL2S::DEF=>ALIST)))
(ACL2S::SYM-AALISTP-IMPLIES-TLP)
(DEFDATA::DEF=>SYM-AALIST)
(DEFDATA::SYM-AALIST=>DEF (4 4 (:REWRITE DEFAULT-CAR))
                          (4 1 (:REWRITE O-P-O-INFP-CAR))
                          (2 2 (:REWRITE DEFAULT-CDR))
                          (2 2 (:REWRITE DEFDATA::DEF=>SYM-AALIST))
                          (1 1 (:REWRITE O-P-DEF-O-FINP-1)))
(ACL2S::NTH-SYM-AALIST-BUILTIN)
(ACL2S::NTH-SYM-AALIST/ACC-BUILTIN)
(ACL2S::NTH-SYM-AALIST)
(ACL2S::NTH-SYM-AALIST/ACC)
(ACL2S::SYM-AALIST-SYM-AALIST1
     (80 20 (:REWRITE O-P-O-INFP-CAR))
     (78 78 (:REWRITE DEFAULT-CAR))
     (24 24 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE O-P-DEF-O-FINP-1))
     (20 20 (:REWRITE ACL2S::DEF=>SYMBOL-ALIST))
     (8 8 (:REWRITE DEFDATA::DEF=>SYM-AALIST))
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
