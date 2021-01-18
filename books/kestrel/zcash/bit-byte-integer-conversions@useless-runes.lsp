(ZCASH::I2LEBSP (26 2 (:DEFINITION EXPT))
                (6 2 (:REWRITE DEFAULT-*-2))
                (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                (4 4 (:REWRITE DEFAULT-<-2))
                (4 4 (:REWRITE DEFAULT-<-1))
                (4 4 (:REWRITE DEFAULT-+-2))
                (4 4 (:REWRITE DEFAULT-+-1))
                (2 2 (:REWRITE ZIP-OPEN))
                (2 2 (:REWRITE DEFAULT-*-1)))
(ZCASH::BIT-LISTP-OF-I2LEBSP)
(ZCASH::LEN-OF-I2LEBSP)
(ZCASH::I2BEBSP (26 2 (:DEFINITION EXPT))
                (6 2 (:REWRITE DEFAULT-*-2))
                (6 2 (:REWRITE COMMUTATIVITY-OF-+))
                (4 4 (:REWRITE DEFAULT-<-2))
                (4 4 (:REWRITE DEFAULT-<-1))
                (4 4 (:REWRITE DEFAULT-+-2))
                (4 4 (:REWRITE DEFAULT-+-1))
                (2 2 (:REWRITE ZIP-OPEN))
                (2 2 (:REWRITE DEFAULT-*-1)))
(ZCASH::BIT-LISTP-OF-I2BEBSP)
(ZCASH::LEN-OF-I2BEBSP)
(ZCASH::LEBS2IP)
(ZCASH::NATP-OF-LEBS2IP)
(ZCASH::LEBS2IP-UPPER-BOUND
     (7 1 (:DEFINITION LEN))
     (2 1 (:REWRITE DEFAULT-EXPT-2))
     (2 1 (:REWRITE DEFAULT-+-2))
     (2 1 (:REWRITE |(expt 2^i n)|))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1
        (:REWRITE LEBITS=>NAT-OF-BIT-LIST-FIX-DIGITS-NORMALIZE-CONST))
     (1 1 (:REWRITE DEFAULT-EXPT-1))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(expt x (- n))|))
     (1 1 (:REWRITE |(expt 1/c n)|))
     (1 1 (:REWRITE |(expt (- x) n)|)))
(ZCASH::LEOS2IP)
(ZCASH::NATP-OF-LEOS2IP)
(ZCASH::LEOS2IP-UPPER-BOUND
     (7 1 (:DEFINITION LEN))
     (2 1 (:REWRITE DEFAULT-EXPT-2))
     (2 1 (:REWRITE DEFAULT-+-2))
     (2 1 (:REWRITE DEFAULT-*-2))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1
        (:REWRITE LEBYTES=>NAT-OF-BYTE-LIST-FIX-DIGITS-NORMALIZE-CONST))
     (1 1 (:REWRITE DEFAULT-EXPT-1))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE DEFAULT-*-1))
     (1 1 (:REWRITE |(expt x (- n))|))
     (1 1 (:REWRITE |(expt 1/c n)|))
     (1 1 (:REWRITE |(expt (- x) n)|)))
(ZCASH::LEBS2OSP
     (7701 3 (:REWRITE ZP-OPEN))
     (6480 3 (:REWRITE |(< x (if a b c))|))
     (6172 37
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5634 1 (:REWRITE SUBSETP-APPEND1))
     (5630 1 (:REWRITE SUBSETP-OF-REPEAT))
     (4724 69 (:REWRITE DEFAULT-PLUS-2))
     (3524 3524
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (3524 3524
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (3524 3524
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (2872 1 (:REWRITE REPEAT-WHEN-ZP))
     (2197 169 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (1846 7 (:REWRITE |(< (+ (- c) x) y)|))
     (1521 169
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (1521 169
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (1521 169
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (1511 42 (:REWRITE DEFAULT-LESS-THAN-2))
     (1127 122 (:REWRITE DEFAULT-TIMES-2))
     (1010 31
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (845 169 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (845 169 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (845 169
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (644 42 (:REWRITE DEFAULT-LESS-THAN-1))
     (604 13 (:REWRITE |(+ c (+ d x))|))
     (511 26 (:REWRITE SIMPLIFY-SUMS-<))
     (395 69 (:REWRITE DEFAULT-PLUS-1))
     (348 122 (:REWRITE DEFAULT-TIMES-1))
     (348 6 (:REWRITE FLOOR-ZERO . 3))
     (255 6 (:REWRITE CANCEL-FLOOR-+))
     (210 6 (:REWRITE FLOOR-ZERO . 4))
     (210 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (144 6 (:REWRITE FLOOR-ZERO . 5))
     (99 12 (:REWRITE INTEGERP-MINUS-X))
     (91 1 (:DEFINITION MEMBER-EQUAL))
     (87 12 (:REWRITE |(* (- x) y)|))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (77 77 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (75 6 (:REWRITE FLOOR-=-X/Y . 3))
     (69 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (63 63
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (60 12 (:REWRITE |(- (* c x))|))
     (54 3 (:REWRITE ACL2-NUMBERP-X))
     (48 6 (:REWRITE FLOOR-=-X/Y . 2))
     (48 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (43 37
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (43 37
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (43 14 (:REWRITE DEFAULT-MINUS))
     (42 42 (:REWRITE THE-FLOOR-BELOW))
     (42 42 (:REWRITE THE-FLOOR-ABOVE))
     (36 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (34 31 (:REWRITE |(< c (- x))|))
     (33 31 (:REWRITE |(< (- x) c)|))
     (33 31 (:REWRITE |(< (- x) (- y))|))
     (33 6 (:REWRITE FLOOR-ZERO . 2))
     (33 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (33 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (33 6
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (33 6 (:REWRITE FLOOR-CANCEL-*-CONST))
     (33 6
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (31 31
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (31 31 (:REWRITE INTEGERP-<-CONSTANT))
     (31 31 (:REWRITE CONSTANT-<-INTEGERP))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (31 31
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (31 31
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (31 31
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (31 31 (:REWRITE |(< (/ x) (/ y))|))
     (28 2 (:REWRITE RATIONALP-X))
     (25 2
         (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
     (23 23
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (21 1 (:DEFINITION RATIONAL-LISTP))
     (20 3
         (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
     (17 3
         (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (14 2 (:DEFINITION LEN))
     (14 1 (:DEFINITION INTEGER-LISTP))
     (12 12 (:TYPE-PRESCRIPTION ABS))
     (12 6
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (12 1 (:DEFINITION ACL2-NUMBER-LISTP))
     (11 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (9 9 (:REWRITE |(< x (+ c/d y))|))
     (9 6 (:REWRITE DEFAULT-FLOOR-1))
     (9 6
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (8 8 (:TYPE-PRESCRIPTION INTEGER-LISTP))
     (7 7 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
     (7 7
        (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
     (7 7 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (6 6 (:REWRITE |(floor x (- y))| . 2))
     (6 6 (:REWRITE |(floor x (- y))| . 1))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (6 6
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(floor (- x) y)| . 2))
     (6 6 (:REWRITE |(floor (- x) y)| . 1))
     (6 6
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (6 6 (:REWRITE |(< y (+ (- c) x))|))
     (6 6 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 1 (:DEFINITION BINARY-APPEND))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE SUBSETP-TRANS2))
     (2 2 (:REWRITE SUBSETP-TRANS))
     (2 2 (:REWRITE SUBSETP-MEMBER . 2))
     (2 2 (:REWRITE SUBSETP-MEMBER . 1))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
     (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 1
        (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
     (2 1
        (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
     (2 1
        (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
     (1 1 (:TYPE-PRESCRIPTION ZP))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE BIT-LISTP-WHEN-NOT-CONSP))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(ZCASH::BYTE-LISTP-OF-LEBS2OSP)
(ZCASH::LEN-OF-LEBS2OSP
   (10505 1 (:REWRITE |(floor (+ x r) i)|))
   (8657 56
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
   (6873 6873
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
   (6873 6873
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
   (6873 6873
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
   (5248 80 (:REWRITE DEFAULT-PLUS-2))
   (4611 53 (:REWRITE INTEGERP-<-CONSTANT))
   (4303 331 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
   (4269 343 (:REWRITE DEFAULT-TIMES-2))
   (3649 10 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
   (3432 343 (:REWRITE DEFAULT-TIMES-1))
   (3387 21 (:REWRITE DEFAULT-FLOOR-RATIO))
   (2979 331
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
   (2979 331
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
   (2979 331
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
   (2872 1 (:REWRITE REPEAT-WHEN-ZP))
   (2666 1 (:REWRITE ZP-OPEN))
   (2160 1 (:REWRITE |(< x (if a b c))|))
   (2159 5 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
   (2156 58 (:REWRITE THE-FLOOR-BELOW))
   (2100 55
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
   (1757 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
   (1655 331 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
   (1655 331 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
   (1655 331
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
   (1181 80 (:REWRITE DEFAULT-PLUS-1))
   (790 17 (:REWRITE CANCEL-FLOOR-+))
   (752 58 (:REWRITE DEFAULT-LESS-THAN-2))
   (729 2 (:DEFINITION NOT))
   (666 52
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
   (664 58 (:REWRITE DEFAULT-LESS-THAN-1))
   (634 21 (:REWRITE DEFAULT-FLOOR-1))
   (616 3 (:REWRITE |(< (+ (- c) x) y)|))
   (594 17 (:REWRITE FLOOR-X-Y-=-1 . 2))
   (533 17 (:REWRITE FLOOR-ZERO . 5))
   (471 17 (:REWRITE FLOOR-ZERO . 3))
   (291 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
   (291 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
   (289 20 (:REWRITE INTEGERP-MINUS-X))
   (289 17 (:REWRITE FLOOR-ZERO . 4))
   (269 34 (:REWRITE |(* (- x) y)|))
   (244 50 (:REWRITE SIMPLIFY-SUMS-<))
   (204 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
   (185 34 (:REWRITE |(- (* c x))|))
   (170 170
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
   (161 161
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
   (161 161
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
   (161 161
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
   (154 58 (:REWRITE THE-FLOOR-ABOVE))
   (151 17 (:REWRITE FLOOR-=-X/Y . 2))
   (120 35 (:REWRITE DEFAULT-MINUS))
   (117 17 (:REWRITE FLOOR-X-Y-=--1 . 2))
   (101 17 (:REWRITE FLOOR-ZERO . 2))
   (101 17 (:REWRITE FLOOR-X-Y-=-1 . 3))
   (101 17 (:REWRITE FLOOR-X-Y-=--1 . 3))
   (97 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
   (87 17
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
   (87 17
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
   (65 55
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
   (65 2 (:REWRITE FLOOR-POSITIVE . 2))
   (62 5 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
   (61 17 (:REWRITE FLOOR-CANCEL-*-CONST))
   (60 2 (:REWRITE FLOOR-NONPOSITIVE . 1))
   (54 53 (:REWRITE |(< c (- x))|))
   (54 53 (:REWRITE |(< (- x) c)|))
   (54 53 (:REWRITE |(< (- x) (- y))|))
   (53 53 (:REWRITE CONSTANT-<-INTEGERP))
   (53 53
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
   (53 53
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
   (53 53
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
   (53 53
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
   (53 53
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
   (53 53
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
   (53 53
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
   (53 53
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
   (53 53 (:REWRITE |(< (/ x) (/ y))|))
   (52 52
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
   (44 2 (:REWRITE FLOOR-NONPOSITIVE . 2))
   (40 2 (:REWRITE FLOOR-POSITIVE . 3))
   (35 35 (:REWRITE REMOVE-WEAK-INEQUALITIES))
   (31 17
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
   (31 17
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
   (29 29
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
   (22 22 (:TYPE-PRESCRIPTION ABS))
   (22 8
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
   (21 21 (:REWRITE DEFAULT-FLOOR-2))
   (21 3 (:DEFINITION LEN))
   (17 17 (:REWRITE |(floor x (- y))| . 2))
   (17 17 (:REWRITE |(floor x (- y))| . 1))
   (17 17
       (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
   (17 17
       (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
   (17 17 (:REWRITE |(floor (- x) y)| . 2))
   (17 17 (:REWRITE |(floor (- x) y)| . 1))
   (17 17 (:REWRITE |(< 0 (* x y))|))
   (16 16
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
   (16 16
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
   (16 16 (:REWRITE |(< 0 (/ x))|))
   (15 8
       (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
   (14 1 (:REWRITE FLOOR-=-X/Y . 4))
   (12 2 (:REWRITE FLOOR-POSITIVE . 4))
   (12 2 (:REWRITE FLOOR-NONPOSITIVE . 3))
   (7 1 (:DEFINITION BINARY-APPEND))
   (6 1
      (:REWRITE |(equal (floor (+ x y) z) x)|))
   (4 4 (:REWRITE DEFAULT-CDR))
   (4 3
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
   (3 3 (:REWRITE REDUCE-INTEGERP-+))
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
   (3 3 (:REWRITE |(< x (+ c/d y))|))
   (3 3 (:REWRITE |(< (+ c/d x) y)|))
   (3 3 (:META META-INTEGERP-CORRECT))
   (3 1
      (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
   (2 2 (:REWRITE FOLD-CONSTS-IN-+))
   (2 2 (:REWRITE FLOOR-POSITIVE . 1))
   (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
   (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
   (2 2 (:REWRITE |(< y (+ (- c) x))|))
   (2 1
      (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
   (1 1 (:TYPE-PRESCRIPTION ZP))
   (1 1
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
   (1 1 (:REWRITE FLOOR-ZERO . 1))
   (1 1 (:REWRITE DEFAULT-CAR))
   (1 1
      (:REWRITE CONS-OF-BIT-LIST-FIX-Y-NORMALIZE-CONST-UNDER-BIT-LIST-EQUIV))
   (1 1
      (:REWRITE CONS-OF-BFIX-X-NORMALIZE-CONST-UNDER-BIT-LIST-EQUIV))
   (1 1
      (:REWRITE CAR-OF-BIT-LIST-FIX-X-NORMALIZE-CONST-UNDER-BIT-EQUIV))
   (1 1
      (:REWRITE BITS=>LEBYTES-OF-BIT-LIST-FIX-DIGITS-NORMALIZE-CONST))
   (1 1
      (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
   (1 1 (:REWRITE |(< (/ x) 0)|))
   (1 1 (:REWRITE |(< (* x y) 0)|)))
(ZCASH::LEOS2BSP)
(ZCASH::BIT-LISTP-OF-LEOS2BSP)
(ZCASH::LEN-OF-LEOS2BSP (10 2 (:DEFINITION LEN))
                        (5 3 (:REWRITE DEFAULT-*-2))
                        (4 3 (:REWRITE DEFAULT-*-1))
                        (4 2 (:REWRITE DEFAULT-+-2))
                        (2 2 (:REWRITE DEFAULT-CDR))
                        (2 2 (:REWRITE DEFAULT-+-1)))
