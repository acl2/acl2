(IND-FN (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
        (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
        (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
        (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
        (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
        (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
        (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
        (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
        (30 6
            (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(CROCK-1
 (2620 2620
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2620 2620
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2620 2620
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2620 2620
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1427 34 (:REWRITE DEFAULT-PLUS-1))
 (1422 34 (:REWRITE DEFAULT-PLUS-2))
 (960 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (720 96
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (720 96
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (657 89
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (503 9 (:REWRITE CANCEL-FLOOR-+))
 (480 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (480 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (480 96 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (480 96
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (480 96
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (480 96
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (480 96
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (480 96
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (464 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (445 89
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (392
  392
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (392 392
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (392
     392
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (392 392
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (392 392
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (313 46 (:REWRITE DEFAULT-LESS-THAN-2))
 (280 48 (:REWRITE INTEGERP-MINUS-X))
 (215 9 (:REWRITE FLOOR-ZERO . 3))
 (180 36
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (177 111 (:REWRITE DEFAULT-TIMES-2))
 (167 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (153 18 (:REWRITE |(* (- x) y)|))
 (149 149
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (149 149
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (149 149
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (149 149
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (132 4
      (:REWRITE |(integerp (* 1/2 (logior x y)))|))
 (122 122
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (122 122
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (122 122
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (114 111 (:REWRITE DEFAULT-TIMES-1))
 (108 12 (:REWRITE ACL2-NUMBERP-X))
 (103 9 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (101 9 (:REWRITE FLOOR-ZERO . 4))
 (101 6 (:REWRITE DEFAULT-LOGIOR-2))
 (101 6 (:REWRITE DEFAULT-LOGIOR-1))
 (99 9 (:REWRITE DEFAULT-FLOOR-RATIO))
 (98 9 (:REWRITE FLOOR-=-X/Y . 3))
 (98 9 (:REWRITE FLOOR-=-X/Y . 2))
 (93 39
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (90 18 (:REWRITE DEFAULT-MINUS))
 (81 18 (:REWRITE |(- (* c x))|))
 (81 9 (:REWRITE FLOOR-ZERO . 5))
 (80 33 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (73 2 (:LINEAR EXPT-X->=-X))
 (73 2 (:LINEAR EXPT-X->-X))
 (60 33 (:REWRITE SIMPLIFY-SUMS-<))
 (60 2 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (53 2 (:LINEAR EXPT-<=-1-TWO))
 (53 2 (:LINEAR EXPT-<-1-TWO))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (48 12 (:REWRITE RATIONALP-X))
 (45 9 (:REWRITE FLOOR-ZERO . 2))
 (45 9 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (45 9 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (45 9 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (45 9
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (45 9
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (44 39
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (44 39
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (39 39 (:REWRITE REDUCE-INTEGERP-+))
 (39 39
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (39 39 (:REWRITE INTEGERP-<-CONSTANT))
 (39 39 (:REWRITE CONSTANT-<-INTEGERP))
 (39 39
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (39 39
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (39 39
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (39 39
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (39 39 (:REWRITE |(< c (- x))|))
 (39 39
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (39 39
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (39 39
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (39 39
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (39 39 (:REWRITE |(< (/ x) (/ y))|))
 (39 39 (:REWRITE |(< (- x) c)|))
 (39 39 (:REWRITE |(< (- x) (- y))|))
 (39 39 (:META META-INTEGERP-CORRECT))
 (24 24 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (21 9 (:REWRITE FLOOR-CANCEL-*-CONST))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (11 11 (:REWRITE DEFAULT-EXPT-1))
 (11 11 (:REWRITE |(expt 1/c n)|))
 (11 11 (:REWRITE |(expt (- x) n)|))
 (10 10 (:TYPE-PRESCRIPTION ABS))
 (9 9
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (9 9 (:REWRITE DEFAULT-FLOOR-2))
 (9 9 (:REWRITE DEFAULT-FLOOR-1))
 (9 9 (:REWRITE |(floor x (- y))| . 2))
 (9 9 (:REWRITE |(floor x (- y))| . 1))
 (9 9
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (9 9
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(floor (- x) y)| . 2))
 (9 9 (:REWRITE |(floor (- x) y)| . 1))
 (9 9
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3
    (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (3 3
    (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(|(n32p (logior x y))|
 (68 68
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (68 68
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (68 68
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (68 68
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (60 2 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (13 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (10
   10
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (10
  10
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE DEFAULT-LOGIOR-2))
 (5 5 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (2 2 (:LINEAR LOGIOR-BOUNDS-NEG . 2)))
(LOGAND-MASK-SHIFTED-2
 (34128 48 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (19333 670 (:REWRITE THE-FLOOR-ABOVE))
 (18433 22 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (18125 22 (:REWRITE MOD-ZERO . 4))
 (17822 6 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (16091 1021 (:REWRITE DEFAULT-TIMES-2))
 (15993 15993
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (15987 15987
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15987 15987
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15987 15987
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15022 22 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (14445 22 (:REWRITE MOD-X-Y-=-X . 4))
 (12393 1074 (:REWRITE DEFAULT-PLUS-2))
 (10902 1074 (:REWRITE DEFAULT-PLUS-1))
 (10880
  10880
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10880
      10880
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10880
     10880
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10880 10880
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10880 10880
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8599 6 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (8473 661 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (8473 661
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (8473 661
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (8473 661
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (8473 661
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (6566 1021 (:REWRITE DEFAULT-TIMES-1))
 (6395 60 (:REWRITE CANCEL-FLOOR-+))
 (5301 41
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (4754 22 (:REWRITE MOD-ZERO . 3))
 (4627 661 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (4627 661 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (4627 661
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4517 626
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4262 62 (:REWRITE |(integerp (- x))|))
 (3564 60 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3377 625 (:REWRITE DEFAULT-MINUS))
 (3282 330 (:REWRITE DEFAULT-DIVIDE))
 (3195 239 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3109 53
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2992 23 (:REWRITE DEFAULT-MOD-RATIO))
 (2973 60 (:REWRITE FLOOR-ZERO . 3))
 (2482 60 (:REWRITE FLOOR-=-X/Y . 2))
 (2477 93 (:LINEAR EXPT-<=-1-TWO))
 (2400 93 (:LINEAR EXPT->-1-ONE))
 (2340 61 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2092 93 (:LINEAR EXPT-X->=-X))
 (2092 93 (:LINEAR EXPT-X->-X))
 (2006 482
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1946 670 (:REWRITE THE-FLOOR-BELOW))
 (1887 658 (:REWRITE DEFAULT-LESS-THAN-2))
 (1854 12 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1854 12 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1819 21 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1819 21
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1675 21 (:REWRITE MOD-X-Y-=-X . 2))
 (1642 658 (:REWRITE DEFAULT-LESS-THAN-1))
 (1598 482 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1583 60 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1564 17
       (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (1500 60 (:REWRITE FLOOR-ZERO . 2))
 (1500 60 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1500 60 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1447 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1095 60 (:REWRITE FLOOR-ZERO . 5))
 (1095 60 (:REWRITE FLOOR-ZERO . 4))
 (1041 22 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1041 22 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (921 12 (:LINEAR BINARY-LOGAND-<=))
 (900 60 (:REWRITE FLOOR-CANCEL-*-CONST))
 (899 323 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (899 323 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (895 20 (:REWRITE MOD-CANCEL-*-CONST))
 (864 738
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (864 738
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (844 655 (:REWRITE |(< (- x) (- y))|))
 (839 650 (:REWRITE |(< (- x) c)|))
 (780 60
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (780 60
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (780 60
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (744 24 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (738 738
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (668 650
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (667 667 (:REWRITE DEFAULT-EXPT-2))
 (667 667 (:REWRITE DEFAULT-EXPT-1))
 (667 667 (:REWRITE |(expt 1/c n)|))
 (667 667 (:REWRITE |(expt (- x) n)|))
 (658 23 (:REWRITE DEFAULT-MOD-1))
 (657 657
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (657 657
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (655 655
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (655 655
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (655 655
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (655 655
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (655 655
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (655 655
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (655 655
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (655 655
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (655 655 (:REWRITE |(< (/ x) (/ y))|))
 (650 650 (:REWRITE INTEGERP-<-CONSTANT))
 (650 650 (:REWRITE CONSTANT-<-INTEGERP))
 (650 650 (:REWRITE |(< c (- x))|))
 (645 230 (:REWRITE |(< 0 (/ x))|))
 (610 61 (:REWRITE DEFAULT-FLOOR-2))
 (599 41 (:REWRITE DEFAULT-LOGAND-2))
 (482 482
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (481 481
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (470 470
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (436 436 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (436 436
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (384 24 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (360 4
      (:REWRITE EXPT-IS-INCREASING-FOR-BASE->-1))
 (360 4
      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (360 4
      (:REWRITE |(< (expt x n) (expt x m))|))
 (314 314
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (275 41 (:REWRITE DEFAULT-LOGAND-1))
 (269 54 (:REWRITE |(equal (- x) (- y))|))
 (240 60
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (240 60
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (240 60
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (231 231 (:REWRITE |(< 0 (* x y))|))
 (224 224
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (224 224
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (207 15
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (186 186
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (186 186
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (186 186
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (180 15
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (177 177 (:REWRITE |(< y (+ (- c) x))|))
 (177 177 (:REWRITE |(< x (+ c/d y))|))
 (176 176 (:REWRITE |(< (* x y) 0)|))
 (175 175 (:REWRITE |(< (/ x) 0)|))
 (167 23 (:REWRITE DEFAULT-MOD-2))
 (162 2 (:LINEAR MOD-BOUNDS-3))
 (152 152
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (152 152
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (136 4 (:REWRITE FLOOR-POSITIVE . 3))
 (132 132 (:REWRITE INTEGERP-MINUS-X))
 (130 130 (:META META-INTEGERP-CORRECT))
 (124 4 (:REWRITE FLOOR-POSITIVE . 2))
 (124 4 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (100 4 (:REWRITE FLOOR-POSITIVE . 4))
 (100 4 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (100 4 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (100 4 (:LINEAR MOD-BOUNDS-2))
 (95 10
     (:REWRITE |(* (expt x m) (expt x n))|))
 (93 93 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (93 93 (:LINEAR EXPT-LINEAR-UPPER-<))
 (93 93 (:LINEAR EXPT-LINEAR-LOWER-<))
 (93 93 (:LINEAR EXPT->=-1-TWO))
 (93 93 (:LINEAR EXPT->-1-TWO))
 (93 93 (:LINEAR EXPT-<=-1-ONE))
 (93 93 (:LINEAR EXPT-<-1-TWO))
 (93 93 (:LINEAR EXPT-<-1-ONE))
 (88 88 (:REWRITE |(- (* c x))|))
 (69 54 (:REWRITE |(equal (/ x) c)|))
 (64 4 (:REWRITE FLOOR-=-X/Y . 4))
 (64 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (61 61 (:REWRITE DEFAULT-FLOOR-1))
 (60 60 (:REWRITE |(floor x (- y))| . 2))
 (60 60 (:REWRITE |(floor x (- y))| . 1))
 (60 60 (:REWRITE |(floor (- x) y)| . 2))
 (60 60 (:REWRITE |(floor (- x) y)| . 1))
 (60 6
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (54 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (54 54 (:REWRITE |(equal c (/ x))|))
 (54 54 (:REWRITE |(equal (/ x) (/ y))|))
 (53 53
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (53 53 (:REWRITE |(equal c (- x))|))
 (53 53 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(< (+ c/d x) y)|))
 (46 46 (:REWRITE |(< (+ (- c) x) y)|))
 (41 41
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (41 41
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (41 41
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (39 39 (:REWRITE LOGAND-CONSTANT-MASK))
 (35 4 (:REWRITE O-INFP->NEQ-0))
 (33 33 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (28 28
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (21 21 (:REWRITE |(equal (+ (- c) x) y)|))
 (19 19
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
 (8 8 (:REWRITE |(* c (* d x))|))
 (4 4 (:REWRITE FLOOR-ZERO . 1))
 (4 4 (:REWRITE FLOOR-POSITIVE . 1))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 5))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 4))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 3))
 (4 4 (:REWRITE |(mod (floor x y) z)| . 2))
 (4 4 (:REWRITE |(equal (* x y) 0)|))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(SNPT-CODE-LOCATION)
(|(natp (snpt-code-location))|)
(|irritating crock|)
(|(n32p (+ 991 (snpt-code-location)))|)
(HANDY-REFERENCE-THM-FOR-OFFSETS)
(CHECK-CODE)
(CODE-LOADED-P-1 (36 33 (:REWRITE DEFAULT-+-1))
                 (35 33 (:REWRITE DEFAULT-+-2))
                 (12 9 (:REWRITE DEFAULT-UNARY-MINUS))
                 (6 2 (:LINEAR |(n08p (r08 addr st))|))
                 (5 5 (:REWRITE DEFAULT-<-2))
                 (5 5 (:REWRITE DEFAULT-<-1))
                 (4 4
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (3 1 (:REWRITE O<=-O-FINP-DEF))
                 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
                 (1 1 (:REWRITE O-INFP-O-FINP-O<=))
                 (1 1 (:REWRITE DEFAULT-CDR))
                 (1 1 (:REWRITE AC-<)))
(CODE-LOADED-P)
(CROCK-1 (175 151 (:REWRITE DEFAULT-+-1))
         (173 151 (:REWRITE DEFAULT-+-2))
         (166 166
              (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
         (50 36 (:REWRITE DEFAULT-UNARY-MINUS))
         (44 44 (:REWRITE FOLD-CONSTS-IN-+))
         (35 24 (:REWRITE DEFAULT-<-1))
         (24 24 (:REWRITE DEFAULT-<-2))
         (18 6 (:LINEAR |(n08p (r08 addr st))|))
         (14 14 (:REWRITE DEFAULT-CDR)))
(CODE-LOADED-P-THM-08 (66 33
                          (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
                      (45 1 (:DEFINITION CODE-LOADED-P-1))
                      (18 14 (:REWRITE DEFAULT-+-2))
                      (17 14 (:REWRITE DEFAULT-+-1))
                      (7 4 (:REWRITE DEFAULT-UNARY-MINUS))
                      (3 3 (:REWRITE DEFAULT-CDR))
                      (3 3 (:REWRITE DEFAULT-<-2))
                      (3 3 (:REWRITE DEFAULT-<-1))
                      (3 1 (:REWRITE <-+-NEGATIVE-0-1)))
(CODE-LOADED-P-THM-32
     (84 41 (:REWRITE DEFAULT-+-2))
     (60 41 (:REWRITE DEFAULT-+-1))
     (51 13 (:REWRITE |(n32p x)|))
     (21 21 (:REWRITE FOLD-CONSTS-IN-+))
     (19 4
         (:REWRITE |(good-32-address-p addr st)|))
     (12 12 (:REWRITE DEFAULT-<-2))
     (12 12 (:REWRITE DEFAULT-<-1))
     (12 6
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (10 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
     (6 6
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(CROCK-1 (474 419 (:REWRITE DEFAULT-+-2))
         (462 419 (:REWRITE DEFAULT-+-1))
         (234 234
              (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
         (85 66 (:REWRITE DEFAULT-UNARY-MINUS))
         (74 74
             (:TYPE-PRESCRIPTION |(natp (snpt-code-location))|))
         (57 39 (:REWRITE DEFAULT-<-1))
         (39 39 (:REWRITE DEFAULT-<-2))
         (32 8
             (:REWRITE |(memoryp (g :mem (w08 addr val st)))|))
         (31 2
             (:REWRITE |(r08 addr1 (w08 addr2 val st)) --- paging|))
         (29 29 (:REWRITE CODE-LOADED-P-THM-08))
         (19 19 (:REWRITE DEFAULT-CDR))
         (16 16 (:TYPE-PRESCRIPTION N08P))
         (12 12
             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
         (8 8 (:REWRITE |(n08p x)|))
         (8 8
            (:REWRITE |(g field (w08 addr val st))|))
         (8 2 (:REWRITE DISJOINT-3-ITEMS))
         (4 4 (:REWRITE |(va-to-pa addr st)|)))
(CROCK-2
 (474 419 (:REWRITE DEFAULT-+-2))
 (462 419 (:REWRITE DEFAULT-+-1))
 (234 234
      (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (85 66 (:REWRITE DEFAULT-UNARY-MINUS))
 (74 74
     (:TYPE-PRESCRIPTION |(natp (snpt-code-location))|))
 (57 39 (:REWRITE DEFAULT-<-1))
 (39 39 (:REWRITE DEFAULT-<-2))
 (32 8
     (:REWRITE |(memoryp (g :mem (w32 addr val st)))|))
 (29 29 (:REWRITE CODE-LOADED-P-THM-08))
 (28 7
     (:REWRITE |(good-32-address-p addr st)|))
 (27 2
     (:REWRITE |(r08 addr1 (w32 addr2 val st)) --- paging|))
 (19 19 (:REWRITE DEFAULT-CDR))
 (12 12
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12
  12
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (9
  9
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (9
  9
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (8 8
    (:REWRITE |(g field (w32 addr val st))|))
 (8 2 (:REWRITE DISJOINT-3-ITEMS))
 (4 4 (:REWRITE |(va-to-pa addr st)|)))
(|(code-loaded-p lower upper (w08 addr s))|
 (60 47 (:REWRITE DEFAULT-+-2))
 (51 47 (:REWRITE DEFAULT-+-1))
 (47 2
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (41
  1
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (33 4 (:REWRITE COMMUTATIVITY-2-OF-+))
 (18 12 (:REWRITE FOLD-CONSTS-IN-+))
 (14 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 12
     (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (9 9
    (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE CODE-LOADED-P-THM-08))
 (3 3 (:REWRITE |(n32p x)|))
 (2 1
    (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
 (2 1 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1 (:REWRITE |(subrangep x x)|))
 (1 1
    (:REWRITE |(subrangep (list x) (range base offset length))|)))
(|(code-loaded-p lower upper (w32 addr s))|
 (60 47 (:REWRITE DEFAULT-+-2))
 (51 47 (:REWRITE DEFAULT-+-1))
 (47 2
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (42
  2
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (33 4 (:REWRITE COMMUTATIVITY-2-OF-+))
 (18 12 (:REWRITE FOLD-CONSTS-IN-+))
 (14 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 12
     (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (9 9
    (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE CODE-LOADED-P-THM-08))
 (4 1
    (:REWRITE |(good-32-address-p addr st)|))
 (3 3 (:REWRITE |(n32p x)|))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2 1
    (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
 (2 1 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1 (:REWRITE |(subrangep x x)|)))
(SEC_NOT_PRESENT-LOADED-P)
(SEC_NOT_PRESENT-LOADED-THM-08
     (54 27
         (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
     (14 8 (:REWRITE DEFAULT-+-2))
     (10 8 (:REWRITE DEFAULT-+-1))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 2 (:REWRITE DEFAULT-<-2))
     (3 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-CDR)))
(SEC_NOT_PRESENT-LOADED-THM-32 (226 108 (:REWRITE DEFAULT-+-2))
                               (162 108 (:REWRITE DEFAULT-+-1))
                               (28 28 (:REWRITE DEFAULT-CDR))
                               (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
                               (12 12
                                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                               (7 5 (:REWRITE DEFAULT-<-2))
                               (7 5 (:REWRITE DEFAULT-<-1)))
(INIT_PDTS-LOADED-P)
(INIT_PDTS-LOADED-THM-08 (54 27
                             (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
                         (20 11 (:REWRITE DEFAULT-+-2))
                         (13 11 (:REWRITE DEFAULT-+-1))
                         (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
                         (3 2 (:REWRITE DEFAULT-<-2))
                         (3 2 (:REWRITE DEFAULT-<-1))
                         (2 2 (:REWRITE DEFAULT-CDR))
                         (1 1
                            (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08)))
(INIT_PDTS-LOADED-THM-32 (364 173 (:REWRITE DEFAULT-+-2))
                         (259 173 (:REWRITE DEFAULT-+-1))
                         (44 44 (:REWRITE DEFAULT-CDR))
                         (28 14 (:REWRITE DEFAULT-UNARY-MINUS))
                         (20 20
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                         (10 10
                             (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
                         (7 5 (:REWRITE DEFAULT-<-2))
                         (7 5 (:REWRITE DEFAULT-<-1)))
(INIT_PDPT-LOADED-P)
(INIT_PDPT-LOADED-THM-08 (54 27
                             (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
                         (20 11 (:REWRITE DEFAULT-+-2))
                         (13 11 (:REWRITE DEFAULT-+-1))
                         (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
                         (3 2 (:REWRITE DEFAULT-<-2))
                         (3 2 (:REWRITE DEFAULT-<-1))
                         (2 2 (:REWRITE DEFAULT-CDR))
                         (1 1
                            (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
                         (1 1 (:REWRITE INIT_PDTS-LOADED-THM-08)))
(INIT_PDPT-LOADED-THM-32 (364 173 (:REWRITE DEFAULT-+-2))
                         (259 173 (:REWRITE DEFAULT-+-1))
                         (44 44 (:REWRITE DEFAULT-CDR))
                         (28 14 (:REWRITE DEFAULT-UNARY-MINUS))
                         (20 20
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                         (10 10
                             (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
                         (10 10 (:REWRITE INIT_PDTS-LOADED-THM-32))
                         (7 5 (:REWRITE DEFAULT-<-2))
                         (7 5 (:REWRITE DEFAULT-<-1)))
(CREATE_NESTED_PT-LOADED-P)
(CREATE_NESTED_PT-LOADED-THM-08
     (54 27
         (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
     (16 9 (:REWRITE DEFAULT-+-2))
     (11 9 (:REWRITE DEFAULT-+-1))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 2 (:REWRITE DEFAULT-<-2))
     (3 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE DEFAULT-CDR))
     (1 1
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
     (1 1 (:REWRITE INIT_PDTS-LOADED-THM-08))
     (1 1 (:REWRITE INIT_PDPT-LOADED-THM-08)))
(CREATE_NESTED_PT-LOADED-THM-32
     (201 95 (:REWRITE DEFAULT-+-2))
     (142 95 (:REWRITE DEFAULT-+-1))
     (54 54 (:REWRITE FOLD-CONSTS-IN-+))
     (24 24 (:REWRITE DEFAULT-CDR))
     (12 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (10 10
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (5 5
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (5 5 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (5 5 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (3 2 (:REWRITE DEFAULT-<-2))
     (3 2 (:REWRITE DEFAULT-<-1)))
(ALL-CODE-LOADED-P)
(ALL-CODE-LOADED-P-FC)
(GOOD-STATE-P)
(GOOD-STATE-P-FC (42 21 (:REWRITE DEFAULT-+-2))
                 (21 21 (:REWRITE DEFAULT-+-1)))
(CROCK-1-1 (159 137 (:REWRITE DEFAULT-+-1))
           (148 137 (:REWRITE DEFAULT-+-2))
           (50 50 (:REWRITE FOLD-CONSTS-IN-+))
           (50 39 (:REWRITE DEFAULT-UNARY-MINUS))
           (44 44
               (:TYPE-PRESCRIPTION |(natp (snpt-code-location))|))
           (17 17
               (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
           (17 17 (:REWRITE INIT_PDTS-LOADED-THM-08))
           (17 17 (:REWRITE INIT_PDPT-LOADED-THM-08))
           (17 17
               (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
           (17 17 (:REWRITE CODE-LOADED-P-THM-08))
           (16 4 (:LINEAR |(n08p (r08 addr st))|))
           (14 14 (:REWRITE DEFAULT-<-2))
           (14 14 (:REWRITE DEFAULT-<-1))
           (11 11 (:REWRITE DEFAULT-CDR))
           (4 4 (:REWRITE G-DIFF-S)))
(CROCK-1 (45 1 (:DEFINITION CODE-LOADED-P-1))
         (14 3 (:REWRITE COMMUTATIVITY-OF-+))
         (10 8 (:REWRITE DEFAULT-+-2))
         (9 8 (:REWRITE DEFAULT-+-1))
         (7 3 (:REWRITE UNICITY-OF-0))
         (5 5
            (:TYPE-PRESCRIPTION |(natp (snpt-code-location))|))
         (4 3 (:DEFINITION FIX))
         (4 2
            (:TYPE-PRESCRIPTION |(n08p (r08 addr st))|))
         (3 2 (:REWRITE DEFAULT-UNARY-MINUS))
         (2 2 (:TYPE-PRESCRIPTION MEMORYP))
         (1 1
            (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
         (1 1 (:REWRITE INIT_PDTS-LOADED-THM-08))
         (1 1 (:REWRITE INIT_PDPT-LOADED-THM-08))
         (1 1 (:REWRITE DEFAULT-CDR))
         (1 1 (:REWRITE DEFAULT-<-2))
         (1 1 (:REWRITE DEFAULT-<-1))
         (1 1
            (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
         (1 1 (:REWRITE CODE-LOADED-P-THM-08)))
(CROCK-3 (4 4 (:REWRITE G-DIFF-S)))
(|(good-state-p (s field val) s) --- n32p|
     (394 197 (:REWRITE DEFAULT-+-2))
     (197 197 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE |(memberp e (list x))|)))
(|(good-state-p (s field val) s) --- n01p|
     (605 5
          (:REWRITE |(good-state-p (s field val) s) --- n32p|))
     (240 120 (:REWRITE DEFAULT-+-2))
     (120 120 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE |(memberp e (list x))|)))
(|(good-state-p (w32 addr val s))|
 (214 123 (:REWRITE DEFAULT-+-2))
 (179 123 (:REWRITE DEFAULT-+-1))
 (16 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4 1
    (:REWRITE |(good-32-address-p addr st)|)))
(IN-INIT_PDPT)
(IN-SUB)
(INIT_PDPT-CUTPOINT-P)
(INIT_PDPT-PRE)
(INIT_PDPT-LOOP-PRE)
(INIT_PDPT-MODIFY-LOOP-1)
(|(paging-p (init_pdpt-modify-loop-1 loop-counter s))|
     (4046 14 (:DEFINITION BINARY-LOGAND))
     (3402 14 (:DEFINITION FLOOR))
     (2296 28
           (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (911 323 (:REWRITE DEFAULT-+-2))
     (610 323 (:REWRITE DEFAULT-+-1))
     (588 28 (:DEFINITION NFIX))
     (364 84 (:REWRITE DEFAULT-UNARY-MINUS))
     (325 73 (:REWRITE DEFAULT-<-1))
     (283 23 (:REWRITE DISTRIBUTIVITY))
     (280 14 (:REWRITE ZIP-OPEN))
     (280 14 (:REWRITE COMMUTATIVITY-OF-*))
     (241 73 (:REWRITE DEFAULT-<-2))
     (187 89 (:REWRITE DEFAULT-*-2))
     (108 108
          (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
     (108 9 (:REWRITE ASSOCIATIVITY-OF-+))
     (98 14 (:REWRITE O-INFP->NEQ-0))
     (98 14 (:REWRITE DEFAULT-NUMERATOR))
     (98 14 (:REWRITE DEFAULT-DENOMINATOR))
     (96 24
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- not paging|))
     (89 89 (:REWRITE DEFAULT-*-1))
     (84 54
         (:REWRITE |(good-32-address-p addr st)|))
     (78 24
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
     (70 70
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (56 56
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (56 56 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (56 56 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (56 56
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (48 9
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
     (44 23 (:REWRITE FOLD-CONSTS-IN-+))
     (42 14 (:REWRITE UNICITY-OF-0))
     (36 36
         (:REWRITE |(g field (w32 addr val st))|))
     (36 9
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
     (28 14 (:DEFINITION FIX))
     (17 8 (:REWRITE ZP-OPEN))
     (14 14
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(|(va-to-pa addr (init_pdpt-modify-loop-1 loop-counter s))|
     (750 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
     (668 2 (:DEFINITION BINARY-LOGIOR))
     (578 2 (:DEFINITION BINARY-LOGAND))
     (486 2 (:DEFINITION FLOOR))
     (410 165
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (328 4
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (165 165 (:TYPE-PRESCRIPTION R32))
     (165 165 (:TYPE-PRESCRIPTION MEMORYP))
     (117 42 (:REWRITE DEFAULT-+-2))
     (88 4 (:DEFINITION LOGNOT))
     (84 42 (:REWRITE DEFAULT-+-1))
     (84 12 (:REWRITE COMMUTATIVITY-OF-+))
     (84 4 (:DEFINITION NFIX))
     (52 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (46 10 (:REWRITE DEFAULT-<-1))
     (40 2 (:REWRITE ZIP-OPEN))
     (40 2 (:REWRITE COMMUTATIVITY-OF-*))
     (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
     (34 10 (:REWRITE DEFAULT-<-2))
     (34 2 (:REWRITE DISTRIBUTIVITY))
     (25 11 (:REWRITE DEFAULT-*-2))
     (22 8 (:DEFINITION IFIX))
     (16 16 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (14 2 (:REWRITE O-INFP->NEQ-0))
     (14 2 (:REWRITE DEFAULT-NUMERATOR))
     (14 2 (:REWRITE DEFAULT-DENOMINATOR))
     (11 11 (:REWRITE DEFAULT-*-1))
     (10 10
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (8 8
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (8 8
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 2 (:DEFINITION FIX))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(|(good-32-address-p addr (init_pdpt-modify-loop-1 loop-counter s))|
     (750 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
     (668 2 (:DEFINITION BINARY-LOGIOR))
     (578 2 (:DEFINITION BINARY-LOGAND))
     (486 2 (:DEFINITION FLOOR))
     (410 165
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (328 4
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (165 165 (:TYPE-PRESCRIPTION R32))
     (165 165 (:TYPE-PRESCRIPTION MEMORYP))
     (119 44 (:REWRITE DEFAULT-+-2))
     (88 4 (:DEFINITION LOGNOT))
     (86 44 (:REWRITE DEFAULT-+-1))
     (84 12 (:REWRITE COMMUTATIVITY-OF-+))
     (84 4 (:DEFINITION NFIX))
     (52 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (50 14 (:REWRITE DEFAULT-<-1))
     (40 2 (:REWRITE ZIP-OPEN))
     (40 2 (:REWRITE COMMUTATIVITY-OF-*))
     (38 14 (:REWRITE DEFAULT-<-2))
     (34 2 (:REWRITE DISTRIBUTIVITY))
     (25 11 (:REWRITE DEFAULT-*-2))
     (23 7 (:REWRITE |(n32p x)|))
     (22 8 (:DEFINITION IFIX))
     (16 16 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (14 2 (:REWRITE O-INFP->NEQ-0))
     (14 2 (:REWRITE DEFAULT-NUMERATOR))
     (14 2 (:REWRITE DEFAULT-DENOMINATOR))
     (11 11 (:REWRITE DEFAULT-*-1))
     (10 10
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (8 8
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (8 8
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (8 2
        (:REWRITE |(good-32-address-p addr st)|))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 4
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (4 4
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (4 2 (:DEFINITION FIX))
     (2 2 (:TYPE-PRESCRIPTION N32P))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 1
        (:REWRITE |(paging-p (init_pdpt-modify-loop-1 loop-counter s))|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(|(memoryp (g :mem (init_pdpt-modify-loop-1 loop-counter s)))|
 (706 508 (:REWRITE DEFAULT-PLUS-2))
 (706 35
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (582 508 (:REWRITE DEFAULT-PLUS-1))
 (269 269
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (269 269 (:REWRITE NORMALIZE-ADDENDS))
 (105 105
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (105 105 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (105 105 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (105 105
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (54 54 (:REWRITE FOLD-CONSTS-IN-+))
 (51 35 (:REWRITE DEFAULT-LESS-THAN-1))
 (47 47 (:REWRITE DEFAULT-TIMES-2))
 (47 47 (:REWRITE DEFAULT-TIMES-1))
 (45 45
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (45 15 (:REWRITE DEFAULT-LOGIOR-2))
 (40
   40
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (35 35 (:REWRITE THE-FLOOR-BELOW))
 (35 35 (:REWRITE THE-FLOOR-ABOVE))
 (35 35
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (35 35 (:REWRITE DEFAULT-LESS-THAN-2))
 (26 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (26 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
 (20 20 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (15 15 (:REWRITE DEFAULT-LOGIOR-1))
 (13
  13
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (13
  13
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (9 9 (:REWRITE ZP-OPEN))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT)))
(|(good-state-p (init_pdpt-modify-loop-1 loop-counter s))|
 (965 674 (:REWRITE DEFAULT-PLUS-2))
 (826 674 (:REWRITE DEFAULT-PLUS-1))
 (782 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (334 316 (:REWRITE NORMALIZE-ADDENDS))
 (314 314
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (107 18 (:REWRITE SIMPLIFY-SUMS-<))
 (100 100
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (100 100 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (100 100 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (100 100
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (70 70 (:REWRITE FOLD-CONSTS-IN-+))
 (49 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (45 15 (:REWRITE DEFAULT-LOGIOR-2))
 (44 44 (:REWRITE DEFAULT-TIMES-2))
 (44 44 (:REWRITE DEFAULT-TIMES-1))
 (42 42
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (40
   40
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (40
  40
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (40 40
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (35 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (27 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (27 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19 19
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (19 19 (:REWRITE INTEGERP-<-CONSTANT))
 (19 19 (:REWRITE CONSTANT-<-INTEGERP))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< c (- x))|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (19 19
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (19 19 (:REWRITE |(< (/ x) (/ y))|))
 (19 19 (:REWRITE |(< (- x) c)|))
 (19 19 (:REWRITE |(< (- x) (- y))|))
 (19 19 (:REWRITE |(< (+ c/d x) y)|))
 (17
  17
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (17
  17
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (15 15 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8 (:REWRITE ZP-OPEN))
 (6 3 (:DEFINITION FIX))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (4 4
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 2 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|)))
(|(r32 addr (init_pdpt-modify-loop-1 loop-counter s))|
 (6495 4731 (:REWRITE DEFAULT-PLUS-2))
 (5823 4731 (:REWRITE DEFAULT-PLUS-1))
 (2007 2007
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2007 2007 (:REWRITE NORMALIZE-ADDENDS))
 (1333 64
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (495 495 (:REWRITE FOLD-CONSTS-IN-+))
 (415 415
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (415 415 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (415 415 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (415 415
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (385
   385
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (385
  385
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (385 385
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (385
     385
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (385 385
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (385 385
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (264 264 (:REWRITE DEFAULT-TIMES-2))
 (264 264 (:REWRITE DEFAULT-TIMES-1))
 (173 173
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (128
  128
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (128
  128
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (90 64 (:REWRITE DEFAULT-LESS-THAN-1))
 (64 64 (:REWRITE THE-FLOOR-BELOW))
 (64 64 (:REWRITE THE-FLOOR-ABOVE))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 64 (:REWRITE DEFAULT-LESS-THAN-2))
 (54 18 (:REWRITE DEFAULT-LOGIOR-2))
 (45 32
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (45 32 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (39 39 (:REWRITE |(< (+ c/d x) y)|))
 (35 35
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (35 35 (:REWRITE INTEGERP-<-CONSTANT))
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
 (35 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (34 34
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (34 34
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (32 32 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18 (:REWRITE DEFAULT-LOGIOR-1))
 (11 11 (:REWRITE ZP-OPEN))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:META META-INTEGERP-CORRECT))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (9 1
    (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)))
(|(init_pdpt-modify-loop-1 loop-counter (w32 addr val s))|
 (12291 9070 (:REWRITE DEFAULT-PLUS-2))
 (11019 9070 (:REWRITE DEFAULT-PLUS-1))
 (4842
  216
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (4587 116
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4364 3644 (:REWRITE NORMALIZE-ADDENDS))
 (3584 3584
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2334 69 (:REWRITE SIMPLIFY-SUMS-<))
 (1470
  216
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1290 6
       (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (862 862 (:REWRITE FOLD-CONSTS-IN-+))
 (702 6 (:REWRITE DISJOINT-3-ITEMS))
 (650
   650
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (650
  650
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (650 650
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (650
     650
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (650 650
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (650 650
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (373 373
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (373 373 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (373 373 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (373 373
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (300 30 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (189 116 (:REWRITE DEFAULT-LESS-THAN-1))
 (161 116 (:REWRITE DEFAULT-LESS-THAN-2))
 (150 150 (:REWRITE DEFAULT-TIMES-2))
 (150 150 (:REWRITE DEFAULT-TIMES-1))
 (143 69
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (143 69 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (135 90 (:DEFINITION FIX))
 (123 37 (:REWRITE DEFAULT-LOGIOR-2))
 (120 120
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (120 30 (:REWRITE |(+ (* c x) (* d x))|))
 (118 19 (:REWRITE ZP-OPEN))
 (116 116 (:REWRITE THE-FLOOR-BELOW))
 (116 116 (:REWRITE THE-FLOOR-ABOVE))
 (116 116
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (116 116
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (90 60 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (74 74
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (74 74
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
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
 (73 73 (:REWRITE |(< (+ c/d x) y)|))
 (66 18 (:REWRITE ACL2-NUMBERP-X))
 (60 30 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (60 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (37 37 (:REWRITE DEFAULT-LOGIOR-1))
 (33 33 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (30 30 (:REWRITE |(+ x (- x))|))
 (30 30 (:REWRITE |(* 0 x)|))
 (24 6 (:REWRITE RATIONALP-X))
 (18 18 (:REWRITE |(< y (+ (- c) x))|))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (12 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (12 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (3 3 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON)))
(|(r32 addr (init_pdpt-modify-loop-1 loop-counter s)) --- written to 1|
 (22085 15095 (:REWRITE DEFAULT-PLUS-2))
 (20073 15071 (:REWRITE DEFAULT-PLUS-1))
 (18337
  289
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (10396 610
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6474 754
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5503 5503
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3376 35 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (2758 1
       (:REWRITE |(init_pdpt-modify-loop-1 loop-counter (w32 addr val s))|))
 (2537 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (2248 480 (:REWRITE INTEGERP-<-CONSTANT))
 (1424 1424 (:REWRITE FOLD-CONSTS-IN-+))
 (1338 37
       (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (1260 972 (:REWRITE DEFAULT-TIMES-2))
 (1021 1021
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1021 1021
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1017 754 (:REWRITE DEFAULT-LESS-THAN-2))
 (972 972 (:REWRITE DEFAULT-TIMES-1))
 (965 754 (:REWRITE DEFAULT-LESS-THAN-1))
 (940 72 (:REWRITE |(* y (* x z))|))
 (855
   855
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (855
  855
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (855 855
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (855
     855
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (855 855
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (855 855
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (826 826
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (826 826 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (826 826 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (826 826
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (818 407
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (754 754 (:REWRITE THE-FLOOR-BELOW))
 (754 754 (:REWRITE THE-FLOOR-ABOVE))
 (746 6 (:REWRITE DISJOINT-3-ITEMS))
 (660 342 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (624 24
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (614 610
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (588 484 (:REWRITE CONSTANT-<-INTEGERP))
 (532 532
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (484 484
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (484 484
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (484 484
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (484 484
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (484 484 (:REWRITE |(< c (- x))|))
 (484 484
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (484 484
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (484 484
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (484 484
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (484 484 (:REWRITE |(< (/ x) (/ y))|))
 (484 484 (:REWRITE |(< (- x) c)|))
 (484 484 (:REWRITE |(< (- x) (- y))|))
 (432 48 (:REWRITE ACL2-NUMBERP-X))
 (412 412
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (372 372 (:REWRITE |(< (+ c/d x) y)|))
 (372 76 (:REWRITE |(* c (* d x))|))
 (340 340 (:REWRITE |(* (- x) y)|))
 (340 112 (:REWRITE DEFAULT-LOGIOR-2))
 (220 22 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (192 48 (:REWRITE RATIONALP-X))
 (152 152 (:TYPE-PRESCRIPTION ABS))
 (124 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (112 112 (:REWRITE DEFAULT-LOGIOR-1))
 (110 110 (:REWRITE |(< x (+ c/d y))|))
 (109 35 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (103 103 (:REWRITE |(< y (+ (- c) x))|))
 (96 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (96 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (96 8
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (88 22 (:REWRITE |(+ (* c x) (* d x))|))
 (84 84 (:REWRITE |(< (* x y) 0)|))
 (83 83 (:REWRITE REDUCE-INTEGERP-+))
 (83 83 (:REWRITE INTEGERP-MINUS-X))
 (83 83 (:META META-INTEGERP-CORRECT))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (72 72 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (69 69
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (68 68 (:REWRITE |(* a (/ a) b)|))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:META META-RATIONALP-CORRECT))
 (48 15 (:REWRITE ZP-OPEN))
 (37 37 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< 0 (/ x))|))
 (22 22 (:REWRITE |(* 0 x)|))
 (16 16 (:REWRITE |(< (/ x) 0)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(* 1 x)|))
 (4 1
    (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|)))
(|(r32 addr (init_pdpt-modify-loop-1 loop-counter s)) --- written to 2|
 (21912 569
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (18928
  222
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (18674 12593 (:REWRITE DEFAULT-PLUS-2))
 (16814 12593 (:REWRITE DEFAULT-PLUS-1))
 (6322 695
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4559 4559
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2537 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (1923 389 (:REWRITE INTEGERP-<-CONSTANT))
 (1711 118 (:REWRITE |(* y (* x z))|))
 (1638 9
       (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (1411 1411 (:REWRITE FOLD-CONSTS-IN-+))
 (1376 904 (:REWRITE DEFAULT-TIMES-2))
 (1290 1
       (:REWRITE |(init_pdpt-modify-loop-1 loop-counter (w32 addr val s))|))
 (1028 7 (:REWRITE DISJOINT-3-ITEMS))
 (931 695 (:REWRITE DEFAULT-LESS-THAN-2))
 (908 695 (:REWRITE DEFAULT-LESS-THAN-1))
 (904 904 (:REWRITE DEFAULT-TIMES-1))
 (695 695 (:REWRITE THE-FLOOR-BELOW))
 (695 695 (:REWRITE THE-FLOOR-ABOVE))
 (650 326
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (610
   610
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (610
  610
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (610 610
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (610
     610
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (610 610
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (610 610
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (600 312 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (573 569
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (542 542
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (542 542 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (542 542 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (542 542
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (497 393 (:REWRITE CONSTANT-<-INTEGERP))
 (464 464
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (393 393
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (393 393
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (393 393
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (393 393
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (393 393 (:REWRITE |(< c (- x))|))
 (393 393
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (393 393
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (393 393
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (393 393
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (393 393 (:REWRITE |(< (/ x) (/ y))|))
 (393 393 (:REWRITE |(< (- x) c)|))
 (393 393 (:REWRITE |(< (- x) (- y))|))
 (387 387 (:REWRITE |(< (+ c/d x) y)|))
 (354 354 (:REWRITE |(* (- x) y)|))
 (330 330
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (327 67 (:REWRITE |(* c (* d x))|))
 (220 22 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (157 157 (:REWRITE |(< x (+ c/d y))|))
 (134 134 (:TYPE-PRESCRIPTION ABS))
 (124 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (88 22 (:REWRITE |(+ (* c x) (* d x))|))
 (79 25 (:REWRITE DEFAULT-LOGIOR-2))
 (76 76 (:REWRITE |(< y (+ (- c) x))|))
 (72 72 (:REWRITE |(< (* x y) 0)|))
 (60 60
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (59 59 (:REWRITE |(* a (/ a) b)|))
 (46 13 (:REWRITE ZP-OPEN))
 (42 42
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (42 42
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (35 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 7
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (35 7 (:REWRITE O-INFP->NEQ-0))
 (25 25 (:REWRITE DEFAULT-LOGIOR-1))
 (22 22 (:REWRITE |(* 0 x)|))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (7 7
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(* 1 x)|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1 (:REWRITE |(< 0 (/ x))|)))
(INIT_PDPT-MODIFY-LOOP)
(INIT_PDPT-MODIFY)
(|(paging-p (init_pdpt-modify s))|
 (188 36 (:REWRITE ACL2-NUMBERP-X))
 (163 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (131 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (76 19 (:REWRITE RATIONALP-X))
 (36 36 (:REWRITE DEFAULT-PLUS-1))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE NORMALIZE-ADDENDS))
 (24 5 (:REWRITE |(+ c (+ d x))|))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:META META-RATIONALP-CORRECT))
 (16 4 (:REWRITE DEFAULT-TIMES-2))
 (16 4 (:REWRITE DEFAULT-TIMES-1))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 2 (:REWRITE DEFAULT-LOGIOR-2))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 9
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (9 9 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (9 9
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (7 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(+ 0 x)|))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(va-to-pa addr (init_pdpt-modify s))|
 (188 36 (:REWRITE ACL2-NUMBERP-X))
 (163 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (131 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (76 19 (:REWRITE RATIONALP-X))
 (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
 (36 36 (:REWRITE DEFAULT-PLUS-1))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (27 27 (:REWRITE NORMALIZE-ADDENDS))
 (24 5 (:REWRITE |(+ c (+ d x))|))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:META META-RATIONALP-CORRECT))
 (16 4 (:REWRITE DEFAULT-TIMES-2))
 (16 4 (:REWRITE DEFAULT-TIMES-1))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 2 (:REWRITE DEFAULT-LOGIOR-2))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 9
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (9 9 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (9 9 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (9 9
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (7 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(+ 0 x)|))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(good-32-address-p addr (init_pdpt-modify s))|
 (211 15
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (188 36 (:REWRITE ACL2-NUMBERP-X))
 (188 7 (:REWRITE |(n32p x)|))
 (163 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (76 19 (:REWRITE RATIONALP-X))
 (46 46 (:REWRITE DEFAULT-PLUS-1))
 (32 7 (:REWRITE |(+ c (+ d x))|))
 (31 31
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (31 31 (:REWRITE NORMALIZE-ADDENDS))
 (31 2
     (:REWRITE |(good-32-address-p addr st)|))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:REWRITE INTEGERP-MINUS-X))
 (22 22 (:META META-INTEGERP-CORRECT))
 (22 2 (:REWRITE |(+ y (+ x z))|))
 (21 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 19 (:META META-RATIONALP-CORRECT))
 (16 4 (:REWRITE DEFAULT-TIMES-2))
 (16 4 (:REWRITE DEFAULT-TIMES-1))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 2 (:REWRITE DEFAULT-LOGIOR-2))
 (11 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
 (9 9 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (9 9 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (9 9
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
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
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(+ 0 x)|))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:TYPE-PRESCRIPTION N32P))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(G field (INIT_PDPT-MODIFY-loop-1 i s))|
     (301 53 (:REWRITE ACL2-NUMBERP-X))
     (124 31 (:REWRITE RATIONALP-X))
     (70 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (57 21 (:REWRITE DEFAULT-TIMES-2))
     (57 21 (:REWRITE DEFAULT-TIMES-1))
     (42 6 (:REWRITE DEFAULT-LOGIOR-2))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 41 (:REWRITE NORMALIZE-ADDENDS))
     (41 41 (:REWRITE DEFAULT-PLUS-1))
     (37 37 (:REWRITE REDUCE-INTEGERP-+))
     (37 37 (:REWRITE INTEGERP-MINUS-X))
     (37 37 (:META META-INTEGERP-CORRECT))
     (31 31 (:REWRITE REDUCE-RATIONALP-+))
     (31 31 (:REWRITE REDUCE-RATIONALP-*))
     (31 31 (:REWRITE RATIONALP-MINUS-X))
     (31 31 (:META META-RATIONALP-CORRECT))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (15 15
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (14 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (10 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE DEFAULT-LOGIOR-1))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(+ c (+ d x))|)))
(|(y86-p (init_pdpt-modify s))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (105 69 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (69 69 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (46 46 (:REWRITE NORMALIZE-ADDENDS))
 (39 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (25 25
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (25 25
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (22 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12 12 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4
  4
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(memoryp (g :mem (init_pdpt-modify s)))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (105 69 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (69 69 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (46 46 (:REWRITE NORMALIZE-ADDENDS))
 (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (25 25
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (25 25
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (21 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 6
    (:REWRITE |(g field (w32 addr val st))|))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4
  4
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2
  2
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1
    (:REWRITE |(G field (INIT_PDPT-MODIFY-loop-1 i s))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(good-state-p (init_pdpt-modify s))|
 (18740 18424 (:REWRITE DEFAULT-PLUS-2))
 (18424 18424 (:REWRITE DEFAULT-PLUS-1))
 (7481 7481
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7481 7481 (:REWRITE NORMALIZE-ADDENDS))
 (3841 212
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1301 27 (:REWRITE |(n32-to-i32 x) --- 2|))
 (1275 27 (:REWRITE |(n32-to-i32 x) --- 1|))
 (1256
   1256
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1256
  1256
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1256
      1256
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1256
     1256
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1256 1256
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1256 1256
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (837
  837
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (837
  837
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (684 9 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (444 444
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (444 444
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (444 444
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (324 324
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (324 324 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (324 324 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (324 324
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (298 212 (:REWRITE DEFAULT-LESS-THAN-1))
 (221 212 (:REWRITE DEFAULT-LESS-THAN-2))
 (212 212 (:REWRITE THE-FLOOR-BELOW))
 (212 212 (:REWRITE THE-FLOOR-ABOVE))
 (212 212
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (212 212
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (174 115
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (174 115
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (146 115
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (133 115 (:REWRITE SIMPLIFY-SUMS-<))
 (115 115 (:REWRITE INTEGERP-<-CONSTANT))
 (115 115 (:REWRITE CONSTANT-<-INTEGERP))
 (115 115
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (115 115
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (115 115
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (115 115
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (115 115 (:REWRITE |(< c (- x))|))
 (115 115
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (115 115
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (115 115
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (115 115
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (115 115 (:REWRITE |(< (/ x) (/ y))|))
 (115 115 (:REWRITE |(< (- x) c)|))
 (115 115 (:REWRITE |(< (- x) (- y))|))
 (106 106 (:REWRITE |(< (+ c/d x) y)|))
 (99 9 (:REWRITE DISJOINT-4-ITEMS))
 (64 28 (:REWRITE DEFAULT-TIMES-2))
 (57 53 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (48 28 (:REWRITE DEFAULT-TIMES-1))
 (46 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (46 27
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (46 27
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (30 10 (:REWRITE DEFAULT-LOGIOR-2))
 (27 27
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (27 27 (:REWRITE |(equal c (/ x))|))
 (27 27 (:REWRITE |(equal c (- x))|))
 (27 27 (:REWRITE |(equal (/ x) c)|))
 (27 27 (:REWRITE |(equal (/ x) (/ y))|))
 (27 27 (:REWRITE |(equal (- x) c)|))
 (27 27 (:REWRITE |(equal (- x) (- y))|))
 (19 19 (:REWRITE |(equal (+ (- c) x) y)|))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:REWRITE DEFAULT-LOGIOR-1))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE O-INFP->NEQ-0)))
(|(g :cr0 (init_pdpt-modify s))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (338 5 (:REWRITE |(n32p x)|))
 (104 68 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (68 68 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 45 (:REWRITE NORMALIZE-ADDENDS))
 (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (24 24
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (24 24
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (21 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (6 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(subrangep x x)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1
  1
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :eip (init_pdpt-modify s))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (338 5 (:REWRITE |(n32p x)|))
 (104 68 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (68 68 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 45 (:REWRITE NORMALIZE-ADDENDS))
 (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (25 25
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (25 25 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (25 25
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (21 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (6 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(subrangep x x)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1
  1
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :ebp (init_pdpt-modify s))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (338 5 (:REWRITE |(n32p x)|))
 (104 68 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (68 68 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (45 45
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 45 (:REWRITE NORMALIZE-ADDENDS))
 (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (24 24
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (24 24
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (21 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (6 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(subrangep x x)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1
  1
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :esp (init_pdpt-modify s))|
 (369 20
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (338 5 (:REWRITE |(n32p x)|))
 (105 69 (:REWRITE DEFAULT-PLUS-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (69 69 (:REWRITE DEFAULT-PLUS-1))
 (60 4 (:REWRITE |(+ y (+ x z))|))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (46 46 (:REWRITE NORMALIZE-ADDENDS))
 (30 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (24 24
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (24 24
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (21 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (20 20 (:REWRITE THE-FLOOR-BELOW))
 (20 20 (:REWRITE THE-FLOOR-ABOVE))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13 11 (:REWRITE SIMPLIFY-SUMS-<))
 (13 9 (:REWRITE |(+ 0 x)|))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE CONSTANT-<-INTEGERP))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< c (- x))|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11 11
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11 11 (:REWRITE |(< (/ x) (/ y))|))
 (11 11 (:REWRITE |(< (- x) c)|))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (6 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(subrangep x x)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1
  1
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(r32 addr (init_pdpt-modify s))|
 (408 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (310 274 (:REWRITE DEFAULT-PLUS-2))
 (274 274 (:REWRITE DEFAULT-PLUS-1))
 (120 120
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (120 120 (:REWRITE NORMALIZE-ADDENDS))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (55 55
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (55 55 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (55 55 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (55 55
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (36
   36
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (36
  36
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (32 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (19 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19 1 (:REWRITE DISJOINT-3-ITEMS))
 (16
  16
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (16
  16
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (15 15
     (:REWRITE |(g field (w32 addr val st))|))
 (15 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 12 (:REWRITE SIMPLIFY-SUMS-<))
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
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (8 4 (:REWRITE DEFAULT-TIMES-2))
 (8 4 (:REWRITE DEFAULT-TIMES-1))
 (6 6
    (:REWRITE |(G field (INIT_PDPT-MODIFY-loop-1 i s))|))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(r32 addr (init_pdpt-modify s)) --- written to 1|
 (610 459 (:REWRITE DEFAULT-PLUS-2))
 (531 459 (:REWRITE DEFAULT-PLUS-1))
 (371 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (211 211
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (211 211 (:REWRITE NORMALIZE-ADDENDS))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (61 61
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (61 61
     (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (60 60
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (60 60 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (60 60 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (60 60
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (49
   49
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (49
  49
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (49 49
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (49 49
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (49 49
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (49 49
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (32 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (21 13 (:REWRITE DEFAULT-TIMES-2))
 (21 13 (:REWRITE DEFAULT-TIMES-1))
 (20 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (20 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15
     (:REWRITE |(g field (w32 addr val st))|))
 (15
  15
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (15
  15
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 4 (:REWRITE DEFAULT-LOGIOR-2))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE |(G field (INIT_PDPT-MODIFY-loop-1 i s))|))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE DEFAULT-LOGIOR-1))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(r32 addr (init_pdpt-modify s)) --- written to 2|
 (709 520 (:REWRITE DEFAULT-PLUS-2))
 (616 520 (:REWRITE DEFAULT-PLUS-1))
 (371 22
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (230 230
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (230 230 (:REWRITE NORMALIZE-ADDENDS))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (55 55
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (55 55 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (55 55 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (55 55
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (50
   50
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (50
  50
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (50 50
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (46 46 (:REWRITE FOLD-CONSTS-IN-+))
 (32 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (20 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15
     (:REWRITE |(g field (w32 addr val st))|))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (14
  14
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (14
  14
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 7 (:REWRITE DEFAULT-TIMES-1))
 (11 1 (:REWRITE DISJOINT-4-ITEMS))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE |(G field (INIT_PDPT-MODIFY-loop-1 i s))|))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 2 (:REWRITE DEFAULT-LOGIOR-2))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE DEFAULT-LOGIOR-1))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(INIT_PDPT-ASSERTION)
($$$INSUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$PRESUB-IMPLIES-INSUB)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-test|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-base|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-step|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-fn|
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1|
 (1
   1
   (:TYPE-PRESCRIPTION |$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-DEF|)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
($$$STEPS-TO-EXITPOINT-SUB-TAIL-DEF (4 4 (:REWRITE DEFAULT-CAR))
                                    (2 2 (:REWRITE DEFAULT-CDR)))
($$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF)
($$$STEPS-TO-EXITPOINT-SUB (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                           (2 2
                              (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR)))
($$$NEXT-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB-SUFF)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn| (4 4 (:REWRITE DEFAULT-<-2))
                                           (4 4 (:REWRITE DEFAULT-<-1))
                                           (1 1 (:REWRITE ZP-OPEN))
                                           (1 1 (:REWRITE DEFAULT-+-2))
                                           (1 1 (:REWRITE DEFAULT-+-1)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF)
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION
 (238 2 (:DEFINITION BINARY-LOGAND))
 (198 2 (:DEFINITION FLOOR))
 (184 1 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (128 79 (:REWRITE DEFAULT-+-2))
 (104 2
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (97 79 (:REWRITE DEFAULT-+-1))
 (41 20 (:REWRITE DEFAULT-<-1))
 (31 31
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (31 31 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (31 31 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (31 31
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (28 2 (:REWRITE COMMUTATIVITY-OF-*))
 (27 20 (:REWRITE DEFAULT-<-2))
 (26 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (19
  19
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (18 8 (:REWRITE DEFAULT-*-2))
 (18 2 (:REWRITE DISTRIBUTIVITY))
 (18 2 (:DEFINITION NFIX))
 (12 8 (:REWRITE DEFAULT-*-1))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (8 8
    (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (7
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (7
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (6 2 (:REWRITE DEFAULT-NUMERATOR))
 (6 2 (:REWRITE DEFAULT-DENOMINATOR))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE O-INFP->NEQ-0)))
($$$ASSERTION-MAIN-IMPLIES-POST
 (11849 41 (:DEFINITION BINARY-LOGAND))
 (9963 41 (:DEFINITION FLOOR))
 (8043 20
       (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (6724 82
       (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (2914 1206 (:REWRITE DEFAULT-+-2))
 (2085 1206 (:REWRITE DEFAULT-+-1))
 (1722 82 (:DEFINITION NFIX))
 (1128 328 (:REWRITE DEFAULT-<-1))
 (1066 246 (:REWRITE DEFAULT-UNARY-MINUS))
 (858 328 (:REWRITE DEFAULT-<-2))
 (820 41 (:REWRITE ZIP-OPEN))
 (820 41 (:REWRITE COMMUTATIVITY-OF-*))
 (463 176 (:REWRITE DEFAULT-*-2))
 (298 49 (:REWRITE O-INFP->NEQ-0))
 (287 41 (:REWRITE DEFAULT-NUMERATOR))
 (287 41 (:REWRITE DEFAULT-DENOMINATOR))
 (285 15 (:REWRITE |(n32p x)|))
 (205 205
      (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (205 205
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (205 205 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (205 205 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (205 205
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (185 49 (:REWRITE |(n32-to-i32 x) --- 2|))
 (185 49 (:REWRITE |(n32-to-i32 x) --- 1|))
 (176 176 (:REWRITE DEFAULT-*-1))
 (85 5
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (75 10
     (:REWRITE |(good-32-address-p addr st)|))
 (68 68
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (54 18
     (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (52 52
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (20 12
     (:REWRITE |(paging-p (w32 addr val st))|))
 (20 5
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (18 3 (:REWRITE DISJOINT-4-ITEMS))
 (8 4
    (:REWRITE |(paging-p (init_pdpt-modify-loop-1 loop-counter s))|))
 (4 1 (:REWRITE ZP-OPEN))
 (3 3
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (3
  3
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (3
  3
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2 2 (:TYPE-PRESCRIPTION N32P)))
($$$ASSERTION-IMPLIES-CUTPOINT
 (1445 5 (:DEFINITION BINARY-LOGAND))
 (1239 2 (:DEFINITION INIT_PDPT-MODIFY-LOOP-1))
 (1215 5 (:DEFINITION FLOOR))
 (820 10
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (590 258 (:REWRITE DEFAULT-+-2))
 (381 258 (:REWRITE DEFAULT-+-1))
 (285 15 (:REWRITE |(n32p x)|))
 (210 10 (:DEFINITION NFIX))
 (204 68 (:REWRITE DEFAULT-<-1))
 (164 68 (:REWRITE DEFAULT-<-2))
 (130 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (100 5 (:REWRITE ZIP-OPEN))
 (100 5 (:REWRITE COMMUTATIVITY-OF-*))
 (67 32 (:REWRITE DEFAULT-*-2))
 (54 18
     (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (45 1
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (43 43
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (43 43 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (43 43 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (43 43
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (43 2
     (:REWRITE |(good-32-address-p addr st)|))
 (40 7 (:REWRITE O-INFP->NEQ-0))
 (35 5 (:REWRITE DEFAULT-NUMERATOR))
 (35 5 (:REWRITE DEFAULT-DENOMINATOR))
 (34 34
     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (32 32 (:REWRITE DEFAULT-*-1))
 (25 25
     (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (18 3 (:REWRITE DISJOINT-4-ITEMS))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (4 4
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4
    (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 1 (:REWRITE ZP-OPEN))
 (4 1
    (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (3 3
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (3
  3
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (3
  3
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2 2 (:TYPE-PRESCRIPTION N32P)))
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
(SIMULATION-DEFAULT-HINT (5 5 (:TYPE-PRESCRIPTION LAST)))
(SIMULATE-MAIN
 (48556 37707 (:REWRITE DEFAULT-PLUS-1))
 (22298 1498
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
 (21667 21667
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18629 18629
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18629 18629
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18629 18629
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (17790 3558 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (17790 3558 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (17790 3558
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (17790 3558
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6247 994
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5796 2708
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5584 2708
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5375 76 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (5306 2840 (:REWRITE DEFAULT-TIMES-2))
 (5263 4071 (:REWRITE DEFAULT-LESS-THAN-2))
 (4804 346 (:REWRITE |(* x (+ y z))|))
 (4375 994
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4270 4070
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4071 4071 (:REWRITE THE-FLOOR-BELOW))
 (4071 4071 (:REWRITE THE-FLOOR-ABOVE))
 (4066 4066
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3639 76 (:REWRITE MOD-ZERO . 1))
 (3558 3558 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3558 3558
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3558 3558
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3558 3558
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3558 3558
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3521 84 (:LINEAR MOD-BOUNDS-3))
 (3368 88 (:REWRITE MOD-ZERO . 3))
 (3182 2840 (:REWRITE DEFAULT-TIMES-1))
 (3115 1072
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2878 106 (:REWRITE DEFAULT-MOD-RATIO))
 (2873 737 (:REWRITE ACL2-NUMBERP-X))
 (2785 2709
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2772 1400 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2738
   2738
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2738
  2738
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2738
      2738
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2738
     2738
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2738 2738
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2738 2738
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2734 1352
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
 (2734 1352 (:REWRITE INIT_PDTS-LOADED-THM-08))
 (2709 2709 (:REWRITE INTEGERP-<-CONSTANT))
 (2709 2709 (:REWRITE CONSTANT-<-INTEGERP))
 (2709 2709
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2709 2709
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2709 2709
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2709 2709
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2709 2709 (:REWRITE |(< c (- x))|))
 (2709 2709
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2709 2709
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2709 2709
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2709 2709 (:REWRITE |(< (/ x) (/ y))|))
 (2709 2709 (:REWRITE |(< (- x) c)|))
 (2709 2709 (:REWRITE |(< (- x) (- y))|))
 (2583 76 (:REWRITE O-INFP->NEQ-0))
 (2564 234 (:REWRITE DISJOINT-4-ITEMS))
 (2470 2470
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2006 2006 (:REWRITE |(< (+ c/d x) y)|))
 (2004 500 (:REWRITE DEFAULT-LOGIOR-2))
 (1935 1528
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1830 936
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1324 28 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1072 1072
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1068 267 (:REWRITE RATIONALP-X))
 (1050 28 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (1006 500 (:REWRITE DEFAULT-LOGIOR-1))
 (1006 168 (:LINEAR MOD-BOUNDS-2))
 (994 994
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (994 994 (:REWRITE |(equal c (/ x))|))
 (994 994 (:REWRITE |(equal c (- x))|))
 (994 994 (:REWRITE |(equal (/ x) c)|))
 (994 994 (:REWRITE |(equal (/ x) (/ y))|))
 (994 994 (:REWRITE |(equal (- x) c)|))
 (994 994 (:REWRITE |(equal (- x) (- y))|))
 (966 28 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (936 936
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (936 936
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (936 936
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (704 88 (:REWRITE MOD-X-Y-=-X . 4))
 (649 649 (:REWRITE |(< (+ (- c) x) y)|))
 (618 106 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (616 88 (:REWRITE MOD-ZERO . 4))
 (616 88 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (595 85 (:REWRITE MOD-X-Y-=-X . 2))
 (595 85 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (595 85
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (530 76 (:REWRITE MOD-ZERO . 2))
 (530 76 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (528 88 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (511 511 (:REWRITE REDUCE-INTEGERP-+))
 (511 511 (:REWRITE INTEGERP-MINUS-X))
 (511 511 (:META META-INTEGERP-CORRECT))
 (510 85
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (510 85
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (510 85
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (480 85 (:REWRITE MOD-CANCEL-*-CONST))
 (473 473 (:REWRITE FOLD-CONSTS-IN-+))
 (464 464 (:REWRITE |(subrangep x x)|))
 (457 457 (:REWRITE |(< x (+ c/d y))|))
 (380 190 (:REWRITE DEFAULT-MINUS))
 (297 297 (:REWRITE |(< y (+ (- c) x))|))
 (282 282
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (282 282
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (282 282
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (267 267 (:REWRITE REDUCE-RATIONALP-+))
 (267 267 (:REWRITE REDUCE-RATIONALP-*))
 (267 267 (:REWRITE RATIONALP-MINUS-X))
 (267 267 (:META META-RATIONALP-CORRECT))
 (240 240
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (218 166
      (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (194 106 (:REWRITE DEFAULT-MOD-1))
 (168 28 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (151 76
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (106 106 (:REWRITE DEFAULT-MOD-2))
 (85 85
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (85 85 (:REWRITE |(mod x (- y))| . 3))
 (85 85 (:REWRITE |(mod x (- y))| . 2))
 (85 85 (:REWRITE |(mod x (- y))| . 1))
 (85 85
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (85 85
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (85 85 (:REWRITE |(mod (- x) y)| . 3))
 (85 85 (:REWRITE |(mod (- x) y)| . 2))
 (85 85 (:REWRITE |(mod (- x) y)| . 1))
 (85 85
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (85 85
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (85 85
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (80 8 (:REWRITE DEFAULT-FLOOR-RATIO))
 (76 76
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (56 4 (:REWRITE |(* y (* x z))|))
 (46 46 (:REWRITE |(< (* x y) 0)|))
 (39 38 (:REWRITE DEFAULT-LOGAND-2))
 (39 38 (:REWRITE DEFAULT-LOGAND-1))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (29 29 (:REWRITE |(< 0 (/ x))|))
 (29 29 (:REWRITE |(< 0 (* x y))|))
 (16 8 (:REWRITE DEFAULT-FLOOR-1))
 (8 8 (:REWRITE DEFAULT-FLOOR-2))
 (8 4 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 1
    (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32)))
(ASSERTION-INVARIANT-DEFAULT-HINT-1)
(ASSERTION-INVARIANT-DEFAULT-HINT)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS
 (304393 238605 (:REWRITE DEFAULT-PLUS-1))
 (107612 107612
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (68648 2325 (:REWRITE |(n32-to-i32 x) --- 2|))
 (21995
   21995
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (21995
  21995
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21995
      21995
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21995
     21995
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21995 21995
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21995 21995
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (19632 14452 (:REWRITE DEFAULT-LESS-THAN-2))
 (19257 179
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (19246 9563
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (19244 9563
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18846 9792 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (14452 14452 (:REWRITE THE-FLOOR-BELOW))
 (14452 14452 (:REWRITE THE-FLOOR-ABOVE))
 (14426 14426
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14426 14426
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12214 84 (:REWRITE DISJOINT-3-ITEMS))
 (9608 9608 (:REWRITE INTEGERP-<-CONSTANT))
 (9608 9608 (:REWRITE CONSTANT-<-INTEGERP))
 (9608 9608
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (9608 9608
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (9608 9608
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (9608 9608
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (9608 9608 (:REWRITE |(< c (- x))|))
 (9608 9608
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9608 9608
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (9608 9608
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (9608 9608
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (9608 9608 (:REWRITE |(< (/ x) (/ y))|))
 (9608 9608 (:REWRITE |(< (- x) c)|))
 (9608 9608 (:REWRITE |(< (- x) (- y))|))
 (8663 8663 (:REWRITE |(< (+ c/d x) y)|))
 (8501 8501 (:REWRITE DEFAULT-TIMES-2))
 (8501 8501 (:REWRITE DEFAULT-TIMES-1))
 (7767 1303 (:REWRITE ACL2-NUMBERP-X))
 (6726 6726
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6469 6469 (:REWRITE FOLD-CONSTS-IN-+))
 (6073 1801
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4473 1801
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4044 1340 (:REWRITE DEFAULT-LOGIOR-2))
 (3845 3845 (:REWRITE |(< (+ (- c) x) y)|))
 (3808 112 (:REWRITE ZP-OPEN))
 (3232 808 (:REWRITE RATIONALP-X))
 (3169 3169 (:REWRITE |(< x (+ c/d y))|))
 (2248 2248
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2150 1340 (:REWRITE DEFAULT-LOGIOR-1))
 (2034 2034 (:REWRITE |(< y (+ (- c) x))|))
 (1801 1801
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1801 1801 (:REWRITE |(equal c (/ x))|))
 (1801 1801 (:REWRITE |(equal c (- x))|))
 (1801 1801 (:REWRITE |(equal (/ x) c)|))
 (1801 1801 (:REWRITE |(equal (/ x) (/ y))|))
 (1801 1801 (:REWRITE |(equal (- x) c)|))
 (1801 1801 (:REWRITE |(equal (- x) (- y))|))
 (1206 327
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (1090 218 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (872 218 (:REWRITE |(+ (* c x) (* d x))|))
 (842 842 (:REWRITE REDUCE-INTEGERP-+))
 (842 842 (:REWRITE INTEGERP-MINUS-X))
 (842 842 (:META META-INTEGERP-CORRECT))
 (808 808 (:REWRITE REDUCE-RATIONALP-+))
 (808 808 (:REWRITE REDUCE-RATIONALP-*))
 (808 808 (:REWRITE RATIONALP-MINUS-X))
 (808 808 (:META META-RATIONALP-CORRECT))
 (700 700
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (700 700
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (568 4
      (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (559 559
      (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (486 12 (:REWRITE |(< (if a b c) x)|))
 (247 116 (:REWRITE O-INFP->NEQ-0))
 (244 244 (:REWRITE |(< (* x y) 0)|))
 (218 218
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (218 218
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (218 218 (:REWRITE |(< 0 (/ x))|))
 (218 218 (:REWRITE |(< 0 (* x y))|))
 (218 218 (:REWRITE |(* 0 x)|))
 (116 116
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:TYPE-PRESCRIPTION N32-TO-I32)))
(EXITSTEPS-TAIL)
(|EXITSTEPS-TAIL-arity-1-defpun-test|)
(|EXITSTEPS-TAIL-arity-1-defpun-base|)
(|EXITSTEPS-TAIL-arity-1-step|)
(|EXITSTEPS-TAIL-arity-1-defpun-stn|)
(|EXITSTEPS-TAIL-arity-1-defpun-fn| (4 4 (:REWRITE DEFAULT-<-2))
                                    (4 4 (:REWRITE DEFAULT-<-1))
                                    (1 1 (:REWRITE ZP-OPEN))
                                    (1 1 (:REWRITE DEFAULT-+-2))
                                    (1 1 (:REWRITE DEFAULT-+-1)))
(|EXITSTEPS-TAIL-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION |EXITSTEPS-TAIL-arity-1-defpun-stn|)))
(|EXITSTEPS-TAIL-arity-1-DEF|)
(EXITSTEPS-TAIL)
(EXITSTEPS-TAIL-DEF (6 6 (:REWRITE DEFAULT-CAR))
                    (4 2 (:REWRITE DEFAULT-+-2))
                    (3 3 (:REWRITE DEFAULT-CDR))
                    (2 2
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (2 2 (:REWRITE DEFAULT-+-1)))
(EXITSTEPS-TAIL$DEF)
(EXITSTEPS)
(EXISTS-NEXT-EXITPOINT)
(EXISTS-NEXT-EXITPOINT-SUFF)
(NEXT-EXITPOINT)
(INIT_PDPT-CORRECT)
(IN-INIT_PDTS)
(INIT_PDTS-CUTPOINT-P)
(INIT_PDTS-PRE)
(INIT_PDTS-OUTER-LOOP-PRE)
(INIT_PDTS-INNER-LOOP-PRE)
(INIT_PDTS-MODIFY-INNER-LOOP-1)
(|(paging-p (init_pdts-modify-inner-loop-1 i j s))|
     (438 6 (:DEFINITION BINARY-LOGAND))
     (342 6 (:DEFINITION FLOOR))
     (296 152 (:REWRITE DEFAULT-+-2))
     (242 152 (:REWRITE DEFAULT-+-1))
     (192 12
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (138 60
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (75 63 (:REWRITE DEFAULT-*-2))
     (69 63 (:REWRITE DEFAULT-*-1))
     (60 60 (:TYPE-PRESCRIPTION R32))
     (60 60 (:TYPE-PRESCRIPTION MEMORYP))
     (48 36 (:REWRITE DEFAULT-UNARY-MINUS))
     (36 12 (:DEFINITION NFIX))
     (30 30
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (30 30 (:REWRITE DEFAULT-<-2))
     (30 30 (:REWRITE DEFAULT-<-1))
     (30 6 (:REWRITE DISTRIBUTIVITY))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (18 18
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (18 6 (:REWRITE UNICITY-OF-0))
     (12 6 (:REWRITE ZIP-OPEN))
     (12 6 (:DEFINITION FIX))
     (6 6 (:REWRITE O-INFP->NEQ-0))
     (6 6 (:REWRITE DEFAULT-NUMERATOR))
     (6 6 (:REWRITE DEFAULT-DENOMINATOR))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+)))
(|(va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))|
     (366 1
          (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (188 2 (:DEFINITION BINARY-LOGIOR))
     (146 2 (:DEFINITION BINARY-LOGAND))
     (114 2 (:DEFINITION FLOOR))
     (99 51 (:REWRITE DEFAULT-+-2))
     (93 19 (:REWRITE COMMUTATIVITY-OF-+))
     (81 51 (:REWRITE DEFAULT-+-1))
     (64 4
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (46 20
         (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (40 4 (:DEFINITION LOGNOT))
     (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
     (25 21 (:REWRITE DEFAULT-*-2))
     (23 21 (:REWRITE DEFAULT-*-1))
     (22 4 (:REWRITE COMMUTATIVITY-OF-*))
     (20 20 (:TYPE-PRESCRIPTION R32))
     (20 20 (:TYPE-PRESCRIPTION MEMORYP))
     (16 16 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (16 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 4 (:DEFINITION NFIX))
     (10 10
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1))
     (10 8 (:DEFINITION IFIX))
     (10 2 (:REWRITE DISTRIBUTIVITY))
     (8 8
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (8 8
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 2 (:REWRITE ZIP-OPEN))
     (4 2 (:DEFINITION FIX))
     (2 2 (:REWRITE O-INFP->NEQ-0))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(|(good-32-address-p addr (init_pdts-modify-inner-loop-1 i j s))|
     (366 1
          (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (188 2 (:DEFINITION BINARY-LOGIOR))
     (146 2 (:DEFINITION BINARY-LOGAND))
     (114 2 (:DEFINITION FLOOR))
     (101 53 (:REWRITE DEFAULT-+-2))
     (93 19 (:REWRITE COMMUTATIVITY-OF-+))
     (83 53 (:REWRITE DEFAULT-+-1))
     (64 4
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (46 20
         (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (40 4 (:DEFINITION LOGNOT))
     (25 21 (:REWRITE DEFAULT-*-2))
     (23 21 (:REWRITE DEFAULT-*-1))
     (23 7 (:REWRITE |(n32p x)|))
     (22 4 (:REWRITE COMMUTATIVITY-OF-*))
     (20 20 (:TYPE-PRESCRIPTION R32))
     (20 20 (:TYPE-PRESCRIPTION MEMORYP))
     (16 16 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (16 12 (:REWRITE DEFAULT-UNARY-MINUS))
     (14 14 (:REWRITE DEFAULT-<-2))
     (14 14 (:REWRITE DEFAULT-<-1))
     (12 4 (:DEFINITION NFIX))
     (10 10
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (10 8 (:DEFINITION IFIX))
     (10 2 (:REWRITE DISTRIBUTIVITY))
     (8 8
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (8 8
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (8 2
        (:REWRITE |(good-32-address-p addr st)|))
     (6 6
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 4
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (4 4
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (4 2 (:REWRITE ZIP-OPEN))
     (4 2 (:DEFINITION FIX))
     (2 2 (:TYPE-PRESCRIPTION N32P))
     (2 2 (:REWRITE O-INFP->NEQ-0))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 1
        (:REWRITE |(paging-p (init_pdts-modify-inner-loop-1 i j s))|))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+)))
(|(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|
     (469 77 (:REWRITE ACL2-NUMBERP-X))
     (266 104 (:REWRITE DEFAULT-PLUS-1))
     (196 49 (:REWRITE RATIONALP-X))
     (70 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (61 61 (:REWRITE REDUCE-INTEGERP-+))
     (61 61 (:REWRITE INTEGERP-MINUS-X))
     (61 61 (:META META-INTEGERP-CORRECT))
     (49 49 (:REWRITE REDUCE-RATIONALP-+))
     (49 49 (:REWRITE REDUCE-RATIONALP-*))
     (49 49 (:REWRITE RATIONALP-MINUS-X))
     (49 49 (:META META-RATIONALP-CORRECT))
     (41 41
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (41 41 (:REWRITE NORMALIZE-ADDENDS))
     (33 33
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (14 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE DEFAULT-LOGIOR-1))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE FOLD-CONSTS-IN-+))
     (3 3 (:REWRITE |(+ c (+ d x))|)))
(|(y86-p (init_pdts-modify-inner-loop-1 i j s))|
 (472 29
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (305 158 (:REWRITE DEFAULT-PLUS-2))
 (190 158 (:REWRITE DEFAULT-PLUS-1))
 (141 7 (:REWRITE |(+ y (+ x z))|))
 (123 123 (:REWRITE REDUCE-INTEGERP-+))
 (123 123 (:REWRITE INTEGERP-MINUS-X))
 (123 123 (:META META-INTEGERP-CORRECT))
 (104 104
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (104 104 (:REWRITE NORMALIZE-ADDENDS))
 (103 31
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (93 93 (:REWRITE DEFAULT-TIMES-2))
 (93 93 (:REWRITE DEFAULT-TIMES-1))
 (73 73
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (68 68
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (68 68 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (68 68 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (68 68
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (59 31 (:REWRITE DEFAULT-LESS-THAN-1))
 (35
   35
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (35
  35
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (34 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (34 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (31 31 (:REWRITE THE-FLOOR-BELOW))
 (31 31 (:REWRITE THE-FLOOR-ABOVE))
 (31 31 (:REWRITE DEFAULT-LESS-THAN-2))
 (29 29
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 22
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (20 20 (:REWRITE SIMPLIFY-SUMS-<))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (15 15 (:REWRITE |(< (+ c/d x) y)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE DEFAULT-LOGIOR-2))
 (9 9 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6
    (:REWRITE |(g field (w32 addr val st))|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(|(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|
 (402 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (250 128 (:REWRITE DEFAULT-PLUS-2))
 (152 128 (:REWRITE DEFAULT-PLUS-1))
 (120 6 (:REWRITE |(+ y (+ x z))|))
 (98 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (84 84
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (84 84 (:REWRITE NORMALIZE-ADDENDS))
 (74 74 (:REWRITE DEFAULT-TIMES-2))
 (74 74 (:REWRITE DEFAULT-TIMES-1))
 (58 58
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (56 56
     (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (56 56 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (56 56 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (56 56
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (50 26 (:REWRITE DEFAULT-LESS-THAN-1))
 (28 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
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
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (14
   14
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (14
  14
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (14 14
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (* x y) 0)|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:REWRITE DEFAULT-LOGIOR-2))
 (7 7 (:REWRITE DEFAULT-LOGIOR-1))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6 6
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (6 6
    (:REWRITE |(g field (w32 addr val st))|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:REWRITE ZP-OPEN))
 (3 3
    (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(|(good-state-p (init_pdts-modify-inner-loop-1 i j s))|
 (5744 10
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (4490 2094 (:REWRITE DEFAULT-PLUS-2))
 (4026 117
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3290 10
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (3214 2094 (:REWRITE DEFAULT-PLUS-1))
 (3192
  48
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2184 8 (:REWRITE DISJOINT-3-ITEMS))
 (1808
  48
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1594 74 (:REWRITE SIMPLIFY-SUMS-<))
 (1500 1020 (:REWRITE NORMALIZE-ADDENDS))
 (988 988
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (400 400
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (400 400 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (400 400 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (400 400
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (349 19 (:REWRITE ZP-OPEN))
 (336 8
      (:REWRITE |(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|))
 (277 277 (:REWRITE FOLD-CONSTS-IN-+))
 (241 117 (:REWRITE DEFAULT-LESS-THAN-1))
 (192 16 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (182 16 (:REWRITE DISJOINT-5-ITEMS))
 (168 74
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (168 74 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (165 117 (:REWRITE DEFAULT-LESS-THAN-2))
 (164 164 (:REWRITE DEFAULT-TIMES-2))
 (164 164 (:REWRITE DEFAULT-TIMES-1))
 (136 136
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (121
   121
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (121
  121
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (121 121
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (121
     121
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (121 121
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (121 121
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (117 117 (:REWRITE THE-FLOOR-BELOW))
 (117 117 (:REWRITE THE-FLOOR-ABOVE))
 (117 117
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (117 117
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (96 48 (:DEFINITION FIX))
 (78 78
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (78 78 (:REWRITE INTEGERP-<-CONSTANT))
 (78 78 (:REWRITE CONSTANT-<-INTEGERP))
 (78 78
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (78 78
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (78 78
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (78 78
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (78 78 (:REWRITE |(< c (- x))|))
 (78 78
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 78
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (78 78 (:REWRITE |(< (/ x) (/ y))|))
 (78 78 (:REWRITE |(< (- x) c)|))
 (78 78 (:REWRITE |(< (- x) (- y))|))
 (66 66 (:REWRITE |(< (+ c/d x) y)|))
 (64 32 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (64 16 (:REWRITE |(+ (* c x) (* d x))|))
 (32 16 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (32 16
     (:REWRITE |(va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))|))
 (27 27 (:REWRITE |(< (+ (- c) x) y)|))
 (26 26 (:REWRITE |(< x (+ c/d y))|))
 (25 25 (:REWRITE DEFAULT-LOGIOR-2))
 (25 25 (:REWRITE DEFAULT-LOGIOR-1))
 (24 6 (:REWRITE |(* y x)|))
 (24 6 (:REWRITE |(* c (* d x))|))
 (18 18 (:REWRITE |(< y (+ (- c) x))|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (16 16 (:REWRITE |(va-to-pa addr st)|))
 (16 16 (:REWRITE |(+ x (- x))|))
 (16 16 (:REWRITE |(* 0 x)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (8 8
    (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT)))
(|(r32 addr (init_pdts-modify-inner-loop-1 i j s))|
 (1449 736 (:REWRITE DEFAULT-PLUS-2))
 (1114 736 (:REWRITE DEFAULT-PLUS-1))
 (706 41
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (359 359
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (359 359 (:REWRITE NORMALIZE-ADDENDS))
 (210 210
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (210 210 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (210 210 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (210 210
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (162 162 (:REWRITE DEFAULT-TIMES-2))
 (162 162 (:REWRITE DEFAULT-TIMES-1))
 (144 144
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (115 43
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (75 75 (:REWRITE FOLD-CONSTS-IN-+))
 (73
   73
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (73
  73
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (73 73
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (71 43 (:REWRITE DEFAULT-LESS-THAN-1))
 (43 43 (:REWRITE THE-FLOOR-BELOW))
 (43 43 (:REWRITE THE-FLOOR-ABOVE))
 (43 43 (:REWRITE DEFAULT-LESS-THAN-2))
 (42 42
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (41 41
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (39 25
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (39 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (28 28
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (28 28 (:REWRITE INTEGERP-<-CONSTANT))
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
 (25 25 (:REWRITE SIMPLIFY-SUMS-<))
 (25 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (25 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (22
  22
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (22
  22
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (21 21 (:REWRITE |(< (+ c/d x) y)|))
 (15 15
     (:REWRITE |(g field (w32 addr val st))|))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 14 (:REWRITE INTEGERP-MINUS-X))
 (14 14 (:META META-INTEGERP-CORRECT))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE |(< (/ x) 0)|))
 (9 1
    (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (8 8
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE DEFAULT-LOGIOR-2))
 (8 8 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:REWRITE ZP-OPEN))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(|(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 1|
 (7641 3613 (:REWRITE DEFAULT-PLUS-2))
 (6859 3613 (:REWRITE DEFAULT-PLUS-1))
 (5622 398
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4348 504
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1553 331 (:REWRITE INTEGERP-<-CONSTANT))
 (1171 1171
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (854 666 (:REWRITE DEFAULT-TIMES-2))
 (788 504 (:REWRITE DEFAULT-LESS-THAN-2))
 (782 278 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (767 8
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (760 278
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (741 741
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (741 741
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (736 504 (:REWRITE DEFAULT-LESS-THAN-1))
 (666 666 (:REWRITE DEFAULT-TIMES-1))
 (655 55 (:REWRITE |(* y (* x z))|))
 (504 504 (:REWRITE THE-FLOOR-BELOW))
 (504 504 (:REWRITE THE-FLOOR-ABOVE))
 (447 447
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (398 398
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (331 331 (:REWRITE CONSTANT-<-INTEGERP))
 (331 331
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (331 331
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (331 331
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (331 331
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (331 331 (:REWRITE |(< c (- x))|))
 (331 331
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (331 331
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (331 331
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (331 331
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (331 331 (:REWRITE |(< (/ x) (/ y))|))
 (331 331 (:REWRITE |(< (- x) c)|))
 (331 331 (:REWRITE |(< (- x) (- y))|))
 (322 322
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (322 322 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (322 322 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (322 322
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (288 24 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (284 284
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (252 252 (:REWRITE |(< (+ c/d x) y)|))
 (250 250 (:REWRITE FOLD-CONSTS-IN-+))
 (239 239 (:REWRITE |(* (- x) y)|))
 (228
   228
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (228
  228
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (228 228
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (228
     228
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (228 228
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (228 228
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (106 106 (:TYPE-PRESCRIPTION ABS))
 (96 24 (:REWRITE |(+ (* c x) (* d x))|))
 (95 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (95 17
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (81 81 (:REWRITE |(< y (+ (- c) x))|))
 (81 81 (:REWRITE |(< x (+ c/d y))|))
 (72 72 (:REWRITE |(< (* x y) 0)|))
 (70 70 (:REWRITE DEFAULT-LOGIOR-2))
 (70 70 (:REWRITE DEFAULT-LOGIOR-1))
 (69 69
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (68 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (68 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (68 11
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (56 56
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (49 49
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (47 47 (:REWRITE |(* a (/ a) b)|))
 (42 7 (:REWRITE DISJOINT-3-ITEMS))
 (24 24 (:REWRITE |(* 0 x)|))
 (22 22 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (21 21 (:REWRITE |(< 0 (* x y))|))
 (19 19 (:REWRITE |(< (/ x) 0)|))
 (17 17 (:REWRITE |(< 0 (/ x))|))
 (16 16
     (:REWRITE |(g field (w32 addr val st))|))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (11 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11 11 (:REWRITE |(equal c (/ x))|))
 (11 11 (:REWRITE |(equal c (- x))|))
 (11 11 (:REWRITE |(equal (/ x) c)|))
 (11 11 (:REWRITE |(equal (/ x) (/ y))|))
 (11 11 (:REWRITE |(equal (- x) c)|))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* 1 x)|))
 (4 1
    (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(|(r32 addr (init_pdts-modify-inner-loop-1 i j s)) --- written to 2|
 (17582 378
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9222 4087 (:REWRITE DEFAULT-PLUS-2))
 (7161 4087 (:REWRITE DEFAULT-PLUS-1))
 (3954 464
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1375 1375
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1251 263 (:REWRITE INTEGERP-<-CONSTANT))
 (1106 80 (:REWRITE |(* y (* x z))|))
 (925 621 (:REWRITE DEFAULT-TIMES-2))
 (828 464 (:REWRITE DEFAULT-LESS-THAN-2))
 (783 8
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (746 464 (:REWRITE DEFAULT-LESS-THAN-1))
 (699 219
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (674 242 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (621 621 (:REWRITE DEFAULT-TIMES-1))
 (472 472 (:REWRITE FOLD-CONSTS-IN-+))
 (464 464 (:REWRITE THE-FLOOR-BELOW))
 (464 464 (:REWRITE THE-FLOOR-ABOVE))
 (409 409
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (378 378
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (292 292
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (292 292 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (292 292 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (292 292
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (288 24 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (270 270 (:REWRITE |(< (+ c/d x) y)|))
 (263 263 (:REWRITE CONSTANT-<-INTEGERP))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (263 263 (:REWRITE |(< c (- x))|))
 (263 263
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (263 263
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (263 263
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (263 263 (:REWRITE |(< (/ x) (/ y))|))
 (263 263 (:REWRITE |(< (- x) c)|))
 (263 263 (:REWRITE |(< (- x) (- y))|))
 (260
   260
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (260
  260
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (260
     260
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (260 260
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (232 232 (:REWRITE |(* (- x) y)|))
 (225 225
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (116 116 (:REWRITE |(< x (+ c/d y))|))
 (96 24 (:REWRITE |(+ (* c x) (* d x))|))
 (86 86 (:TYPE-PRESCRIPTION ABS))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (60 60
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (60 60 (:REWRITE |(< (* x y) 0)|))
 (54 54 (:REWRITE |(< y (+ (- c) x))|))
 (50 50
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (42 7 (:REWRITE DISJOINT-3-ITEMS))
 (40 40
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (38 38 (:REWRITE |(* a (/ a) b)|))
 (29 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (29 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 5 (:REWRITE O-INFP->NEQ-0))
 (24 24 (:REWRITE |(* 0 x)|))
 (16 16
     (:REWRITE |(g field (w32 addr val st))|))
 (16 16 (:REWRITE |(< (/ x) 0)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE DEFAULT-LOGIOR-2))
 (9 9 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (8 8
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (7 7 (:REWRITE ZP-OPEN))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(|(init_pdts-modify-inner-loop-1 i j (w32 addr val s))|
 (5158 2503 (:REWRITE DEFAULT-PLUS-2))
 (4640 137
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4360 11
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (4036
  106
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (3843 2503 (:REWRITE DEFAULT-PLUS-1))
 (2890 10 (:REWRITE DISJOINT-3-ITEMS))
 (2306
  106
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1986 86 (:REWRITE SIMPLIFY-SUMS-<))
 (1769 1169 (:REWRITE NORMALIZE-ADDENDS))
 (1129 1129
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (416 416 (:REWRITE DEFAULT-TIMES-2))
 (416 416 (:REWRITE DEFAULT-TIMES-1))
 (363 363 (:REWRITE FOLD-CONSTS-IN-+))
 (351 21 (:REWRITE ZP-OPEN))
 (328 328
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (321 321
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (321 321 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (321 321 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (321 321
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (240
   240
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (240
  240
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (240 240
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (240
     240
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (240 240
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (240 240
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (240 20 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (236 139 (:REWRITE DEFAULT-LESS-THAN-1))
 (211 139
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (199 139 (:REWRITE DEFAULT-LESS-THAN-2))
 (175 86
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (175 86 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (139 139 (:REWRITE THE-FLOOR-BELOW))
 (139 139 (:REWRITE THE-FLOOR-ABOVE))
 (137 137
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (120 60 (:DEFINITION FIX))
 (99 27 (:REWRITE ACL2-NUMBERP-X))
 (90 90 (:REWRITE |(< (+ c/d x) y)|))
 (90 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (88 88
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (88 88 (:REWRITE INTEGERP-<-CONSTANT))
 (88 88 (:REWRITE CONSTANT-<-INTEGERP))
 (88 88
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (88 88
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (88 88
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (88 88
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (88 88 (:REWRITE |(< c (- x))|))
 (88 88
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (88 88
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (88 88
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (88 88
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (88 88 (:REWRITE |(< (/ x) (/ y))|))
 (88 88 (:REWRITE |(< (- x) c)|))
 (88 88 (:REWRITE |(< (- x) (- y))|))
 (88 20
     (:REWRITE |(va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))|))
 (80 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (80 20 (:REWRITE |(+ (* c x) (* d x))|))
 (41 41 (:REWRITE |(< (+ (- c) x) y)|))
 (40 40 (:REWRITE DEFAULT-LOGIOR-2))
 (40 40 (:REWRITE DEFAULT-LOGIOR-1))
 (40 20 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (36 9 (:REWRITE RATIONALP-X))
 (36 4 (:REWRITE |(y86-p (w32 addr val s))|))
 (35 35 (:REWRITE REDUCE-INTEGERP-+))
 (35 35 (:REWRITE INTEGERP-MINUS-X))
 (35 35 (:META META-INTEGERP-CORRECT))
 (30 30 (:REWRITE |(< x (+ c/d y))|))
 (23 23 (:REWRITE |(< (* x y) 0)|))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(+ x (- x))|))
 (20 20 (:REWRITE |(* 0 x)|))
 (18 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (18 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (12 12
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:META META-RATIONALP-CORRECT))
 (5 2
    (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(INIT_PDTS-MODIFY-OUTER-LOOP-1)
(|(paging-p (init_pdts-modify-outer-loop-1 i s))|
     (1146 6
           (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (522 6 (:DEFINITION BINARY-LOGIOR))
     (384 6 (:DEFINITION BINARY-LOGAND))
     (341 164 (:REWRITE DEFAULT-+-2))
     (336 63 (:REWRITE COMMUTATIVITY-OF-+))
     (294 6 (:DEFINITION FLOOR))
     (290 164 (:REWRITE DEFAULT-+-1))
     (198 84
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (144 9
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (132 12 (:DEFINITION LOGNOT))
     (84 84 (:TYPE-PRESCRIPTION R32))
     (84 84 (:TYPE-PRESCRIPTION MEMORYP))
     (66 12 (:REWRITE COMMUTATIVITY-OF-*))
     (63 54 (:REWRITE DEFAULT-*-2))
     (63 9 (:REWRITE FOLD-CONSTS-IN-+))
     (57 54 (:REWRITE DEFAULT-*-1))
     (48 48 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (45 33 (:REWRITE DEFAULT-UNARY-MINUS))
     (30 6 (:REWRITE DISTRIBUTIVITY))
     (27 27
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (27 21 (:DEFINITION IFIX))
     (27 9 (:DEFINITION NFIX))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (18 6 (:REWRITE UNICITY-OF-0))
     (12 12
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 6 (:DEFINITION FIX))
     (12 3
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (6 6 (:REWRITE DEFAULT-NUMERATOR))
     (6 6 (:REWRITE DEFAULT-DENOMINATOR))
     (6 3 (:REWRITE ZIP-OPEN))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE O-INFP->NEQ-0)))
(|(va-to-pa addr (init_pdts-modify-outer-loop-1 i s))|
     (386 1
          (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
     (382 2
          (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (174 2 (:DEFINITION BINARY-LOGIOR))
     (128 2 (:DEFINITION BINARY-LOGAND))
     (114 55 (:REWRITE DEFAULT-+-2))
     (112 21 (:REWRITE COMMUTATIVITY-OF-+))
     (98 2 (:DEFINITION FLOOR))
     (97 55 (:REWRITE DEFAULT-+-1))
     (66 28
         (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (48 3
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (44 4 (:DEFINITION LOGNOT))
     (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
     (28 28 (:TYPE-PRESCRIPTION R32))
     (28 28 (:TYPE-PRESCRIPTION MEMORYP))
     (22 4 (:REWRITE COMMUTATIVITY-OF-*))
     (21 18 (:REWRITE DEFAULT-*-2))
     (21 3 (:REWRITE FOLD-CONSTS-IN-+))
     (19 18 (:REWRITE DEFAULT-*-1))
     (16 16 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (15 11 (:REWRITE DEFAULT-UNARY-MINUS))
     (10 2 (:REWRITE DISTRIBUTIVITY))
     (9 9
        (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (9 7 (:DEFINITION IFIX))
     (9 3 (:DEFINITION NFIX))
     (8 8
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (8 8 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (8 8 (:REWRITE DEFAULT-<-2))
     (8 8 (:REWRITE DEFAULT-<-1))
     (8 8
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (6 2 (:REWRITE UNICITY-OF-0))
     (4 4
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 2 (:DEFINITION FIX))
     (4 1
        (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (2 2 (:REWRITE DEFAULT-NUMERATOR))
     (2 2 (:REWRITE DEFAULT-DENOMINATOR))
     (2 1 (:REWRITE ZIP-OPEN))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE O-INFP->NEQ-0)))
(|(good-32-address-p addr (init_pdts-modify-outer-loop-1 i s))|
     (1146 6
           (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (522 6 (:DEFINITION BINARY-LOGIOR))
     (384 6 (:DEFINITION BINARY-LOGAND))
     (341 164 (:REWRITE DEFAULT-+-2))
     (336 63 (:REWRITE COMMUTATIVITY-OF-+))
     (294 6 (:DEFINITION FLOOR))
     (290 164 (:REWRITE DEFAULT-+-1))
     (198 84
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (144 9
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (132 12 (:DEFINITION LOGNOT))
     (84 84 (:TYPE-PRESCRIPTION R32))
     (84 84 (:TYPE-PRESCRIPTION MEMORYP))
     (66 12 (:REWRITE COMMUTATIVITY-OF-*))
     (63 54 (:REWRITE DEFAULT-*-2))
     (63 9 (:REWRITE FOLD-CONSTS-IN-+))
     (57 54 (:REWRITE DEFAULT-*-1))
     (48 48 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (45 33 (:REWRITE DEFAULT-UNARY-MINUS))
     (37 10
         (:REWRITE |(good-32-address-p addr st)|))
     (30 6 (:REWRITE DISTRIBUTIVITY))
     (27 27
         (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (27 21 (:DEFINITION IFIX))
     (27 9 (:DEFINITION NFIX))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24 (:REWRITE DEFAULT-<-2))
     (24 24 (:REWRITE DEFAULT-<-1))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (18 6 (:REWRITE UNICITY-OF-0))
     (12 12
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (12 6 (:DEFINITION FIX))
     (12 3
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (10 10 (:TYPE-PRESCRIPTION N32P))
     (6 6 (:REWRITE DEFAULT-NUMERATOR))
     (6 6 (:REWRITE DEFAULT-DENOMINATOR))
     (6 3 (:REWRITE ZIP-OPEN))
     (5 5 (:REWRITE |(n32p x)|))
     (4 4 (:REWRITE ZP-OPEN))
     (3 3 (:REWRITE O-INFP->NEQ-0)))
(|(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|
     (1335 6
           (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
     (557 119 (:REWRITE DEFAULT-PLUS-2))
     (355 59 (:REWRITE ACL2-NUMBERP-X))
     (336 36 (:REWRITE |(+ y x)|))
     (330 138
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (269 107 (:REWRITE DEFAULT-PLUS-1))
     (174 6 (:REWRITE |(+ x (if a b c))|))
     (148 37 (:REWRITE RATIONALP-X))
     (144 48 (:REWRITE DEFAULT-TIMES-2))
     (138 138 (:TYPE-PRESCRIPTION R32))
     (138 138 (:TYPE-PRESCRIPTION MEMORYP))
     (84 42 (:REWRITE DEFAULT-TIMES-1))
     (75 6 (:REWRITE |(+ c (+ d x))|))
     (70 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (50 50
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (50 50 (:REWRITE NORMALIZE-ADDENDS))
     (43 43 (:REWRITE REDUCE-INTEGERP-+))
     (43 43 (:REWRITE INTEGERP-MINUS-X))
     (43 43 (:META META-INTEGERP-CORRECT))
     (37 37 (:REWRITE REDUCE-RATIONALP-+))
     (37 37 (:REWRITE REDUCE-RATIONALP-*))
     (37 37 (:REWRITE RATIONALP-MINUS-X))
     (37 37 (:META META-RATIONALP-CORRECT))
     (30 9 (:REWRITE DEFAULT-LOGIOR-2))
     (24 24
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (24 24
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (24 24 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (24 24 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (24 24
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (24 6 (:REWRITE |(+ 0 x)|))
     (24 6 (:REWRITE |(* y x)|))
     (24 6 (:REWRITE |(* c (* d x))|))
     (24 3 (:REWRITE |(+ (if a b c) x)|))
     (21 3 (:REWRITE |(* x (if a b c))|))
     (14 7
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (10 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7 7
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7 7 (:REWRITE |(equal c (/ x))|))
     (7 7 (:REWRITE |(equal c (- x))|))
     (7 7 (:REWRITE |(equal (/ x) c)|))
     (7 7 (:REWRITE |(equal (/ x) (/ y))|))
     (7 7 (:REWRITE |(equal (- x) c)|))
     (7 7 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE DEFAULT-LOGIOR-1))
     (4 4 (:REWRITE ZP-OPEN)))
(|(y86-p (init_pdts-modify-outer-loop-1 i s))|
 (44557 16
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (15540 8768 (:REWRITE DEFAULT-PLUS-2))
 (11240 8768 (:REWRITE DEFAULT-PLUS-1))
 (3810 3810
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3810 3810 (:REWRITE NORMALIZE-ADDENDS))
 (2752 88
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1504 1504
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1504 1504 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1504 1504 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1504 1504
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (620
   620
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (620
  620
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (620
     620
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (620 620
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (292
  292
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (292
  292
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (200 88 (:REWRITE DEFAULT-LESS-THAN-1))
 (120 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (100 44
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (88 88 (:REWRITE THE-FLOOR-BELOW))
 (88 88 (:REWRITE THE-FLOOR-ABOVE))
 (88 88
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (88 88
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (88 88 (:REWRITE DEFAULT-LESS-THAN-2))
 (44 44 (:REWRITE SIMPLIFY-SUMS-<))
 (44 44
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (44 44 (:REWRITE INTEGERP-<-CONSTANT))
 (44 44 (:REWRITE CONSTANT-<-INTEGERP))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< c (- x))|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (44 44
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (44 44 (:REWRITE |(< (/ x) (/ y))|))
 (44 44 (:REWRITE |(< (- x) c)|))
 (44 44 (:REWRITE |(< (- x) (- y))|))
 (44 44 (:REWRITE |(< (+ c/d x) y)|))
 (44 4 (:REWRITE DISJOINT-5-ITEMS))
 (12 12
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|)))
(|(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|
 (45409 17
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (15726 8827 (:REWRITE DEFAULT-PLUS-2))
 (11317 8827 (:REWRITE DEFAULT-PLUS-1))
 (3842 3842
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3842 3842 (:REWRITE NORMALIZE-ADDENDS))
 (3118 98
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1522 1522
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1522 1522 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1522 1522 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1522 1522
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (626
   626
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (626
  626
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (626 626
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (626
     626
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (626 626
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (626 626
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (495 1
      (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (292
  292
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (292
  292
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (230 98 (:REWRITE DEFAULT-LESS-THAN-1))
 (139 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (113 49
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (98 98 (:REWRITE THE-FLOOR-BELOW))
 (98 98 (:REWRITE THE-FLOOR-ABOVE))
 (98 98
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (98 98
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (98 98 (:REWRITE DEFAULT-LESS-THAN-2))
 (49 49 (:REWRITE SIMPLIFY-SUMS-<))
 (49 49
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (49 49 (:REWRITE |(< (+ c/d x) y)|))
 (44 4 (:REWRITE DISJOINT-5-ITEMS))
 (19 19
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (2 1
    (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(ANCESTORS-CHECK-DISJOINTP-HACK-2
     (558 66 (:DEFINITION LEN))
     (527 76
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (457 455 (:REWRITE DEFAULT-CDR))
     (439 1 (:DEFINITION VAR-FN-COUNT-1))
     (430 86 (:REWRITE ACL2-NUMBERP-X))
     (411 1 (:DEFINITION FN-COUNT-EVG-REC))
     (376 76 (:REWRITE O-P-O-INFP-CAR))
     (299 298 (:REWRITE DEFAULT-CAR))
     (183 76
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (176 44 (:REWRITE RATIONALP-X))
     (175 4 (:DEFINITION MIN-FIXNUM))
     (151 80 (:REWRITE DEFAULT-PLUS-2))
     (148 76 (:REWRITE O-P-DEF-O-FINP-1))
     (144 16 (:DEFINITION SYMBOL-LISTP))
     (124 76 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (81 80 (:REWRITE DEFAULT-PLUS-1))
     (78 72 (:REWRITE NORMALIZE-ADDENDS))
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
     (72 72 (:TYPE-PRESCRIPTION O-FINP))
     (71 71
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (66 66 (:REWRITE REDUCE-INTEGERP-+))
     (66 66 (:REWRITE INTEGERP-MINUS-X))
     (66 66 (:META META-INTEGERP-CORRECT))
     (61 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (44 44 (:REWRITE REDUCE-RATIONALP-+))
     (44 44 (:REWRITE REDUCE-RATIONALP-*))
     (44 44 (:REWRITE RATIONALP-MINUS-X))
     (44 44 (:META META-RATIONALP-CORRECT))
     (37 37
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (22 22
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (18 18 (:REWRITE DEFAULT-COERCE-2))
     (18 18 (:REWRITE DEFAULT-COERCE-1))
     (16 16 (:REWRITE |(equal x (if a b c))|))
     (16 16 (:REWRITE |(equal (if a b c) x)|))
     (14 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (12 10 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (10 1 (:REWRITE |(+ y (+ x z))|))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (8 5 (:REWRITE |(+ 0 x)|))
     (5 1 (:REWRITE |(+ y x)|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (4 2 (:REWRITE DEFAULT-TIMES-2))
     (2 2
        (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
     (2 2
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (2 2 (:REWRITE DEFAULT-TIMES-1))
     (2 2 (:DEFINITION FIX))
     (2 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
     (1 1 (:REWRITE DEFAULT-REALPART))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE DEFAULT-MINUS))
     (1 1 (:REWRITE DEFAULT-IMAGPART))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(+ x (- x))|)))
(ANCESTORS-CHECK-DISJOINTP-HACK-CONSTRAINT-2
     (39237 21 (:DEFINITION ANCESTORS-CHECK1))
     (20447 1384 (:REWRITE DEFAULT-LESS-THAN-2))
     (16440 40 (:DEFINITION FN-COUNT-EVG-REC))
     (16154 42
            (:DEFINITION EARLIER-ANCESTOR-BIGGERP))
     (10537 1617 (:REWRITE ACL2-NUMBERP-X))
     (10020 1139 (:REWRITE DEFAULT-LESS-THAN-1))
     (7000 160 (:DEFINITION MIN-FIXNUM))
     (4620 1131 (:REWRITE RATIONALP-X))
     (3523 544
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3044 1004
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2520 63 (:DEFINITION INTERSECTP-EQUAL))
     (2284 2051 (:REWRITE DEFAULT-CDR))
     (1967 388 (:REWRITE O-P-O-INFP-CAR))
     (1621 1395 (:REWRITE DEFAULT-CAR))
     (1384 1384 (:REWRITE THE-FLOOR-BELOW))
     (1384 1384 (:REWRITE THE-FLOOR-ABOVE))
     (1360 1360 (:TYPE-PRESCRIPTION LEN))
     (1171 1171 (:REWRITE REDUCE-INTEGERP-+))
     (1171 1171 (:REWRITE INTEGERP-MINUS-X))
     (1171 1171 (:META META-INTEGERP-CORRECT))
     (1164 1004
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1131 1131 (:REWRITE REDUCE-RATIONALP-+))
     (1131 1131 (:REWRITE REDUCE-RATIONALP-*))
     (1131 1131 (:REWRITE RATIONALP-MINUS-X))
     (1131 1131 (:META META-RATIONALP-CORRECT))
     (1004 1004
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1004 1004
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1004 1004
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1004 1004
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1004 1004
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1004 1004 (:REWRITE INTEGERP-<-CONSTANT))
     (1004 1004 (:REWRITE CONSTANT-<-INTEGERP))
     (1004 1004
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1004 1004
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1004 1004
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1004 1004
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1004 1004 (:REWRITE |(< c (- x))|))
     (1004 1004
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1004 1004
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1004 1004
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1004 1004
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1004 1004 (:REWRITE |(< (/ x) (/ y))|))
     (1004 1004 (:REWRITE |(< (- x) c)|))
     (1004 1004 (:REWRITE |(< (- x) (- y))|))
     (964 964 (:REWRITE SIMPLIFY-SUMS-<))
     (920 640 (:REWRITE DEFAULT-PLUS-2))
     (875 544
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (845 367 (:REWRITE O-P-DEF-O-FINP-1))
     (800 80 (:DEFINITION LENGTH))
     (739 544 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (680 640 (:REWRITE DEFAULT-PLUS-1))
     (560 320 (:REWRITE NORMALIZE-ADDENDS))
     (560 80 (:DEFINITION LEN))
     (544 544
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (544 544
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (544 544
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (544 544 (:REWRITE |(equal c (/ x))|))
     (544 544 (:REWRITE |(equal c (- x))|))
     (544 544 (:REWRITE |(equal (/ x) c)|))
     (544 544 (:REWRITE |(equal (/ x) (/ y))|))
     (544 544 (:REWRITE |(equal (- x) c)|))
     (544 544 (:REWRITE |(equal (- x) (- y))|))
     (478 478 (:TYPE-PRESCRIPTION O-FINP))
     (400 40 (:REWRITE |(+ y (+ x z))|))
     (320 200 (:REWRITE |(+ 0 x)|))
     (280 280
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (255 255
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (255 255
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (255 255 (:REWRITE |(< (/ x) 0)|))
     (255 255 (:REWRITE |(< (* x y) 0)|))
     (200 40 (:REWRITE |(+ y x)|))
     (160 160 (:REWRITE |(< y (+ (- c) x))|))
     (160 160 (:REWRITE |(< x (+ c/d y))|))
     (160 80 (:REWRITE DEFAULT-TIMES-2))
     (118 118
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (118 118
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (118 118 (:REWRITE |(< 0 (/ x))|))
     (118 118 (:REWRITE |(< 0 (* x y))|))
     (80 80
         (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
     (80 80
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (80 80 (:REWRITE DEFAULT-TIMES-1))
     (80 80 (:REWRITE DEFAULT-COERCE-2))
     (80 80 (:REWRITE DEFAULT-COERCE-1))
     (80 80 (:DEFINITION FIX))
     (80 40 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (63 63 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (63 63
         (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
     (48 6 (:DEFINITION STRIP-ANCESTOR-LITERALS))
     (42 42
         (:TYPE-PRESCRIPTION EARLIER-ANCESTOR-BIGGERP))
     (40 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (40 40 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (40 40
         (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (40 40 (:REWRITE DEFAULT-SYMBOL-NAME))
     (40 40 (:REWRITE DEFAULT-REALPART))
     (40 40
         (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (40 40
         (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (40 40 (:REWRITE DEFAULT-MINUS))
     (40 40 (:REWRITE DEFAULT-IMAGPART))
     (40 40 (:REWRITE |(< (+ c/d x) y)|))
     (40 40 (:REWRITE |(< (+ (- c) x) y)|))
     (40 40 (:REWRITE |(+ x (- x))|)))
(|(r32 addr (init_pdts-modify-outer-loop-1 i s))|
 (53031 17
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (22349 12599 (:REWRITE DEFAULT-PLUS-2))
 (16001 12599 (:REWRITE DEFAULT-PLUS-1))
 (6019 154
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5620 5620
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5620 5620 (:REWRITE NORMALIZE-ADDENDS))
 (2377 2377
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2377 2377 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2377 2377 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2377 2377
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (883
   883
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (883
  883
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (883 883
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (883
     883
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (883 883
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (883 883
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (872 1
      (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (650
  650
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (650
  650
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (334 154 (:REWRITE DEFAULT-LESS-THAN-1))
 (215 77 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (154 154 (:REWRITE THE-FLOOR-BELOW))
 (154 154 (:REWRITE THE-FLOOR-ABOVE))
 (154 154
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (154 154
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (154 154 (:REWRITE DEFAULT-LESS-THAN-2))
 (147 77
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (84 4 (:REWRITE DISJOINT-6-ITEMS))
 (77 77 (:REWRITE SIMPLIFY-SUMS-<))
 (77 77
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (77 77 (:REWRITE INTEGERP-<-CONSTANT))
 (77 77 (:REWRITE CONSTANT-<-INTEGERP))
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
 (77 77 (:REWRITE |(< (- x) c)|))
 (77 77 (:REWRITE |(< (- x) (- y))|))
 (77 77 (:REWRITE |(< (+ c/d x) y)|))
 (37 37
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 1
    (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|)))
(|(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 1|
 (507809 171
         (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (353496 202184 (:REWRITE DEFAULT-PLUS-2))
 (263954 202184 (:REWRITE DEFAULT-PLUS-1))
 (127942 156
         (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (91171 87427 (:REWRITE NORMALIZE-ADDENDS))
 (87115 87115
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (38020 1149
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (31716 31716
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (31716 31716
        (:REWRITE INIT_PDTS-LOADED-THM-32))
 (31716 31716
        (:REWRITE INIT_PDPT-LOADED-THM-32))
 (31716 31716
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (30438
  8208
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (26496 636 (:REWRITE SIMPLIFY-SUMS-<))
 (25416
  8208
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (20007
   20007
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20007
  20007
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20007
      20007
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20007
     20007
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20007 20007
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20007 20007
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (13576 24
        (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (12177 1386
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2840 812 (:REWRITE CONSTANT-<-INTEGERP))
 (2762 734 (:REWRITE INTEGERP-<-CONSTANT))
 (2497 2497
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2497 2497
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2276 1386 (:REWRITE DEFAULT-LESS-THAN-1))
 (1872 156 (:REWRITE |(* y (* x z))|))
 (1698 1386 (:REWRITE DEFAULT-LESS-THAN-2))
 (1658 636
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1480 636
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1404 468 (:DEFINITION FIX))
 (1386 1386 (:REWRITE THE-FLOOR-BELOW))
 (1386 1386 (:REWRITE THE-FLOOR-ABOVE))
 (1318 694 (:REWRITE DEFAULT-TIMES-2))
 (1149 1149
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (936 312 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (812 812
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (812 812
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (812 812
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (812 812
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (812 812 (:REWRITE |(< c (- x))|))
 (812 812
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (812 812
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (812 812
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (812 812
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (812 812 (:REWRITE |(< (/ x) (/ y))|))
 (812 812 (:REWRITE |(< (- x) c)|))
 (812 812 (:REWRITE |(< (- x) (- y))|))
 (694 694 (:REWRITE DEFAULT-TIMES-1))
 (656 656
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (624 312 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (507 507 (:REWRITE |(< (+ c/d x) y)|))
 (480 480 (:REWRITE FOLD-CONSTS-IN-+))
 (402 81 (:REWRITE |(* c (* d x))|))
 (390 390 (:REWRITE |(* (- x) y)|))
 (312 312 (:REWRITE |(+ x (- x))|))
 (298 298
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (237 237 (:TYPE-PRESCRIPTION ABS))
 (230 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (230 22
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (230 22
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (176 16 (:REWRITE DISJOINT-6-ITEMS))
 (170 170 (:REWRITE |(< (+ (- c) x) y)|))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (156 156 (:REWRITE |(* a (/ a) b)|))
 (122 122
      (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (116 116 (:REWRITE |(< (* x y) 0)|))
 (99 99 (:REWRITE DEFAULT-LOGIOR-2))
 (99 99 (:REWRITE DEFAULT-LOGIOR-1))
 (86 86 (:REWRITE |(< y (+ (- c) x))|))
 (86 86 (:REWRITE |(< x (+ c/d y))|))
 (78 78
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (78 78
     (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (26 26 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (16 8
     (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< 0 (/ x))|))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3 (:REWRITE |(* 1 x)|)))
(|(r32 addr (init_pdts-modify-outer-loop-1 i s)) --- written to 2|
 (507809 171
         (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (359734 204694 (:REWRITE DEFAULT-PLUS-2))
 (267808 204694 (:REWRITE DEFAULT-PLUS-1))
 (134054 156
         (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (92105 88361 (:REWRITE NORMALIZE-ADDENDS))
 (88049 88049
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (57511 1230
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (33714
  8208
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (31732 31732
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (31732 31732
        (:REWRITE INIT_PDTS-LOADED-THM-32))
 (31732 31732
        (:REWRITE INIT_PDPT-LOADED-THM-32))
 (31732 31732
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (31068
  8208
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (27535 625 (:REWRITE SIMPLIFY-SUMS-<))
 (20007
   20007
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20007
  20007
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20007
      20007
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20007
     20007
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20007 20007
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20007 20007
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (13576 24
        (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (13008 1464
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3120 234 (:REWRITE |(* y (* x z))|))
 (2829 801 (:REWRITE CONSTANT-<-INTEGERP))
 (2751 723 (:REWRITE INTEGERP-<-CONSTANT))
 (2538 1464 (:REWRITE DEFAULT-LESS-THAN-1))
 (1932 1464 (:REWRITE DEFAULT-LESS-THAN-2))
 (1748 812 (:REWRITE DEFAULT-TIMES-2))
 (1743 625
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1565 625
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1464 1464 (:REWRITE THE-FLOOR-BELOW))
 (1464 1464 (:REWRITE THE-FLOOR-ABOVE))
 (1404 468 (:DEFINITION FIX))
 (1354 1354 (:REWRITE FOLD-CONSTS-IN-+))
 (1230 1230
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (936 312 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (812 812 (:REWRITE DEFAULT-TIMES-1))
 (801 801
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (801 801
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (801 801
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (801 801
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (801 801 (:REWRITE |(< c (- x))|))
 (801 801
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (801 801
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (801 801
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (801 801
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (801 801 (:REWRITE |(< (/ x) (/ y))|))
 (801 801 (:REWRITE |(< (- x) c)|))
 (801 801 (:REWRITE |(< (- x) (- y))|))
 (645 645
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (624 312 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (599 599 (:REWRITE |(< (+ c/d x) y)|))
 (468 468 (:REWRITE |(* (- x) y)|))
 (390 78 (:REWRITE |(* c (* d x))|))
 (344 344
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (312 312 (:REWRITE |(+ x (- x))|))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (234 234 (:TYPE-PRESCRIPTION ABS))
 (176 16 (:REWRITE DISJOINT-6-ITEMS))
 (170 170 (:REWRITE |(< (+ (- c) x) y)|))
 (156 156 (:REWRITE |(< x (+ c/d y))|))
 (156 156 (:REWRITE |(* a (/ a) b)|))
 (132 22
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (132 22
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (132 22 (:REWRITE O-INFP->NEQ-0))
 (122 122
      (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (116 116 (:REWRITE |(< (* x y) 0)|))
 (78 78 (:REWRITE |(< y (+ (- c) x))|))
 (78 78
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (78 78
     (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (22 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (22 22
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (22 22
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (22 22 (:REWRITE |(equal c (/ x))|))
 (22 22 (:REWRITE |(equal c (- x))|))
 (22 22 (:REWRITE |(equal (/ x) c)|))
 (22 22 (:REWRITE |(equal (/ x) (/ y))|))
 (22 22 (:REWRITE |(equal (- x) c)|))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (16 8
     (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|)))
(|(good-state-p (init_pdts-modify-outer-loop-1 i s))|
 (74953 27
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (34879 18879 (:REWRITE DEFAULT-PLUS-2))
 (23197 18879 (:REWRITE DEFAULT-PLUS-1))
 (19771 274
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8694 8694
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8694 8694 (:REWRITE NORMALIZE-ADDENDS))
 (7932 24
       (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (7202 142
       (:REWRITE |(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|))
 (4537 4537
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (4537 4537 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (4537 4537 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (4537 4537
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (3516 24
       (:REWRITE |(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|))
 (2675
   2675
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2675
  2675
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2675
      2675
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2675
     2675
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2675 2675
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2675 2675
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (893
  893
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (893
  893
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (746 274 (:REWRITE DEFAULT-LESS-THAN-1))
 (661 1
      (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (429 137
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (369 137
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (274 274 (:REWRITE THE-FLOOR-BELOW))
 (274 274 (:REWRITE THE-FLOOR-ABOVE))
 (274 274
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (274 274
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (274 274 (:REWRITE DEFAULT-LESS-THAN-2))
 (137 137 (:REWRITE SIMPLIFY-SUMS-<))
 (137 137
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (137 137 (:REWRITE INTEGERP-<-CONSTANT))
 (137 137 (:REWRITE CONSTANT-<-INTEGERP))
 (137 137
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (137 137
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (137 137
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (137 137
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (137 137 (:REWRITE |(< c (- x))|))
 (137 137
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (137 137
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (137 137
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (137 137
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (137 137 (:REWRITE |(< (/ x) (/ y))|))
 (137 137 (:REWRITE |(< (- x) c)|))
 (137 137 (:REWRITE |(< (- x) (- y))|))
 (137 137 (:REWRITE |(< (+ c/d x) y)|))
 (88 8 (:REWRITE DISJOINT-7-ITEMS))
 (38 38
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16 (:REWRITE |(< (* x y) 0)|)))
(|(init_pdts-modify-outer-loop-1 i (w32 addr val s))|
 (118732 48
         (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (37245 20167 (:REWRITE DEFAULT-PLUS-2))
 (25081 20167 (:REWRITE DEFAULT-PLUS-1))
 (20199 288
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (9209 9209
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9209 9209 (:REWRITE NORMALIZE-ADDENDS))
 (8088 56
       (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (7202 142
       (:REWRITE |(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|))
 (4641 4641
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (4641 4641 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (4641 4641 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (4641 4641
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (3516 24
       (:REWRITE |(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|))
 (2783
   2783
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2783
  2783
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2783
      2783
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2783
     2783
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2783 2783
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2783 2783
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (873
  873
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (873
  873
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (762 288 (:REWRITE DEFAULT-LESS-THAN-1))
 (643 1
      (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (545 19 (:REWRITE DISJOINT-5-ITEMS))
 (439 145
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (379 145
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (335 21
      (:REWRITE |(good-32-address-p addr st)|))
 (302 8
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- not paging|))
 (288 288 (:REWRITE THE-FLOOR-BELOW))
 (288 288 (:REWRITE THE-FLOOR-ABOVE))
 (288 288
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (288 288
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (288 288 (:REWRITE DEFAULT-LESS-THAN-2))
 (145 145 (:REWRITE SIMPLIFY-SUMS-<))
 (145 145
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (145 145 (:REWRITE INTEGERP-<-CONSTANT))
 (145 145 (:REWRITE CONSTANT-<-INTEGERP))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< c (- x))|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (145 145
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (145 145 (:REWRITE |(< (/ x) (/ y))|))
 (145 145 (:REWRITE |(< (- x) c)|))
 (145 145 (:REWRITE |(< (- x) (- y))|))
 (143 143 (:REWRITE |(< (+ c/d x) y)|))
 (110 8
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (88 8 (:REWRITE DISJOINT-7-ITEMS))
 (81 9 (:REWRITE |(y86-p (w32 addr val s))|))
 (70 54
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (44 12 (:REWRITE ACL2-NUMBERP-X))
 (42 6
     (:REWRITE |(memoryp (g :mem (w32 addr val st)))|))
 (40 4
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (28 28
     (:REWRITE |(g field (w32 addr val st))|))
 (27 27 (:REWRITE REDUCE-INTEGERP-+))
 (27 27 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:META META-INTEGERP-CORRECT))
 (25 25
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (22 2 (:REWRITE DISJOINT-3-ITEMS))
 (22 2
     (:REWRITE |(n32p (r32 addr (g :mem st)))|))
 (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (16 4 (:REWRITE RATIONALP-X))
 (8 8 (:REWRITE |(va-to-pa addr st)|))
 (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 4
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|)))
(INIT_PDTS-MODIFY-INNER-LOOP)
(INIT_PDTS-MODIFY-OUTER-LOOP)
(INIT_PDTS-MODIFY)
(|(paging-p (init_pdts-modify s))|
 (228 44 (:REWRITE ACL2-NUMBERP-X))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (139 1
      (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (138 1
      (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (131 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 23 (:REWRITE RATIONALP-X))
 (64 43 (:REWRITE DEFAULT-PLUS-1))
 (42 18
     (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE NORMALIZE-ADDENDS))
 (27 5 (:REWRITE |(+ c (+ d x))|))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (23 23 (:META META-INTEGERP-CORRECT))
 (18 18 (:TYPE-PRESCRIPTION R32))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (7 7
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (7 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 4
    (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(+ 0 x)|))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:TYPE-PRESCRIPTION Y86-P))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(va-to-pa addr (init_pdts-modify s))|
 (228 44 (:REWRITE ACL2-NUMBERP-X))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (139 1
      (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (138 1
      (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (131 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 23 (:REWRITE RATIONALP-X))
 (64 43 (:REWRITE DEFAULT-PLUS-1))
 (42 18
     (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
 (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
 (29 29
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE NORMALIZE-ADDENDS))
 (27 5 (:REWRITE |(+ c (+ d x))|))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (23 23 (:META META-INTEGERP-CORRECT))
 (18 18 (:TYPE-PRESCRIPTION R32))
 (15 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 9
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (7 7
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (7 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 4
    (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(+ 0 x)|))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:TYPE-PRESCRIPTION Y86-P))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(good-32-address-p addr (init_pdts-modify s))|
 (228 44 (:REWRITE ACL2-NUMBERP-X))
 (211 15
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (188 7 (:REWRITE |(n32p x)|))
 (162 4 (:REWRITE |(< (if a b c) x)|))
 (139 1
      (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (138 1
      (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 23 (:REWRITE RATIONALP-X))
 (74 53 (:REWRITE DEFAULT-PLUS-1))
 (42 18
     (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
 (37 2
     (:REWRITE |(good-32-address-p addr st)|))
 (35 7 (:REWRITE |(+ c (+ d x))|))
 (33 33
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (33 33 (:REWRITE NORMALIZE-ADDENDS))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (23 23 (:REWRITE REDUCE-RATIONALP-+))
 (23 23 (:REWRITE REDUCE-RATIONALP-*))
 (23 23 (:REWRITE RATIONALP-MINUS-X))
 (23 23 (:META META-RATIONALP-CORRECT))
 (22 2 (:REWRITE |(+ y (+ x z))|))
 (21 19 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE THE-FLOOR-BELOW))
 (19 19 (:REWRITE THE-FLOOR-ABOVE))
 (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
 (18 18 (:TYPE-PRESCRIPTION R32))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (11 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE SIMPLIFY-SUMS-<))
 (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (9 9 (:REWRITE INTEGERP-<-CONSTANT))
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
 (9 9 (:REWRITE |(< (/ x) (/ y))|))
 (9 9 (:REWRITE |(< (- x) c)|))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (7 7
    (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (7 7 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (7 7
    (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(+ 0 x)|))
 (6 4
    (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (6 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 2
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:TYPE-PRESCRIPTION Y86-P))
 (2 2 (:TYPE-PRESCRIPTION N32P))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(y86-p (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (2701 1980 (:REWRITE DEFAULT-PLUS-2))
 (2371 1980 (:REWRITE DEFAULT-PLUS-1))
 (813 813
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (813 813 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (153 153
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (153 153 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (153 153 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (153 153
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (111
  111
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (111
  111
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (68
   68
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (68
  68
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (68 68
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(memoryp (g :mem (init_pdts-modify s)))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (2701 1980 (:REWRITE DEFAULT-PLUS-2))
 (2371 1980 (:REWRITE DEFAULT-PLUS-1))
 (813 813
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (813 813 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (153 153
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (153 153 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (153 153 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (153 153
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (111
  111
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (111
  111
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (55
   55
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (55
  55
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (55 55
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12
     (:REWRITE |(g field (w32 addr val st))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(good-state-p (init_pdts-modify s))|
 (58145 5
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (58140 5
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (57830 20
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (40849 36143 (:REWRITE DEFAULT-PLUS-2))
 (37854 36143 (:REWRITE DEFAULT-PLUS-1))
 (32920 20 (:REWRITE DISJOINT-6-ITEMS))
 (17180 20 (:REWRITE DISJOINT-5-ITEMS))
 (15049 15049
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (15049 15049 (:REWRITE NORMALIZE-ADDENDS))
 (2795 136
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2089
  2089
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2089
  2089
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1622
   1622
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1622
  1622
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1622
      1622
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1622
     1622
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1622 1622
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1622 1622
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1506 1506
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1506 1506 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1506 1506 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1506 1506
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (701 15 (:REWRITE |(n32-to-i32 x) --- 2|))
 (687 15 (:REWRITE |(n32-to-i32 x) --- 1|))
 (234 136 (:REWRITE DEFAULT-LESS-THAN-1))
 (141 136 (:REWRITE DEFAULT-LESS-THAN-2))
 (136 136 (:REWRITE THE-FLOOR-BELOW))
 (136 136 (:REWRITE THE-FLOOR-ABOVE))
 (136 136
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (136 136
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (131 73
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (131 73 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (90 73
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (83 73 (:REWRITE SIMPLIFY-SUMS-<))
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
 (68 68 (:REWRITE |(< (+ c/d x) y)|))
 (31 29 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (26 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (26 15
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (15 15 (:REWRITE |(equal c (/ x))|))
 (15 15 (:REWRITE |(equal c (- x))|))
 (15 15 (:REWRITE |(equal (/ x) c)|))
 (15 15 (:REWRITE |(equal (/ x) (/ y))|))
 (15 15 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE O-INFP->NEQ-0)))
(|(g :cr0 (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (9718 101
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (7261
  845
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (3504 224 (:REWRITE |(+ (+ x y) z)|))
 (3436 4 (:REWRITE DISJOINT-5-ITEMS))
 (2377 1743 (:REWRITE DEFAULT-PLUS-2))
 (2086 1743 (:REWRITE DEFAULT-PLUS-1))
 (933 933 (:TYPE-PRESCRIPTION SUBRANGEP))
 (932 732 (:REWRITE NTH-ADD1))
 (828 35 (:REWRITE |(n32p x)|))
 (819 144 (:REWRITE |(+ c (+ d x))|))
 (717 717
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (717 717 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (308 183 (:REWRITE |(+ 0 x)|))
 (290 290 (:REWRITE |(subrangep x x)|))
 (200 200 (:TYPE-PRESCRIPTION RANGE))
 (200 200 (:REWRITE NTH-0-CONS))
 (138 138
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (138 138
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (38
   38
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (38
  38
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :eip (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (9718 101
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (7261
  845
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (3504 224 (:REWRITE |(+ (+ x y) z)|))
 (3436 4 (:REWRITE DISJOINT-5-ITEMS))
 (2377 1743 (:REWRITE DEFAULT-PLUS-2))
 (2086 1743 (:REWRITE DEFAULT-PLUS-1))
 (933 933 (:TYPE-PRESCRIPTION SUBRANGEP))
 (932 732 (:REWRITE NTH-ADD1))
 (828 35 (:REWRITE |(n32p x)|))
 (819 144 (:REWRITE |(+ c (+ d x))|))
 (717 717
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (717 717 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (308 183 (:REWRITE |(+ 0 x)|))
 (290 290 (:REWRITE |(subrangep x x)|))
 (200 200 (:TYPE-PRESCRIPTION RANGE))
 (200 200 (:REWRITE NTH-0-CONS))
 (139 139
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (139 139 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (139 139 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (139 139
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (38
   38
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (38
  38
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :ebp (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (9718 101
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (7261
  845
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (3504 224 (:REWRITE |(+ (+ x y) z)|))
 (3436 4 (:REWRITE DISJOINT-5-ITEMS))
 (2377 1743 (:REWRITE DEFAULT-PLUS-2))
 (2086 1743 (:REWRITE DEFAULT-PLUS-1))
 (933 933 (:TYPE-PRESCRIPTION SUBRANGEP))
 (932 732 (:REWRITE NTH-ADD1))
 (828 35 (:REWRITE |(n32p x)|))
 (819 144 (:REWRITE |(+ c (+ d x))|))
 (717 717
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (717 717 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (308 183 (:REWRITE |(+ 0 x)|))
 (290 290 (:REWRITE |(subrangep x x)|))
 (200 200 (:TYPE-PRESCRIPTION RANGE))
 (200 200 (:REWRITE NTH-0-CONS))
 (138 138
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (138 138
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (38
   38
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (38
  38
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(g :esp (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (11566 4
        (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (9718 101
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (7261
  845
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (6584 4 (:REWRITE DISJOINT-6-ITEMS))
 (3504 224 (:REWRITE |(+ (+ x y) z)|))
 (3436 4 (:REWRITE DISJOINT-5-ITEMS))
 (2378 1744 (:REWRITE DEFAULT-PLUS-2))
 (2087 1744 (:REWRITE DEFAULT-PLUS-1))
 (933 933 (:TYPE-PRESCRIPTION SUBRANGEP))
 (932 732 (:REWRITE NTH-ADD1))
 (828 35 (:REWRITE |(n32p x)|))
 (819 144 (:REWRITE |(+ c (+ d x))|))
 (718 718
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (718 718 (:REWRITE NORMALIZE-ADDENDS))
 (507 24
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (342 22 (:REWRITE |(+ y (+ x z))|))
 (308 183 (:REWRITE |(+ 0 x)|))
 (290 290 (:REWRITE |(subrangep x x)|))
 (200 200 (:TYPE-PRESCRIPTION RANGE))
 (200 200 (:REWRITE NTH-0-CONS))
 (138 138
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (138 138 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (138 138
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (101
  101
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (44 24 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (38
   38
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (38
  38
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (25 24 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 24
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (24 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13 (:REWRITE INTEGERP-<-CONSTANT))
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
 (13 13 (:REWRITE |(< (/ x) (/ y))|))
 (13 13 (:REWRITE |(< (- x) c)|))
 (13 13 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(|(r32 addr (init_pdts-modify s))|
 (11629 1
        (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (11628 1
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (7067 5281 (:REWRITE DEFAULT-PLUS-2))
 (6260 5281 (:REWRITE DEFAULT-PLUS-1))
 (2131 2131
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2131 2131 (:REWRITE NORMALIZE-ADDENDS))
 (546 26
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (379 379
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (379 379 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (379 379 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (379 379
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (259
  259
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (259
  259
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (194
   194
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (194
  194
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (194 194
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (194
     194
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (194 194
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (194 194
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (66 66
     (:REWRITE |(g field (w32 addr val st))|))
 (46 26 (:REWRITE DEFAULT-LESS-THAN-1))
 (27 26 (:REWRITE DEFAULT-LESS-THAN-2))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (26 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (26 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (17 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 14 (:REWRITE SIMPLIFY-SUMS-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (14 14
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< c (- x))|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14 14
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14 14 (:REWRITE |(< (/ x) (/ y))|))
 (14 14 (:REWRITE |(< (- x) c)|))
 (14 14 (:REWRITE |(< (- x) (- y))|))
 (13 13 (:REWRITE |(< (+ c/d x) y)|))
 (11 1 (:REWRITE DISJOINT-7-ITEMS))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
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
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE O-INFP->NEQ-0))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(|(r32 addr (init_pdts-modify s)) --- written to 1|
 (81406 7
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (54359 39478 (:REWRITE DEFAULT-PLUS-2))
 (48116 39478 (:REWRITE DEFAULT-PLUS-1))
 (16023 15927 (:REWRITE NORMALIZE-ADDENDS))
 (15919 15919
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2575
  2005
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2544 2544
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2544 2544 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2544 2544 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2544 2544
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2437
  2005
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2246 120
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1183
   1183
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1183
  1183
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1183
      1183
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1183
     1183
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1183 1183
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1183 1183
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (736 68 (:REWRITE SIMPLIFY-SUMS-<))
 (404 12 (:REWRITE |(n32-to-i32 x) --- 2|))
 (400 126
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (396 12 (:REWRITE |(n32-to-i32 x) --- 1|))
 (391 391
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (391 391
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (264 264
      (:REWRITE |(g field (w32 addr val st))|))
 (210 126 (:REWRITE DEFAULT-LESS-THAN-1))
 (153 153 (:REWRITE FOLD-CONSTS-IN-+))
 (138 126 (:REWRITE DEFAULT-LESS-THAN-2))
 (128 68
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (128 68 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (126 126 (:REWRITE THE-FLOOR-BELOW))
 (126 126 (:REWRITE THE-FLOOR-ABOVE))
 (126 74 (:REWRITE CONSTANT-<-INTEGERP))
 (124 72 (:REWRITE INTEGERP-<-CONSTANT))
 (120 120
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 70
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (54 54 (:REWRITE |(< (+ c/d x) y)|))
 (48 4 (:REWRITE |(* y (* x z))|))
 (45 29 (:REWRITE DEFAULT-TIMES-2))
 (44 4 (:REWRITE DISJOINT-7-ITEMS))
 (36 12 (:DEFINITION FIX))
 (35 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (35 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29 29 (:REWRITE DEFAULT-TIMES-1))
 (24 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (15 15 (:REWRITE |(< (* x y) 0)|))
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
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (12 12
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (10 10 (:REWRITE |(* (- x) y)|))
 (10 2 (:REWRITE |(* c (* d x))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE DEFAULT-LOGIOR-2))
 (8 8 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(+ x (- x))|))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE O-INFP->NEQ-0))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (2 2 (:REWRITE |(< x (+ c/d y))|)))
(|(r32 addr (init_pdts-modify s)) --- written to 2|
 (81406 7
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (55689 40052 (:REWRITE DEFAULT-PLUS-2))
 (49098 40052 (:REWRITE DEFAULT-PLUS-1))
 (16232 16136 (:REWRITE NORMALIZE-ADDENDS))
 (16128 16128
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2716 122
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2659
  2005
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2585
  2005
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (2544 2544
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2544 2544 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2544 2544 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2544 2544
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1183
   1183
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1183
  1183
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1183
      1183
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1183
     1183
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1183 1183
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1183 1183
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (766 68 (:REWRITE SIMPLIFY-SUMS-<))
 (424 128
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (404 12 (:REWRITE |(n32-to-i32 x) --- 2|))
 (396 12 (:REWRITE |(n32-to-i32 x) --- 1|))
 (366 366 (:REWRITE FOLD-CONSTS-IN-+))
 (264 264
      (:REWRITE |(g field (w32 addr val st))|))
 (216 128 (:REWRITE DEFAULT-LESS-THAN-1))
 (144 128 (:REWRITE DEFAULT-LESS-THAN-2))
 (132 68
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (132 68 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (128 128 (:REWRITE THE-FLOOR-BELOW))
 (128 128 (:REWRITE THE-FLOOR-ABOVE))
 (126 74 (:REWRITE CONSTANT-<-INTEGERP))
 (124 72 (:REWRITE INTEGERP-<-CONSTANT))
 (122 122
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (82 70
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (80 6 (:REWRITE |(* y (* x z))|))
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
 (56 56 (:REWRITE |(< (+ c/d x) y)|))
 (49 25 (:REWRITE DEFAULT-TIMES-2))
 (44 4 (:REWRITE DISJOINT-7-ITEMS))
 (36 12 (:DEFINITION FIX))
 (30 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (30 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 25 (:REWRITE DEFAULT-TIMES-1))
 (25 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (12 12
     (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (12 12 (:REWRITE |(* (- x) y)|))
 (10 5 (:REWRITE O-INFP->NEQ-0))
 (10 2 (:REWRITE |(* c (* d x))|))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(+ x (- x))|))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< 0 y)|)))
(INIT_PDTS-ASSERTION)
($$$INSUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$PRESUB-IMPLIES-INSUB)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-test|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-base|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-step|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-fn|
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1|
 (1
   1
   (:TYPE-PRESCRIPTION |$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-DEF|)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
($$$STEPS-TO-EXITPOINT-SUB-TAIL-DEF (4 4 (:REWRITE DEFAULT-CAR))
                                    (2 2 (:REWRITE DEFAULT-CDR)))
($$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF)
($$$STEPS-TO-EXITPOINT-SUB (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                           (2 2
                              (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR)))
($$$NEXT-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB-SUFF)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn| (4 4 (:REWRITE DEFAULT-<-2))
                                           (4 4 (:REWRITE DEFAULT-<-1))
                                           (1 1 (:REWRITE ZP-OPEN))
                                           (1 1 (:REWRITE DEFAULT-+-2))
                                           (1 1 (:REWRITE DEFAULT-+-1)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF)
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION
 (8297 1
       (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (8296 1
       (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (8252 4
       (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (4704 4 (:REWRITE DISJOINT-6-ITEMS))
 (4611
  971
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (2540 4 (:REWRITE DISJOINT-5-ITEMS))
 (1506 1124 (:REWRITE DEFAULT-+-2))
 (1355 1124 (:REWRITE DEFAULT-+-1))
 (883 245 (:REWRITE FOLD-CONSTS-IN-+))
 (157 157
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (157 157 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (157 157 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (157 157
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (122
  122
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (122
  122
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (30 16 (:REWRITE DEFAULT-<-1))
 (19 16 (:REWRITE DEFAULT-<-2))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (2 2
    (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (1 1 (:REWRITE O-INFP->NEQ-0)))
($$$ASSERTION-MAIN-IMPLIES-POST
 (18535 63
        (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (8587 220
       (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (8251 129
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (7208 4158 (:REWRITE DEFAULT-+-2))
 (5755 4158 (:REWRITE DEFAULT-+-1))
 (5464
  980
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (4704 4 (:REWRITE DISJOINT-6-ITEMS))
 (2540 4 (:REWRITE DISJOINT-5-ITEMS))
 (1956 12
       (:REWRITE |(r32 addr (init_pdts-modify-inner-loop-1 i j s))|))
 (1240 1240
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1240 1240 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1240 1240 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1240 1240
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1168 12 (:DEFINITION BINARY-LOGIOR))
 (1074 1074 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1010 786 (:REWRITE NTH-ADD1))
 (866 12 (:DEFINITION BINARY-LOGAND))
 (783 404 (:REWRITE DEFAULT-<-1))
 (676 12 (:DEFINITION FLOOR))
 (566 11
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (503 404 (:REWRITE DEFAULT-<-2))
 (487 22
      (:REWRITE |(good-32-address-p addr st)|))
 (451 14
      (:REWRITE
           |(good-32-address-p addr (init_pdts-modify-inner-loop-1 i j s))|))
 (368 23
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (339 339 (:REWRITE |(subrangep x x)|))
 (338 86 (:REWRITE |(n32-to-i32 x) --- 2|))
 (290 24 (:DEFINITION LOGNOT))
 (290 11
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (235 199 (:REWRITE DEFAULT-*-2))
 (226 16 (:REWRITE DISJOINT-7-ITEMS))
 (224 224 (:TYPE-PRESCRIPTION RANGE))
 (224 224 (:REWRITE NTH-0-CONS))
 (211 199 (:REWRITE DEFAULT-*-1))
 (190
  130
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (172
  130
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (170
   4
   (:REWRITE |(good-32-address-p addr (init_pdts-modify-outer-loop-1 i s))|))
 (158 158
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (149 71 (:REWRITE O-INFP->NEQ-0))
 (131 1 (:REWRITE DISJOINT-3-ITEMS))
 (114 114
      (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (96 96 (:TYPE-PRESCRIPTION BINARY-LOGAND))
 (96 72 (:REWRITE DEFAULT-UNARY-MINUS))
 (69 23 (:DEFINITION NFIX))
 (66 54
     (:REWRITE |(paging-p (w32 addr val st))|))
 (59 59
     (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (59 47 (:DEFINITION IFIX))
 (49 12
     (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (38 1
     (:REWRITE |(memoryp (g :mem (init_pdts-modify-inner-loop-1 i j s)))|))
 (33 1
     (:REWRITE |(y86-p (init_pdts-modify-inner-loop-1 i j s))|))
 (32 8 (:REWRITE ZP-OPEN))
 (22 11 (:REWRITE ZIP-OPEN))
 (20 10
     (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|))
 (15 8
     (:REWRITE |(paging-p (init_pdts-modify-inner-loop-1 i j s))|))
 (12 12 (:REWRITE DEFAULT-NUMERATOR))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (12 4
     (:REWRITE |(va-to-pa addr (init_pdts-modify-inner-loop-1 i j s))|))
 (12 4
     (:REWRITE |(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|))
 (7 7
    (:REWRITE |(G field (INIT_PDTS-MODIFY-INNER-LOOP-1 i j s))|))
 (2 2 (:REWRITE |(va-to-pa addr st)|)))
($$$ASSERTION-IMPLIES-CUTPOINT
 (3220 14
       (:DEFINITION INIT_PDTS-MODIFY-INNER-LOOP-1))
 (2075 979 (:REWRITE DEFAULT-+-2))
 (1820 7
       (:DEFINITION INIT_PDTS-MODIFY-OUTER-LOOP-1))
 (1393 979 (:REWRITE DEFAULT-+-1))
 (1205 38 (:REWRITE |(n32p x)|))
 (990 10 (:DEFINITION BINARY-LOGIOR))
 (738 10 (:DEFINITION BINARY-LOGAND))
 (578 10 (:DEFINITION FLOOR))
 (320 20
      (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (288 120 (:REWRITE DEFAULT-<-1))
 (263 6
      (:REWRITE
           |(good-32-address-p addr (init_pdts-modify-inner-loop-1 i j s))|))
 (259 259
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (259 259 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (259 259 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (259 259
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (252 3
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (242 20 (:DEFINITION LOGNOT))
 (235 6
      (:REWRITE |(good-32-address-p addr st)|))
 (201 167 (:REWRITE DEFAULT-*-2))
 (184 56
      (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (179 167 (:REWRITE DEFAULT-*-1))
 (170
   4
   (:REWRITE |(good-32-address-p addr (init_pdts-modify-outer-loop-1 i s))|))
 (165 120 (:REWRITE DEFAULT-<-2))
 (114 114
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (87 30 (:REWRITE O-INFP->NEQ-0))
 (81 61 (:REWRITE DEFAULT-UNARY-MINUS))
 (80 80 (:TYPE-PRESCRIPTION BINARY-LOGAND))
 (72 48
     (:REWRITE |(r32 addr (init_pdts-modify-outer-loop-1 i s))|))
 (60 20 (:DEFINITION NFIX))
 (50 50
     (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (50 40 (:DEFINITION IFIX))
 (41 10
     (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (32 32 (:TYPE-PRESCRIPTION Y86-P))
 (30 5 (:REWRITE DISJOINT-7-ITEMS))
 (28 28
     (:REWRITE |(G field (INIT_PDTS-MODIFY-outer-LOOP-1 i s))|))
 (24 6 (:REWRITE ZP-OPEN))
 (23 3
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (20 10 (:REWRITE ZIP-OPEN))
 (12 12
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (12 4
     (:REWRITE |(memoryp (g :mem (init_pdts-modify-outer-loop-1 i s)))|))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (11 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (8 4
    (:REWRITE |(paging-p (init_pdts-modify-outer-loop-1 i s))|))
 (6 6 (:TYPE-PRESCRIPTION N32P))
 (5 5
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4 4
    (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE)))
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
(SIMULATION-DEFAULT-HINT (5 5 (:TYPE-PRESCRIPTION LAST)))
(SIMULATE-MAIN
 (537243 22335
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (294890 229484 (:REWRITE DEFAULT-PLUS-1))
 (123834 123834
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (111580 22316 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (111580 22316 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (111580 22316
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (111580 22316
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (111062 111062
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (111062 111062
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (111062 111062
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (99118 7183 (:REWRITE INIT_PDPT-LOADED-THM-08))
 (99118 7183
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
 (44482 12609
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (36380 12609
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32880 13712
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (32149 13712
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28482 22345 (:REWRITE DEFAULT-LESS-THAN-2))
 (22774 22344
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22345 22345 (:REWRITE THE-FLOOR-BELOW))
 (22345 22345 (:REWRITE THE-FLOOR-ABOVE))
 (22335 22335
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22316 22316 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (22316 22316
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (22316 22316
        (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (22316 22316
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (22316 22316
        (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (20128 12901
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (19103 280 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (18480 1365 (:REWRITE |(* x (+ y z))|))
 (16458
   16458
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (16458
  16458
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (16458
      16458
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (16458
     16458
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (16458 16458
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16458 16458
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (16122 8097 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (15977 3512 (:REWRITE O-INFP->NEQ-0))
 (15958 9479 (:REWRITE DEFAULT-TIMES-2))
 (14040 13713
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (13713 13713 (:REWRITE INTEGERP-<-CONSTANT))
 (13713 13713 (:REWRITE CONSTANT-<-INTEGERP))
 (13713 13713
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (13713 13713
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (13713 13713
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (13713 13713
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (13713 13713 (:REWRITE |(< c (- x))|))
 (13713 13713
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (13713 13713
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (13713 13713
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (13713 13713 (:REWRITE |(< (/ x) (/ y))|))
 (13713 13713 (:REWRITE |(< (- x) c)|))
 (13713 13713 (:REWRITE |(< (- x) (- y))|))
 (13224 6542
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-08))
 (13107 280 (:REWRITE MOD-ZERO . 1))
 (12901 12901
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12789 312 (:LINEAR MOD-BOUNDS-3))
 (12672 3240 (:REWRITE ACL2-NUMBERP-X))
 (12609 12609
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12609 12609 (:REWRITE |(equal c (/ x))|))
 (12609 12609 (:REWRITE |(equal c (- x))|))
 (12609 12609 (:REWRITE |(equal (/ x) c)|))
 (12609 12609 (:REWRITE |(equal (/ x) (/ y))|))
 (12609 12609 (:REWRITE |(equal (- x) c)|))
 (12609 12609 (:REWRITE |(equal (- x) (- y))|))
 (12381 477 (:REWRITE DEFAULT-MOD-RATIO))
 (12198 328 (:REWRITE MOD-ZERO . 3))
 (11315 11315 (:REWRITE |(< (+ c/d x) y)|))
 (11194 1019 (:REWRITE DISJOINT-7-ITEMS))
 (10569 9479 (:REWRITE DEFAULT-TIMES-1))
 (8053 8053
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7937 6444
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6502 3627
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4716 1179 (:REWRITE RATIONALP-X))
 (3668 3668 (:REWRITE FOLD-CONSTS-IN-+))
 (3654 624 (:LINEAR MOD-BOUNDS-2))
 (3627 3627
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3627 3627
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3627 3627
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3512 3512
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3253 3253 (:REWRITE |(< x (+ c/d y))|))
 (2693 2693 (:REWRITE |(< (+ (- c) x) y)|))
 (2667 477 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2486 328 (:REWRITE MOD-X-Y-=-X . 4))
 (2204 328 (:REWRITE MOD-ZERO . 4))
 (2204 328 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (2126 316 (:REWRITE MOD-X-Y-=-X . 2))
 (2126 316
       (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2126 316
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2073 2073 (:REWRITE REDUCE-INTEGERP-+))
 (2073 2073 (:REWRITE INTEGERP-MINUS-X))
 (2073 2073 (:META META-INTEGERP-CORRECT))
 (2032 2032 (:REWRITE |(subrangep x x)|))
 (1935 1935 (:REWRITE |(< y (+ (- c) x))|))
 (1922 328 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1886 280 (:REWRITE MOD-ZERO . 2))
 (1886 280 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1853 316
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1853 316
       (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (1853 316
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1739 316 (:REWRITE MOD-CANCEL-*-CONST))
 (1738 869 (:REWRITE DEFAULT-MINUS))
 (1259 1250 (:REWRITE DEFAULT-LOGIOR-2))
 (1250 1250 (:REWRITE DEFAULT-LOGIOR-1))
 (1179 1179 (:REWRITE REDUCE-RATIONALP-+))
 (1179 1179 (:REWRITE REDUCE-RATIONALP-*))
 (1179 1179 (:REWRITE RATIONALP-MINUS-X))
 (1179 1179 (:META META-RATIONALP-CORRECT))
 (1074 1074
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1074 1074
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (888 888
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (759 477 (:REWRITE DEFAULT-MOD-1))
 (523 280
      (:REWRITE |(equal (mod (+ x y) z) x)|))
 (490 56 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (477 477 (:REWRITE DEFAULT-MOD-2))
 (316 316
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (316 316 (:REWRITE |(mod x (- y))| . 3))
 (316 316 (:REWRITE |(mod x (- y))| . 2))
 (316 316 (:REWRITE |(mod x (- y))| . 1))
 (316 316
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (316 316
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (316 316 (:REWRITE |(mod (- x) y)| . 3))
 (316 316 (:REWRITE |(mod (- x) y)| . 2))
 (316 316 (:REWRITE |(mod (- x) y)| . 1))
 (316 316
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (316 316
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (316 316
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (309 306 (:REWRITE DEFAULT-LOGAND-2))
 (309 306 (:REWRITE DEFAULT-LOGAND-1))
 (168 18 (:REWRITE DEFAULT-FLOOR-RATIO))
 (120 9 (:REWRITE |(* y (* x z))|))
 (79 79 (:REWRITE |(< (* x y) 0)|))
 (59 59 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (32 18 (:REWRITE DEFAULT-FLOOR-1))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (29 29
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (29 29 (:REWRITE |(< 0 (/ x))|))
 (29 29 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:REWRITE DEFAULT-FLOOR-2))
 (16 9 (:REWRITE |(* a (/ a) b)|))
 (9 9 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32)))
(ASSERTION-INVARIANT-DEFAULT-HINT-1)
(ASSERTION-INVARIANT-DEFAULT-HINT)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS
 (16900667 13207415 (:REWRITE DEFAULT-PLUS-1))
 (5454162 5454162
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1072543
   1072543
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1072543
  1072543
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1072543
      1072543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1072543
     1072543
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1072543 1072543
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1072543 1072543
          (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (318823 1478 (:REWRITE DISJOINT-3-ITEMS))
 (270029 614
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (248718 128258 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (243187 1531
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (212619 8508 (:REWRITE |(n32-to-i32 x) --- 2|))
 (205461 8508 (:REWRITE |(n32-to-i32 x) --- 1|))
 (174847 75451
         (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (172857 75451
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (154331 108005 (:REWRITE DEFAULT-LESS-THAN-2))
 (128175 43771
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (117093 43771
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (108005 108005 (:REWRITE THE-FLOOR-BELOW))
 (108005 108005 (:REWRITE THE-FLOOR-ABOVE))
 (107951 107951
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (107951 107951
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (75693 75693 (:REWRITE INTEGERP-<-CONSTANT))
 (75693 75693 (:REWRITE CONSTANT-<-INTEGERP))
 (75693 75693
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (75693 75693
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (75693 75693
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (75693 75693
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (75693 75693 (:REWRITE |(< c (- x))|))
 (75693 75693
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (75693 75693
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (75693 75693
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (75693 75693
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (75693 75693 (:REWRITE |(< (/ x) (/ y))|))
 (75693 75693 (:REWRITE |(< (- x) c)|))
 (75693 75693 (:REWRITE |(< (- x) (- y))|))
 (65605 65605 (:REWRITE |(< (+ c/d x) y)|))
 (54854 54854
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (50447 50243 (:REWRITE DEFAULT-TIMES-2))
 (50391 50243 (:REWRITE DEFAULT-TIMES-1))
 (49300 8396 (:REWRITE ACL2-NUMBERP-X))
 (43771 43771
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (43771 43771 (:REWRITE |(equal c (/ x))|))
 (43771 43771 (:REWRITE |(equal c (- x))|))
 (43771 43771 (:REWRITE |(equal (/ x) c)|))
 (43771 43771 (:REWRITE |(equal (/ x) (/ y))|))
 (43771 43771 (:REWRITE |(equal (- x) c)|))
 (43771 43771 (:REWRITE |(equal (- x) (- y))|))
 (42036 42036
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (40528 40528 (:REWRITE FOLD-CONSTS-IN-+))
 (33359 33359 (:REWRITE |(< (+ (- c) x) y)|))
 (28956 28956 (:REWRITE |(< x (+ c/d y))|))
 (25874 761 (:REWRITE ZP-OPEN))
 (20452 5113 (:REWRITE RATIONALP-X))
 (17290 17290 (:REWRITE |(< y (+ (- c) x))|))
 (14304 1192 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (11940 11940
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (11940 11940
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (10192 4867 (:REWRITE O-INFP->NEQ-0))
 (6045 39
       (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (5187 5187 (:REWRITE REDUCE-INTEGERP-+))
 (5187 5187 (:REWRITE INTEGERP-MINUS-X))
 (5187 5187 (:META META-INTEGERP-CORRECT))
 (5113 5113 (:REWRITE REDUCE-RATIONALP-+))
 (5113 5113 (:REWRITE REDUCE-RATIONALP-*))
 (5113 5113 (:REWRITE RATIONALP-MINUS-X))
 (5113 5113 (:META META-RATIONALP-CORRECT))
 (4880 4880
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4768 1192 (:REWRITE |(+ (* c x) (* d x))|))
 (3505 3505 (:REWRITE DEFAULT-LOGIOR-2))
 (3505 3505 (:REWRITE DEFAULT-LOGIOR-1))
 (2850 2
       (:REWRITE |(y86-p (init_pdts-modify-outer-loop-1 i s))|))
 (2398 2398 (:REWRITE |(< (* x y) 0)|))
 (1910 1910
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1910 1910
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1910 1910 (:REWRITE |(< 0 (/ x))|))
 (1910 1910 (:REWRITE |(< 0 (* x y))|))
 (1192 1192 (:REWRITE |(* 0 x)|))
 (324 8 (:REWRITE |(< (if a b c) x)|))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:TYPE-PRESCRIPTION N32-TO-I32)))
(INIT_PDTS-CORRECT)
(IN-SEC_NOT_PRESENT)
(SEC_NOT_PRESENT-CUTPOINT-P)
(SEC_NOT_PRESENT-PRE)
(SEC_NOT_PRESENT-LOOP-PRE)
(SEC_NOT_PRESENT-MODIFY-LOOP-1
     (14660 124 (:DEFINITION BINARY-LOGAND))
     (7896 301
           (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (2808 1692 (:REWRITE DEFAULT-+-2))
     (2361 1692 (:REWRITE DEFAULT-+-1))
     (1553 124 (:REWRITE ZIP-OPEN))
     (1297 822 (:REWRITE DEFAULT-<-1))
     (1141 822 (:REWRITE DEFAULT-<-2))
     (1092 624 (:REWRITE DEFAULT-UNARY-MINUS))
     (944 570 (:REWRITE DEFAULT-*-2))
     (602 570 (:REWRITE DEFAULT-*-1))
     (559 124 (:REWRITE O-INFP->NEQ-0))
     (424 211 (:REWRITE DEFAULT-NUMERATOR))
     (399 21 (:REWRITE DISTRIBUTIVITY))
     (388 193 (:REWRITE DEFAULT-DENOMINATOR))
     (267 15 (:REWRITE O<=-O-FINP-DEF))
     (145 145
          (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (145 145 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (145 145 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (145 145
          (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (77 77
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (54 6 (:REWRITE O-FIRST-EXPT-<))
     (51 15 (:REWRITE AC-<))
     (42 12 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
     (36 15 (:REWRITE O-INFP-O-FINP-O<=))
     (18 6 (:REWRITE O-FIRST-COEFF-<))
     (15 15
         (:REWRITE |a < b & b < c  =>  a < c|)))
(|(paging-p (sec_not_present-modify-loop-1 i s))|
     (22043 159 (:DEFINITION BINARY-LOGAND))
     (5200 2714 (:REWRITE DEFAULT-+-2))
     (4587 2714 (:REWRITE DEFAULT-+-1))
     (3930 159 (:REWRITE ZIP-OPEN))
     (2482 1183 (:REWRITE DEFAULT-*-2))
     (2305 1337 (:REWRITE DEFAULT-<-1))
     (2035 1337 (:REWRITE DEFAULT-<-2))
     (1885 985 (:REWRITE DEFAULT-UNARY-MINUS))
     (1623 1183 (:REWRITE DEFAULT-*-1))
     (1363 159 (:REWRITE O-INFP->NEQ-0))
     (715 318 (:REWRITE DEFAULT-NUMERATOR))
     (715 318 (:REWRITE DEFAULT-DENOMINATOR))
     (513 27 (:REWRITE DISTRIBUTIVITY))
     (477 159 (:REWRITE UNICITY-OF-0))
     (262 262
          (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (262 262 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (262 262 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (262 262
          (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (60 60
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (19 19 (:REWRITE FOLD-CONSTS-IN-+)))
(|(va-to-pa addr (sec_not_present-modify-loop-1 i s))|
     (2682 1
           (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
     (1553 16 (:DEFINITION FLOOR))
     (1212 8 (:DEFINITION BINARY-LOGAND))
     (1048 8 (:DEFINITION ASH))
     (996 32
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (950 405
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (405 405 (:TYPE-PRESCRIPTION R32))
     (405 405 (:TYPE-PRESCRIPTION MEMORYP))
     (359 174 (:REWRITE DEFAULT-+-2))
     (340 60 (:REWRITE COMMUTATIVITY-OF-+))
     (316 174 (:REWRITE DEFAULT-+-1))
     (301 8 (:REWRITE ZIP-OPEN))
     (228 32 (:DEFINITION NFIX))
     (218 218 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (168 66 (:REWRITE DEFAULT-*-2))
     (164 164
          (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (155 24 (:REWRITE COMMUTATIVITY-OF-*))
     (148 82 (:REWRITE DEFAULT-<-1))
     (132 82 (:REWRITE DEFAULT-<-2))
     (124 64 (:REWRITE DEFAULT-UNARY-MINUS))
     (103 8 (:REWRITE O-INFP->NEQ-0))
     (98 66 (:REWRITE DEFAULT-*-1))
     (56 40 (:DEFINITION IFIX))
     (40 16 (:DEFINITION FIX))
     (38 38 (:TYPE-PRESCRIPTION VA-TO-PA))
     (38 16 (:REWRITE DEFAULT-NUMERATOR))
     (38 16 (:REWRITE DEFAULT-DENOMINATOR))
     (32 8 (:REWRITE UNICITY-OF-1))
     (24 8 (:REWRITE UNICITY-OF-0))
     (19 1 (:REWRITE DISTRIBUTIVITY))
     (17 17
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (17 17 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (17 17 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (17 17
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (5 5
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(|(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|
     (2682 1
           (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
     (1553 16 (:DEFINITION FLOOR))
     (1212 8 (:DEFINITION BINARY-LOGAND))
     (1048 8 (:DEFINITION ASH))
     (996 32
          (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
     (950 405
          (:TYPE-PRESCRIPTION |(n32p (r32 addr (g :mem st)))|))
     (405 405 (:TYPE-PRESCRIPTION R32))
     (405 405 (:TYPE-PRESCRIPTION MEMORYP))
     (361 176 (:REWRITE DEFAULT-+-2))
     (340 60 (:REWRITE COMMUTATIVITY-OF-+))
     (318 176 (:REWRITE DEFAULT-+-1))
     (301 8 (:REWRITE ZIP-OPEN))
     (228 32 (:DEFINITION NFIX))
     (218 218 (:TYPE-PRESCRIPTION BINARY-LOGAND))
     (168 66 (:REWRITE DEFAULT-*-2))
     (164 164
          (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
     (155 24 (:REWRITE COMMUTATIVITY-OF-*))
     (152 86 (:REWRITE DEFAULT-<-1))
     (136 86 (:REWRITE DEFAULT-<-2))
     (124 64 (:REWRITE DEFAULT-UNARY-MINUS))
     (103 8 (:REWRITE O-INFP->NEQ-0))
     (98 66 (:REWRITE DEFAULT-*-1))
     (56 40 (:DEFINITION IFIX))
     (40 16 (:DEFINITION FIX))
     (38 16 (:REWRITE DEFAULT-NUMERATOR))
     (38 16 (:REWRITE DEFAULT-DENOMINATOR))
     (32 8 (:REWRITE UNICITY-OF-1))
     (24 8 (:REWRITE UNICITY-OF-0))
     (23 7 (:REWRITE |(n32p x)|))
     (19 1 (:REWRITE DISTRIBUTIVITY))
     (17 17
         (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (17 17 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (17 17 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (17 17
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (8 2
        (:REWRITE |(good-32-address-p addr st)|))
     (5 5
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (4 4
        (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
     (4 4
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
     (2 2 (:TYPE-PRESCRIPTION N32P))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 1
        (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|)))
(|(G field (sec_not_present-modify-loop-1 i s))|
 (41297 36 (:REWRITE FLOOR-=-X/Y . 4))
 (27779 27779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (27779 27779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (27779 27779
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (22413 167 (:REWRITE FLOOR-ZERO . 3))
 (19195 167 (:REWRITE CANCEL-FLOOR-+))
 (15275 1247
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (14458 167 (:REWRITE FLOOR-ZERO . 5))
 (14127 167 (:REWRITE FLOOR-ZERO . 4))
 (13966 167 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (12900 2329 (:REWRITE DEFAULT-TIMES-2))
 (12296 12296
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (11223 1247
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (11223 1247
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (11223 1247
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (8901 750 (:REWRITE INTEGERP-MINUS-X))
 (7884 2329 (:REWRITE DEFAULT-TIMES-1))
 (7823 797 (:REWRITE DEFAULT-LOGAND-2))
 (7695 432 (:REWRITE DEFAULT-PLUS-1))
 (7136 342 (:LINEAR BINARY-LOGAND-<=))
 (7064 342 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (6508 167 (:REWRITE FLOOR-=-X/Y . 3))
 (6508 167 (:REWRITE FLOOR-=-X/Y . 2))
 (6287 334 (:REWRITE |(* (- x) y)|))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (6235 1247
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (6075 689
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5867 689
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4881 80
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4796 66 (:DEFINITION NATP))
 (4691 80 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4536 28 (:REWRITE |(equal (+ (- c) x) y)|))
 (4487 80
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4423 167 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3857 693 (:REWRITE DEFAULT-LESS-THAN-1))
 (3760 16 (:REWRITE |(+ (+ x y) z)|))
 (3394 334 (:REWRITE DEFAULT-MINUS))
 (3249 167 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3227 334 (:REWRITE |(- (* c x))|))
 (3061 3061
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3061 3061
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3061 3061
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2933 693 (:REWRITE DEFAULT-LESS-THAN-2))
 (2252 689 (:REWRITE SIMPLIFY-SUMS-<))
 (2106 234
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1734 342 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1734 342 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1712 28 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1697 167 (:REWRITE FLOOR-ZERO . 2))
 (1697 167 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1697 167 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1436 28 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1373 167
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1373 167
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1318 104
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (1293 1293
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1153 167 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1152 444
       (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (1029 167 (:REWRITE DEFAULT-FLOOR-1))
 (1010 10 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (998 46 (:REWRITE |(+ c (+ d x))|))
 (818 693
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (818 693
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (814 142 (:REWRITE ACL2-NUMBERP-X))
 (797 797 (:REWRITE LOGAND-CONSTANT-MASK))
 (797 797 (:REWRITE DEFAULT-LOGAND-1))
 (711 104
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (693 693
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (693 693
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (693 693 (:REWRITE INTEGERP-<-CONSTANT))
 (693 693 (:REWRITE CONSTANT-<-INTEGERP))
 (693 693
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (693 693
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (693 693
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (693 693
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (693 693 (:REWRITE |(< c (- x))|))
 (693 693
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (693 693
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (693 693
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (693 693
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (693 693 (:REWRITE |(< (/ x) (/ y))|))
 (693 693 (:REWRITE |(< (- x) c)|))
 (693 693 (:REWRITE |(< (- x) (- y))|))
 (583 583 (:REWRITE REDUCE-INTEGERP-+))
 (583 583 (:META META-INTEGERP-CORRECT))
 (491 167
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (491 167
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (381 36
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (342 342 (:TYPE-PRESCRIPTION NATP))
 (336 84 (:REWRITE RATIONALP-X))
 (294 294
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (254 254 (:TYPE-PRESCRIPTION ABS))
 (234 234 (:TYPE-PRESCRIPTION FLOOR))
 (206 206 (:REWRITE |(< (/ x) 0)|))
 (206 206 (:REWRITE |(< (* x y) 0)|))
 (204 204
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (204 204
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (202 202
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (202 202 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (202 202 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (202 202
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (167 167 (:REWRITE DEFAULT-FLOOR-2))
 (167 167 (:REWRITE |(floor x (- y))| . 2))
 (167 167 (:REWRITE |(floor x (- y))| . 1))
 (167 167
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (167 167
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (167 167 (:REWRITE |(floor (- x) y)| . 2))
 (167 167 (:REWRITE |(floor (- x) y)| . 1))
 (128 16 (:REWRITE |(* x (+ y z))|))
 (127 127
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (127 127
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (127 127 (:REWRITE |(< 0 (/ x))|))
 (127 127 (:REWRITE |(< 0 (* x y))|))
 (96 92
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (92 92
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (84 84 (:REWRITE REDUCE-RATIONALP-+))
 (84 84 (:REWRITE REDUCE-RATIONALP-*))
 (84 84 (:REWRITE RATIONALP-MINUS-X))
 (84 84 (:META META-RATIONALP-CORRECT))
 (80 80
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (80 80 (:REWRITE |(equal c (/ x))|))
 (80 80 (:REWRITE |(equal c (- x))|))
 (80 80 (:REWRITE |(equal (/ x) c)|))
 (80 80 (:REWRITE |(equal (/ x) (/ y))|))
 (80 80 (:REWRITE |(equal (- x) c)|))
 (80 80 (:REWRITE |(equal (- x) (- y))|))
 (64 8
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (52 52 (:REWRITE |(< (+ c/d x) y)|))
 (52 52 (:REWRITE |(< (+ (- c) x) y)|))
 (36 16
     (:REWRITE |(good-32-address-p addr st)|))
 (36 8
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (34 34 (:REWRITE FOLD-CONSTS-IN-+))
 (32 32
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (24 24 (:TYPE-PRESCRIPTION PAGING-P))
 (21 21
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (16
   8
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (8 4
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|)))
(|(y86-p (sec_not_present-modify-loop-1 i s))|
 (93692 93692
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (93692 93692
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (93692 93692
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57987 4491
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (42555 42 (:REWRITE FLOOR-=-X/Y . 4))
 (40419 4491
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (40419 4491
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (40419 4491
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (23901 600 (:REWRITE DEFAULT-PLUS-2))
 (23517 208 (:REWRITE FLOOR-ZERO . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (22455 4491
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (19795 19795
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (17852 208 (:REWRITE CANCEL-FLOOR-+))
 (17493 721
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15574 208 (:REWRITE FLOOR-ZERO . 5))
 (15331 208 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (14775 208 (:REWRITE FLOOR-ZERO . 4))
 (13219 1839 (:REWRITE DEFAULT-LOGAND-2))
 (12350 3011 (:REWRITE DEFAULT-TIMES-2))
 (8704 1075 (:REWRITE INTEGERP-MINUS-X))
 (6873 3011 (:REWRITE DEFAULT-TIMES-1))
 (6561 600 (:REWRITE DEFAULT-PLUS-1))
 (6439 208 (:REWRITE FLOOR-=-X/Y . 3))
 (6439 208 (:REWRITE FLOOR-=-X/Y . 2))
 (5812 416 (:REWRITE |(* (- x) y)|))
 (5749 705
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5749 705
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5404 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5404 64
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5192 721 (:REWRITE DEFAULT-LESS-THAN-1))
 (5089 64
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4265 4265
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4265 4265
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4265 4265
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3995 208 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3930 10 (:REWRITE |(+ y (+ x z))|))
 (3219 21 (:REWRITE |(equal (+ (- c) x) y)|))
 (3218 416 (:REWRITE DEFAULT-MINUS))
 (3010 416 (:REWRITE |(- (* c x))|))
 (2508 721 (:REWRITE DEFAULT-LESS-THAN-2))
 (2178 208 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2077 430 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (2077 430 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (2021 705 (:REWRITE SIMPLIFY-SUMS-<))
 (1964 43 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1839 1839 (:REWRITE LOGAND-CONSTANT-MASK))
 (1839 1839 (:REWRITE DEFAULT-LOGAND-1))
 (1665 1665
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1651 43 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1609 208 (:REWRITE FLOOR-ZERO . 2))
 (1609 208 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1609 208 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1276 1276
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1276 1276 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1276 1276 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1276 1276
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1259 208
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1259 208
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1162 208 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1059 159
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (891 99
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (882 721
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (882 721
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (867 867 (:REWRITE REDUCE-INTEGERP-+))
 (867 867 (:META META-INTEGERP-CORRECT))
 (792 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (777 208 (:REWRITE DEFAULT-FLOOR-1))
 (709 709
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (709 709 (:REWRITE INTEGERP-<-CONSTANT))
 (709 709 (:REWRITE CONSTANT-<-INTEGERP))
 (709 709
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (709 709
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (709 709
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (709 709
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (709 709 (:REWRITE |(< c (- x))|))
 (709 709
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (709 709
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (709 709
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (709 709
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (709 709 (:REWRITE |(< (/ x) (/ y))|))
 (709 709 (:REWRITE |(< (- x) c)|))
 (709 709 (:REWRITE |(< (- x) (- y))|))
 (609 159
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (558 208
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (558 208
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (431 431
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (346 42
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (325 325 (:TYPE-PRESCRIPTION ABS))
 (208 208 (:REWRITE DEFAULT-FLOOR-2))
 (208 208 (:REWRITE |(floor x (- y))| . 2))
 (208 208 (:REWRITE |(floor x (- y))| . 1))
 (208 208
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (208 208
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (208 208 (:REWRITE |(floor (- x) y)| . 2))
 (208 208 (:REWRITE |(floor (- x) y)| . 1))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (166 166 (:REWRITE |(< 0 (/ x))|))
 (166 166 (:REWRITE |(< 0 (* x y))|))
 (76 73
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (73 73
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (64 64
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (64 64 (:REWRITE |(equal c (/ x))|))
 (64 64 (:REWRITE |(equal c (- x))|))
 (64 64 (:REWRITE |(equal (/ x) c)|))
 (64 64 (:REWRITE |(equal (/ x) (/ y))|))
 (64 64 (:REWRITE |(equal (- x) c)|))
 (64 64 (:REWRITE |(equal (- x) (- y))|))
 (54 54 (:REWRITE FOLD-CONSTS-IN-+))
 (48 6
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (29
   29
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (29
  29
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (29 29
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (27 12
     (:REWRITE |(good-32-address-p addr st)|))
 (27 6
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (24 24
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (18 18 (:TYPE-PRESCRIPTION PAGING-P))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12
   6
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (6 6
    (:REWRITE |(g field (w32 addr val st))|))
 (6 3
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(|(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|
 (53444 53444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (53444 53444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (53444 53444
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (42836 42 (:REWRITE FLOOR-=-X/Y . 4))
 (31362 2462
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (23901 600 (:REWRITE DEFAULT-PLUS-2))
 (23511 208 (:REWRITE FLOOR-ZERO . 3))
 (22158 2462
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (22158 2462
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (22158 2462
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (17901 17901
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (17852 208 (:REWRITE CANCEL-FLOOR-+))
 (17593 721
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15798 208 (:REWRITE FLOOR-ZERO . 5))
 (15555 208 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (14769 208 (:REWRITE FLOOR-ZERO . 4))
 (13219 1839 (:REWRITE DEFAULT-LOGAND-2))
 (12350 3011 (:REWRITE DEFAULT-TIMES-2))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (12310 2462
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (8495 866 (:REWRITE INTEGERP-MINUS-X))
 (6873 3011 (:REWRITE DEFAULT-TIMES-1))
 (6561 600 (:REWRITE DEFAULT-PLUS-1))
 (6439 208 (:REWRITE FLOOR-=-X/Y . 3))
 (6439 208 (:REWRITE FLOOR-=-X/Y . 2))
 (5812 416 (:REWRITE |(* (- x) y)|))
 (5749 705
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5749 705
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5404 64 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5404 64
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5192 721 (:REWRITE DEFAULT-LESS-THAN-1))
 (5089 64
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3995 208 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3948 3948
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3948 3948
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3948 3948
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3930 10 (:REWRITE |(+ y (+ x z))|))
 (3219 21 (:REWRITE |(equal (+ (- c) x) y)|))
 (3218 416 (:REWRITE DEFAULT-MINUS))
 (3010 416 (:REWRITE |(- (* c x))|))
 (2508 721 (:REWRITE DEFAULT-LESS-THAN-2))
 (2178 208 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2077 430 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (2077 430 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (2021 705 (:REWRITE SIMPLIFY-SUMS-<))
 (1964 43 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1839 1839 (:REWRITE LOGAND-CONSTANT-MASK))
 (1839 1839 (:REWRITE DEFAULT-LOGAND-1))
 (1665 1665
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1651 43 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1609 208 (:REWRITE FLOOR-ZERO . 2))
 (1609 208 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1609 208 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1449 161
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1276 1276
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1276 1276 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1276 1276 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1276 1276
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1259 208
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1259 208
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1162 208 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1059 159
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (882 721
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (882 721
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (792 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (777 208 (:REWRITE DEFAULT-FLOOR-1))
 (709 709
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (709 709 (:REWRITE INTEGERP-<-CONSTANT))
 (709 709 (:REWRITE CONSTANT-<-INTEGERP))
 (709 709
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (709 709
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (709 709
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (709 709
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (709 709 (:REWRITE |(< c (- x))|))
 (709 709
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (709 709
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (709 709
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (709 709
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (709 709 (:REWRITE |(< (/ x) (/ y))|))
 (709 709 (:REWRITE |(< (- x) c)|))
 (709 709 (:REWRITE |(< (- x) (- y))|))
 (658 658 (:REWRITE REDUCE-INTEGERP-+))
 (658 658 (:META META-INTEGERP-CORRECT))
 (609 159
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (558 208
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (558 208
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (431 431
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (346 42
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (325 325 (:TYPE-PRESCRIPTION ABS))
 (208 208 (:REWRITE DEFAULT-FLOOR-2))
 (208 208 (:REWRITE |(floor x (- y))| . 2))
 (208 208 (:REWRITE |(floor x (- y))| . 1))
 (208 208
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (208 208
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (208 208 (:REWRITE |(floor (- x) y)| . 2))
 (208 208 (:REWRITE |(floor (- x) y)| . 1))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (166 166
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (166 166 (:REWRITE |(< 0 (/ x))|))
 (166 166 (:REWRITE |(< 0 (* x y))|))
 (76 73
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (73 73
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (64 64
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (64 64 (:REWRITE |(equal c (/ x))|))
 (64 64 (:REWRITE |(equal c (- x))|))
 (64 64 (:REWRITE |(equal (/ x) c)|))
 (64 64 (:REWRITE |(equal (/ x) (/ y))|))
 (64 64 (:REWRITE |(equal (- x) c)|))
 (64 64 (:REWRITE |(equal (- x) (- y))|))
 (54 54 (:REWRITE FOLD-CONSTS-IN-+))
 (48 6
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (27 12
     (:REWRITE |(good-32-address-p addr st)|))
 (27 6
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (26 26 (:REWRITE |(< (* x y) 0)|))
 (24 24
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (18 18 (:TYPE-PRESCRIPTION PAGING-P))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12
   6
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (10
   10
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (10
  10
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (10 10
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6 6
    (:REWRITE |(g field (w32 addr val st))|))
 (6 6
    (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (6 3
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(|(good-state-p (sec_not_present-modify-loop-1 i s))|
 (105290 8
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (69251 69251
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (69251 69251
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (69251 69251
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (55333 1049 (:REWRITE DEFAULT-PLUS-2))
 (42939 3303
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (42070 689
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (36927 39 (:REWRITE FLOOR-=-X/Y . 4))
 (34567
  19
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (29727 3303
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (29727 3303
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (29646 3294
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (28618 6
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (25686 1049 (:REWRITE DEFAULT-PLUS-1))
 (21598 198 (:REWRITE FLOOR-ZERO . 3))
 (19718 1825 (:REWRITE DEFAULT-LOGAND-2))
 (19609 668 (:REWRITE SIMPLIFY-SUMS-<))
 (17207 17207
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (16866 198 (:REWRITE CANCEL-FLOOR-+))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (16515 3303
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (16470 3294
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (14707 200 (:REWRITE FLOOR-ZERO . 5))
 (14545 200 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (13615
  19
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (11640 2873 (:REWRITE DEFAULT-TIMES-2))
 (11314 2 (:REWRITE DISJOINT-3-ITEMS))
 (8031 822 (:REWRITE INTEGERP-MINUS-X))
 (6474 2873 (:REWRITE DEFAULT-TIMES-1))
 (6423 668
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6411 668
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6077 200 (:REWRITE FLOOR-=-X/Y . 3))
 (6077 200 (:REWRITE FLOOR-=-X/Y . 2))
 (5490 396 (:REWRITE |(* (- x) y)|))
 (5191 444 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (5191 444 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (4828 689 (:REWRITE DEFAULT-LESS-THAN-1))
 (4791 61
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4690 61 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4480 61
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4292 28 (:REWRITE |(equal (+ (- c) x) y)|))
 (3811 200 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3727 3727
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3727 3727
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3727 3727
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3626 689 (:REWRITE DEFAULT-LESS-THAN-2))
 (3042 396 (:REWRITE DEFAULT-MINUS))
 (2844 396 (:REWRITE |(- (* c x))|))
 (2074 200 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1852 41 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1825 1825 (:REWRITE LOGAND-CONSTANT-MASK))
 (1825 1825 (:REWRITE DEFAULT-LOGAND-1))
 (1685 25 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1664 8 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (1584 1584
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1557 41 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1537 200 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1537 200 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1521 198 (:REWRITE FLOOR-ZERO . 2))
 (1213 1213
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1213 1213 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1213 1213 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1213 1213
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1129 198
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1129 198
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1060 198 (:REWRITE FLOOR-CANCEL-*-CONST))
 (960 146
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (896 2
      (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (840 689
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (840 689
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (737 200 (:REWRITE DEFAULT-FLOOR-1))
 (678 678
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (678 678 (:REWRITE INTEGERP-<-CONSTANT))
 (678 678 (:REWRITE CONSTANT-<-INTEGERP))
 (678 678
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (678 678
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (678 678
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (678 678
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (678 678 (:REWRITE |(< c (- x))|))
 (678 678
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (678 678
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (678 678
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (678 678
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (678 678 (:REWRITE |(< (/ x) (/ y))|))
 (678 678 (:REWRITE |(< (- x) c)|))
 (678 678 (:REWRITE |(< (- x) (- y))|))
 (624 624 (:REWRITE REDUCE-INTEGERP-+))
 (624 624 (:META META-INTEGERP-CORRECT))
 (590 198
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (590 198
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (581 581
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (553 146
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (353 75
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (312 38
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (308 308 (:TYPE-PRESCRIPTION ABS))
 (200 200 (:REWRITE DEFAULT-FLOOR-2))
 (198 198 (:REWRITE |(floor x (- y))| . 2))
 (198 198 (:REWRITE |(floor x (- y))| . 1))
 (198 198
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (198 198
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (198 198 (:REWRITE |(floor (- x) y)| . 2))
 (198 198 (:REWRITE |(floor (- x) y)| . 1))
 (155 155
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (155 155
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (155 155 (:REWRITE |(< 0 (/ x))|))
 (155 155 (:REWRITE |(< 0 (* x y))|))
 (144 18 (:REWRITE |(* x (+ y z))|))
 (128 128 (:REWRITE FOLD-CONSTS-IN-+))
 (99 1 (:REWRITE O-INFP->NEQ-0))
 (73 73
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (61 61
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (61 61 (:REWRITE |(equal c (/ x))|))
 (61 61 (:REWRITE |(equal c (- x))|))
 (61 61 (:REWRITE |(equal (/ x) c)|))
 (61 61 (:REWRITE |(equal (/ x) (/ y))|))
 (61 61 (:REWRITE |(equal (- x) c)|))
 (61 61 (:REWRITE |(equal (- x) (- y))|))
 (38
   38
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (38
  38
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (38 38
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (34 34 (:REWRITE |(< (+ c/d x) y)|))
 (32 8 (:REWRITE |(+ (* c x) (* d x))|))
 (24 24 (:REWRITE |(< (* x y) 0)|))
 (23 23 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22 (:REWRITE |(< (/ x) 0)|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 2 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(* 0 x)|))
 (8 4
    (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (4 4 (:REWRITE |(va-to-pa addr st)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2
    (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (1 1 (:REWRITE FLOOR-POSITIVE . 4))
 (1 1 (:REWRITE FLOOR-POSITIVE . 3))
 (1 1 (:REWRITE FLOOR-POSITIVE . 2))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|)))
(|(r32 addr (sec_not_present-modify-loop-1 i s))|
 (158762 158762
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (158762 158762
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (158762 158762
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (98576 2298 (:REWRITE DEFAULT-PLUS-2))
 (98411 7635
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (69493 2298 (:REWRITE DEFAULT-PLUS-1))
 (68715 7635
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (68715 7635
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (68715 7635
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (46522 4
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (41291 1047
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (39840 4 (:REWRITE DISJOINT-3-ITEMS))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (38175 7635
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (30226 2693 (:REWRITE DEFAULT-LOGAND-2))
 (30089 30089
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (27606 301 (:REWRITE FLOOR-ZERO . 3))
 (26177 301 (:REWRITE CANCEL-FLOOR-+))
 (24937 38 (:REWRITE FLOOR-=-X/Y . 4))
 (21591 4354 (:REWRITE DEFAULT-TIMES-2))
 (19030 301 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (17665 301 (:REWRITE FLOOR-ZERO . 5))
 (16834 301 (:REWRITE FLOOR-ZERO . 4))
 (15615 960
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12411 1228 (:REWRITE INTEGERP-MINUS-X))
 (9768 4354 (:REWRITE DEFAULT-TIMES-1))
 (8770 301 (:REWRITE FLOOR-=-X/Y . 3))
 (8770 301 (:REWRITE FLOOR-=-X/Y . 2))
 (8536 613 (:REWRITE |(* (- x) y)|))
 (7165 1047 (:REWRITE DEFAULT-LESS-THAN-1))
 (6255 633 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (6255 633 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5867 301 (:REWRITE DEFAULT-FLOOR-RATIO))
 (5280 59
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5152 1047 (:REWRITE DEFAULT-LESS-THAN-2))
 (4986 59
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4977 59 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4959 4959
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4959 4959
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4959 4959
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4912 604 (:REWRITE DEFAULT-MINUS))
 (3374 34 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3359 62 (:REWRITE |(equal (/ x) c)|))
 (3209 301 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2944 65 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (2693 2693 (:REWRITE LOGAND-CONSTANT-MASK))
 (2693 2693 (:REWRITE DEFAULT-LOGAND-1))
 (2475 65 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2464 2464
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2357 301 (:REWRITE FLOOR-ZERO . 2))
 (2357 301 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (2357 301 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1899 211
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (1839 301
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1839 301
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1810 1810
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (1810 1810 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (1810 1810 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (1810 1810
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1618 301 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1316 1316
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1304 196
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (1243 1047
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1243 1047
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1153 301 (:REWRITE DEFAULT-FLOOR-1))
 (1059 961 (:REWRITE |(< (- x) c)|))
 (1059 961 (:REWRITE |(< (- x) (- y))|))
 (961 961
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (961 961 (:REWRITE INTEGERP-<-CONSTANT))
 (961 961 (:REWRITE CONSTANT-<-INTEGERP))
 (961 961
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (961 961
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (961 961
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (961 961
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (961 961 (:REWRITE |(< c (- x))|))
 (961 961
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (961 961
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (961 961
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (961 961
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (961 961 (:REWRITE |(< (/ x) (/ y))|))
 (927 927 (:REWRITE REDUCE-INTEGERP-+))
 (927 927 (:META META-INTEGERP-CORRECT))
 (819 301
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (819 301
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (750 196
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (591 3 (:REWRITE |(equal x (/ y))|))
 (395 395 (:TYPE-PRESCRIPTION ABS))
 (356 62 (:REWRITE |(equal (/ x) (/ y))|))
 (317 38
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (306 306 (:REWRITE FOLD-CONSTS-IN-+))
 (301 301 (:REWRITE DEFAULT-FLOOR-2))
 (301 301 (:REWRITE |(floor x (- y))| . 2))
 (301 301 (:REWRITE |(floor x (- y))| . 1))
 (301 301
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (301 301
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (301 301 (:REWRITE |(floor (- x) y)| . 2))
 (301 301 (:REWRITE |(floor (- x) y)| . 1))
 (297 3 (:REWRITE O-INFP->NEQ-0))
 (297 3 (:REWRITE DEFAULT-DIVIDE))
 (297 3 (:REWRITE |(not (equal x (/ y)))|))
 (297 3 (:REWRITE |(/ (/ x))|))
 (221 65
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (201 201
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (201 201
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (201 201 (:REWRITE |(< 0 (/ x))|))
 (201 201 (:REWRITE |(< 0 (* x y))|))
 (185
   185
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (185
  185
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (185
     185
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (185 185
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (165 165 (:REWRITE |(< (+ c/d x) y)|))
 (79 79 (:REWRITE |(< (+ (- c) x) y)|))
 (72 72
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (65 65
     (:REWRITE |(g field (w32 addr val st))|))
 (62 62
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (62 62 (:REWRITE |(equal c (/ x))|))
 (62 62 (:REWRITE |(equal (- x) (- y))|))
 (59 59
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (59 59 (:REWRITE |(equal c (- x))|))
 (59 59 (:REWRITE |(equal (- x) c)|))
 (32
  32
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (32
  32
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (30 30 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 3 (:REWRITE |(* a (/ a) b)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:REWRITE FLOOR-ZERO . 1))
 (3 3 (:REWRITE FLOOR-NEGATIVE . 4))
 (3 3 (:REWRITE FLOOR-NEGATIVE . 3))
 (3 3 (:REWRITE FLOOR-NEGATIVE . 2))
 (3 3 (:REWRITE |(equal (* x y) 0)|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|)))
(|(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 1|
 (288106 288106
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (288106 288106
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (288106 288106
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (238604
  65
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (226234 5037 (:REWRITE DEFAULT-PLUS-2))
 (190014 14
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (177273 13865
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (125774 1860
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (124785 13865
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (124785 13865
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (124758 13862
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (102226 5037 (:REWRITE DEFAULT-PLUS-1))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (69325 13865
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (69310 13862
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (65640 39
        (:REWRITE |(r32 addr (sec_not_present-modify-loop-1 i s))|))
 (50149 50149
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (45332 443 (:REWRITE FLOOR-ZERO . 3))
 (38627 443 (:REWRITE CANCEL-FLOOR-+))
 (37636 7
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (31289 3872 (:REWRITE DEFAULT-LOGAND-2))
 (28521 447 (:REWRITE FLOOR-ZERO . 5))
 (28510 447 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (27496 6693 (:REWRITE DEFAULT-TIMES-2))
 (26362 75 (:REWRITE FLOOR-=-X/Y . 4))
 (25307 1685
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (24713 1685
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (21357 8
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (18281 1785 (:REWRITE INTEGERP-MINUS-X))
 (17006 1860 (:REWRITE DEFAULT-LESS-THAN-1))
 (15953 14 (:REWRITE DISJOINT-3-ITEMS))
 (15077 1860 (:REWRITE DEFAULT-LESS-THAN-2))
 (15073 6693 (:REWRITE DEFAULT-TIMES-1))
 (13361 447 (:REWRITE FLOOR-=-X/Y . 3))
 (13361 447 (:REWRITE FLOOR-=-X/Y . 2))
 (12583 898 (:REWRITE |(* (- x) y)|))
 (12318 178 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10797 143
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10482 143
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10376 48 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (9215 143 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8726 447 (:REWRITE DEFAULT-FLOOR-RATIO))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7511 49 (:REWRITE |(equal (+ (- c) x) y)|))
 (6980 922 (:REWRITE DEFAULT-MINUS))
 (6687 743
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6581 898 (:REWRITE |(- (* c x))|))
 (5041 860 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (5041 860 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (4793 447 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3872 3872 (:REWRITE LOGAND-CONSTANT-MASK))
 (3872 3872 (:REWRITE DEFAULT-LOGAND-1))
 (3854 3854
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3768 79 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (3514 447 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (3514 447 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (3482 443 (:REWRITE FLOOR-ZERO . 2))
 (3426 443
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3426 443
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (3164 79 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2831 2831
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2831 2831 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2831 2831 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2831 2831
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2688 2
       (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (2677 2677
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2506 443 (:REWRITE FLOOR-CANCEL-*-CONST))
 (2262 326
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2192 1860
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2192 1860
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2102 1706 (:REWRITE |(< (- x) c)|))
 (1726 447 (:REWRITE DEFAULT-FLOOR-1))
 (1710 1706 (:REWRITE |(< (- x) (- y))|))
 (1706 1706
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1706 1706
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1706 1706
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1706 1706
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1706 1706 (:REWRITE |(< c (- x))|))
 (1706 1706
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1706 1706
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1706 1706
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1706 1706
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1706 1706 (:REWRITE |(< (/ x) (/ y))|))
 (1694 1694
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1694 1694 (:REWRITE INTEGERP-<-CONSTANT))
 (1694 1694 (:REWRITE CONSTANT-<-INTEGERP))
 (1598 19 (:REWRITE O-INFP->NEQ-0))
 (1342 1342 (:REWRITE REDUCE-INTEGERP-+))
 (1342 1342 (:META META-INTEGERP-CORRECT))
 (1294 326
       (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (729 729 (:REWRITE FOLD-CONSTS-IN-+))
 (688 12 (:DEFINITION MAX))
 (672 672 (:TYPE-PRESCRIPTION ABS))
 (606 74
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (584 48 (:REWRITE |(+ (* c x) (* d x))|))
 (531
   531
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (531
  531
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (531 531
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (531
     531
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (531 531
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (531 531
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (499 443
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (499 443
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (447 447 (:REWRITE DEFAULT-FLOOR-2))
 (443 443 (:REWRITE |(floor x (- y))| . 2))
 (443 443 (:REWRITE |(floor x (- y))| . 1))
 (443 443
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (443 443
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (443 443 (:REWRITE |(floor (- x) y)| . 2))
 (443 443 (:REWRITE |(floor (- x) y)| . 1))
 (404 404 (:REWRITE |(< (+ c/d x) y)|))
 (342 342
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (342 342
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (342 342 (:REWRITE |(< 0 (/ x))|))
 (342 342 (:REWRITE |(< 0 (* x y))|))
 (228 169
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (207 147 (:REWRITE |(equal (/ x) c)|))
 (168 168
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (147 147 (:REWRITE |(equal c (/ x))|))
 (147 147 (:REWRITE |(equal (/ x) (/ y))|))
 (147 147 (:REWRITE |(equal (- x) (- y))|))
 (143 143
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (143 143 (:REWRITE |(equal c (- x))|))
 (143 143 (:REWRITE |(equal (- x) c)|))
 (120 12 (:REWRITE |(* x (- y))|))
 (116 116
      (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (94 94
     (:REWRITE |(g field (w32 addr val st))|))
 (87 87 (:REWRITE |(< (* x y) 0)|))
 (62 62 (:REWRITE |(< x (+ c/d y))|))
 (60 4 (:REWRITE |(* x (if a b c))|))
 (56 56 (:REWRITE |(< (/ x) 0)|))
 (48 48 (:REWRITE |(< y (+ (- c) x))|))
 (48 48 (:REWRITE |(* 0 x)|))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (35 35
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (28 4 (:REWRITE |(+ x (if a b c))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (16 12 (:REWRITE |(- (- x))|))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(not (equal x (/ y)))|))
 (4 4 (:REWRITE |(equal x (/ y))|))
 (4 4 (:REWRITE |(/ (/ x))|))
 (4 1 (:REWRITE |(* a (/ a) b)|))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
(|(r32 addr (sec_not_present-modify-loop-1 i s)) --- written to 2|
 (298986 298986
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (298986 298986
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (298986 298986
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (263777 5466 (:REWRITE DEFAULT-PLUS-2))
 (256176 1884
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (190014 14
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (184345 14409
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (129681 14409
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (129681 14409
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (129654 14406
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (107919 5466 (:REWRITE DEFAULT-PLUS-1))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (72045 14409
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (72030 14406
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (71955 39
        (:REWRITE |(r32 addr (sec_not_present-modify-loop-1 i s))|))
 (50741 50741
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (45332 443 (:REWRITE FLOOR-ZERO . 3))
 (38627 443 (:REWRITE CANCEL-FLOOR-+))
 (37636 7
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (31749 3892 (:REWRITE DEFAULT-LOGAND-2))
 (28521 447 (:REWRITE FLOOR-ZERO . 5))
 (28510 447 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (27488 6685 (:REWRITE DEFAULT-TIMES-2))
 (26362 75 (:REWRITE FLOOR-=-X/Y . 4))
 (24599 1677
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (24005 1677
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (23037 8
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (19443 14 (:REWRITE DISJOINT-3-ITEMS))
 (18846 1884 (:REWRITE DEFAULT-LESS-THAN-1))
 (18281 1785 (:REWRITE INTEGERP-MINUS-X))
 (17097 1884 (:REWRITE DEFAULT-LESS-THAN-2))
 (15065 6685 (:REWRITE DEFAULT-TIMES-1))
 (13361 447 (:REWRITE FLOOR-=-X/Y . 3))
 (13361 447 (:REWRITE FLOOR-=-X/Y . 2))
 (12583 898 (:REWRITE |(* (- x) y)|))
 (11502 162 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10797 143
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10482 143
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9215 143 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8726 447 (:REWRITE DEFAULT-FLOOR-RATIO))
 (8712 40 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8269 8269
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (7511 49 (:REWRITE |(equal (+ (- c) x) y)|))
 (6980 922 (:REWRITE DEFAULT-MINUS))
 (6687 743
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6581 898 (:REWRITE |(- (* c x))|))
 (5156 865 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (5156 865 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (4793 447 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3892 3892 (:REWRITE LOGAND-CONSTANT-MASK))
 (3892 3892 (:REWRITE DEFAULT-LOGAND-1))
 (3854 3854
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3768 79 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (3514 447 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (3514 447 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (3482 443 (:REWRITE FLOOR-ZERO . 2))
 (3426 443
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3426 443
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (3164 79 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2844 2844
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2844 2844 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2844 2844 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2844 2844
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2841 2841
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2506 443 (:REWRITE FLOOR-CANCEL-*-CONST))
 (2262 326
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2216 1884
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2216 1884
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2094 1698 (:REWRITE |(< (- x) c)|))
 (1726 447 (:REWRITE DEFAULT-FLOOR-1))
 (1702 1698 (:REWRITE |(< (- x) (- y))|))
 (1698 1698
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1698 1698
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1698 1698
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1698 1698
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1698 1698 (:REWRITE |(< c (- x))|))
 (1698 1698
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1698 1698
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1698 1698
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1698 1698
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1698 1698 (:REWRITE |(< (/ x) (/ y))|))
 (1686 1686
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1686 1686 (:REWRITE INTEGERP-<-CONSTANT))
 (1686 1686 (:REWRITE CONSTANT-<-INTEGERP))
 (1598 19 (:REWRITE O-INFP->NEQ-0))
 (1342 1342 (:REWRITE REDUCE-INTEGERP-+))
 (1342 1342 (:META META-INTEGERP-CORRECT))
 (1294 326
       (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (896 896 (:REWRITE FOLD-CONSTS-IN-+))
 (688 12 (:DEFINITION MAX))
 (672 672 (:TYPE-PRESCRIPTION ABS))
 (606 74
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (552 40 (:REWRITE |(+ (* c x) (* d x))|))
 (535
   535
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (535
  535
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (535 535
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (535
     535
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (535 535
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (535 535
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (499 443
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (499 443
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (447 447 (:REWRITE DEFAULT-FLOOR-2))
 (443 443 (:REWRITE |(floor x (- y))| . 2))
 (443 443 (:REWRITE |(floor x (- y))| . 1))
 (443 443
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (443 443
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (443 443 (:REWRITE |(floor (- x) y)| . 2))
 (443 443 (:REWRITE |(floor (- x) y)| . 1))
 (417 417 (:REWRITE |(< (+ c/d x) y)|))
 (342 342
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (342 342
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (342 342 (:REWRITE |(< 0 (/ x))|))
 (342 342 (:REWRITE |(< 0 (* x y))|))
 (228 169
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (207 147 (:REWRITE |(equal (/ x) c)|))
 (168 168
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (147 147 (:REWRITE |(equal c (/ x))|))
 (147 147 (:REWRITE |(equal (/ x) (/ y))|))
 (147 147 (:REWRITE |(equal (- x) (- y))|))
 (143 143
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (143 143 (:REWRITE |(equal c (- x))|))
 (143 143 (:REWRITE |(equal (- x) c)|))
 (120 12 (:REWRITE |(* x (- y))|))
 (116 116
      (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (95 95 (:REWRITE |(< x (+ c/d y))|))
 (94 94
     (:REWRITE |(g field (w32 addr val st))|))
 (87 87 (:REWRITE |(< (* x y) 0)|))
 (60 4 (:REWRITE |(* x (if a b c))|))
 (55 55 (:REWRITE |(< y (+ (- c) x))|))
 (52 52 (:REWRITE |(< (/ x) 0)|))
 (40 40 (:REWRITE |(* 0 x)|))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (31 31
     (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (28 4 (:REWRITE |(+ x (if a b c))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (16 12 (:REWRITE |(- (- x))|))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (4 4 (:REWRITE DEFAULT-DIVIDE))
 (4 4 (:REWRITE |(not (equal x (/ y)))|))
 (4 4 (:REWRITE |(equal x (/ y))|))
 (4 4 (:REWRITE |(/ (/ x))|))
 (4 1 (:REWRITE |(* a (/ a) b)|))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
(|(sec_not_present-modify-loop-1 i (w32 addr val s))|
 (430049 14291 (:REWRITE DEFAULT-PLUS-2))
 (360424 360424
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (360424 360424
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (360424 360424
         (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (320220
  340
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (275937 2468
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (222306 17390
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (193020 22
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (183221 14291 (:REWRITE DEFAULT-PLUS-1))
 (174484 2338 (:REWRITE SIMPLIFY-SUMS-<))
 (156510 17390
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (156510 17390
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (156510 17390
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (136300
  340
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (118734 37 (:REWRITE DISJOINT-3-ITEMS))
 (98893 115 (:REWRITE FLOOR-=-X/Y . 4))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (86950 17390
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (65284 667 (:REWRITE FLOOR-ZERO . 3))
 (55643 667 (:REWRITE CANCEL-FLOOR-+))
 (54078 54078
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (44566 9571 (:REWRITE DEFAULT-TIMES-2))
 (41253 667 (:REWRITE FLOOR-ZERO . 5))
 (40514 667 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (38854 667 (:REWRITE FLOOR-ZERO . 4))
 (37203 4262 (:REWRITE DEFAULT-LOGAND-2))
 (31003 2338
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (30518 2338
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (26595 2799 (:REWRITE INTEGERP-MINUS-X))
 (25027 2468 (:REWRITE DEFAULT-LESS-THAN-1))
 (21555 140 (:REWRITE |(equal (+ (- c) x) y)|))
 (20765 9571 (:REWRITE DEFAULT-TIMES-1))
 (19852 2468 (:REWRITE DEFAULT-LESS-THAN-2))
 (19035 667 (:REWRITE FLOOR-=-X/Y . 3))
 (19035 667 (:REWRITE FLOOR-=-X/Y . 2))
 (18103 1334 (:REWRITE |(* (- x) y)|))
 (16640 80 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (14533 205
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (14381 205 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (13442 205
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12410 667 (:REWRITE DEFAULT-FLOOR-RATIO))
 (12191 12191
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12191 12191
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12191 12191
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10052 1334 (:REWRITE DEFAULT-MINUS))
 (9744 176 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (9385 1334 (:REWRITE |(- (* c x))|))
 (8469 941
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (8255 25
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (7802 24 (:DEFINITION NATP))
 (7277 667 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (6010 6010
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5476 122 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (5387 1014 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (5387 1014 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5350 5350
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5026 667 (:REWRITE FLOOR-ZERO . 2))
 (5026 667 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (5026 667 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (4604 122 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (4262 4262 (:REWRITE LOGAND-CONSTANT-MASK))
 (4262 4262 (:REWRITE DEFAULT-LOGAND-1))
 (4202 667
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (4202 667
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (3506 667 (:REWRITE FLOOR-CANCEL-*-CONST))
 (3059 479
       (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (2963 2468
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2963 2468
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2358 667 (:REWRITE DEFAULT-FLOOR-1))
 (2344 2344
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2344 2344 (:REWRITE INTEGERP-<-CONSTANT))
 (2344 2344 (:REWRITE CONSTANT-<-INTEGERP))
 (2344 2344
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2344 2344
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2344 2344
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2344 2344
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2344 2344 (:REWRITE |(< c (- x))|))
 (2344 2344
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2344 2344
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2344 2344
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2344 2344
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2344 2344 (:REWRITE |(< (/ x) (/ y))|))
 (2344 2344 (:REWRITE |(< (- x) c)|))
 (2344 2344 (:REWRITE |(< (- x) (- y))|))
 (2132 2132 (:REWRITE REDUCE-INTEGERP-+))
 (2132 2132 (:META META-INTEGERP-CORRECT))
 (2128 2128
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2128 2128 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2128 2128 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2128 2128
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1858 34
       (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (1769 479
       (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (1491 667
       (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1491 667
       (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1162 1162 (:REWRITE FOLD-CONSTS-IN-+))
 (1010 1010 (:TYPE-PRESCRIPTION ABS))
 (960 115
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (787
   787
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (787
  787
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (787 787
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (787
     787
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (787 787
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (787 787
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (667 667 (:REWRITE DEFAULT-FLOOR-2))
 (667 667 (:REWRITE |(floor x (- y))| . 2))
 (667 667 (:REWRITE |(floor x (- y))| . 1))
 (667 667
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (667 667
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (667 667 (:REWRITE |(floor (- x) y)| . 2))
 (667 667 (:REWRITE |(floor (- x) y)| . 1))
 (504 504
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (504 504
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (504 504 (:REWRITE |(< 0 (/ x))|))
 (504 504 (:REWRITE |(< 0 (* x y))|))
 (320 80 (:REWRITE |(+ (* c x) (* d x))|))
 (308 308 (:REWRITE |(< (+ c/d x) y)|))
 (285 265
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (265 265
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (209 57 (:REWRITE ACL2-NUMBERP-X))
 (205 205
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (205 205 (:REWRITE |(equal c (/ x))|))
 (205 205 (:REWRITE |(equal c (- x))|))
 (205 205 (:REWRITE |(equal (/ x) c)|))
 (205 205 (:REWRITE |(equal (/ x) (/ y))|))
 (205 205 (:REWRITE |(equal (- x) c)|))
 (205 205 (:REWRITE |(equal (- x) (- y))|))
 (184 184 (:REWRITE |(< (+ (- c) x) y)|))
 (164 40
      (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (160 160 (:REWRITE |(< (* x y) 0)|))
 (137 137 (:REWRITE |(< (/ x) 0)|))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (96 96 (:TYPE-PRESCRIPTION NATP))
 (80 80 (:REWRITE |(< x (+ c/d y))|))
 (80 80 (:REWRITE |(* 0 x)|))
 (76 19 (:REWRITE RATIONALP-X))
 (63 7 (:REWRITE |(y86-p (w32 addr val s))|))
 (40 40 (:REWRITE |(< y (+ (- c) x))|))
 (25 25
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (19 19 (:REWRITE REDUCE-RATIONALP-+))
 (19 19 (:REWRITE REDUCE-RATIONALP-*))
 (19 19 (:REWRITE RATIONALP-MINUS-X))
 (19 19 (:META META-RATIONALP-CORRECT))
 (16 16
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(SEC_NOT_PRESENT-MODIFY-LOOP)
(SEC_NOT_PRESENT-MODIFY)
(|(paging-p (sec_not_present-modify s))|
 (272409 1357 (:DEFINITION BINARY-LOGAND))
 (157788 3578
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (48687 23788 (:REWRITE DEFAULT-+-2))
 (42681 23788 (:REWRITE DEFAULT-+-1))
 (38154 3578 (:DEFINITION NFIX))
 (26723 1357 (:REWRITE ZIP-OPEN))
 (23029 9020 (:REWRITE DEFAULT-<-1))
 (20878 9197 (:REWRITE DEFAULT-*-2))
 (18301 9020 (:REWRITE DEFAULT-<-2))
 (18010 7106 (:REWRITE DEFAULT-UNARY-MINUS))
 (10377 9197 (:REWRITE DEFAULT-*-1))
 (9435 2630 (:REWRITE DEFAULT-NUMERATOR))
 (9360 1357 (:REWRITE O-INFP->NEQ-0))
 (8699 2374 (:REWRITE DEFAULT-DENOMINATOR))
 (3747 3747
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (3747 3747
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (535 535
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (464 58 (:REWRITE ASSOCIATIVITY-OF-+))
 (400 44
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (210 88
      (:REWRITE |(good-32-address-p addr st)|))
 (210 44
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (176 176
      (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (136
  68
  (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|)))
(|(va-to-pa addr (sec_not_present-modify s))|
 (281796 1436 (:DEFINITION BINARY-LOGAND))
 (160316 3736
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (49793 24578 (:REWRITE DEFAULT-+-2))
 (43629 24578 (:REWRITE DEFAULT-+-1))
 (38628 3736 (:DEFINITION NFIX))
 (29290 1436 (:REWRITE ZIP-OPEN))
 (23914 9494 (:REWRITE DEFAULT-<-1))
 (21194 9434 (:REWRITE DEFAULT-*-2))
 (18775 9494 (:REWRITE DEFAULT-<-2))
 (18405 7422 (:REWRITE DEFAULT-UNARY-MINUS))
 (14438 44
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (14316 88
        (:REWRITE |(good-32-address-p addr st)|))
 (13928 44 (:REWRITE |(n32p x)|))
 (10614 9434 (:REWRITE DEFAULT-*-1))
 (10302
   68
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (10242 1436 (:REWRITE O-INFP->NEQ-0))
 (9583 79 (:LINEAR BINARY-LOGAND->=-0))
 (9514 2709 (:REWRITE DEFAULT-NUMERATOR))
 (8778 2453 (:REWRITE DEFAULT-DENOMINATOR))
 (3747 3747
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (3747 3747
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (3688 35 (:LINEAR BINARY-LOGAND-<=))
 (2884 35 (:DEFINITION NATP))
 (1459 1459 (:TYPE-PRESCRIPTION VA-TO-PA))
 (535 535
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (464 58 (:REWRITE ASSOCIATIVITY-OF-+))
 (210 70
      (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (210 44
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (176 176
      (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (88 88 (:TYPE-PRESCRIPTION N32P))
 (44 44
     (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (44 44
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (35 35 (:TYPE-PRESCRIPTION NATP)))
(|(good-32-address-p addr (sec_not_present-modify s))|
 (309000 1664 (:DEFINITION BINARY-LOGAND))
 (167612 4192
         (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (53265 27050 (:REWRITE DEFAULT-+-2))
 (46557 27050 (:REWRITE DEFAULT-+-1))
 (42604
   68
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (39996 4192 (:DEFINITION NFIX))
 (37476 44
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (37389 307 (:LINEAR BINARY-LOGAND->=-0))
 (36766 1664 (:REWRITE ZIP-OPEN))
 (26983 11007 (:REWRITE DEFAULT-<-1))
 (23284 44
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (22106 10118 (:REWRITE DEFAULT-*-2))
 (20288 11007 (:REWRITE DEFAULT-<-2))
 (19545 8334 (:REWRITE DEFAULT-UNARY-MINUS))
 (18440 175 (:LINEAR BINARY-LOGAND-<=))
 (14420 175 (:DEFINITION NATP))
 (14287 90
        (:REWRITE |(good-32-address-p addr st)|))
 (12810 1664 (:REWRITE O-INFP->NEQ-0))
 (11298 10118 (:REWRITE DEFAULT-*-1))
 (9742 2937 (:REWRITE DEFAULT-NUMERATOR))
 (9006 2681 (:REWRITE DEFAULT-DENOMINATOR))
 (3747 3747
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (3747 3747 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (3747 3747
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1050 350
       (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (535 535
      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (464 58 (:REWRITE ASSOCIATIVITY-OF-+))
 (175 175 (:TYPE-PRESCRIPTION NATP))
 (24 4
     (:REWRITE |(n32p (va-to-pa addr st))| . 1))
 (16 8
     (:REWRITE |(integerp (va-to-pa addr st))| . 2))
 (12 4
     (:REWRITE |(n32p (va-to-pa addr st))| . 2))
 (12 4
     (:REWRITE |(integerp (va-to-pa addr st))| . 1)))
(CROCK-100 (590 10 (:REWRITE DEFAULT-PLUS-1))
           (588 10 (:REWRITE DEFAULT-PLUS-2))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
           (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
           (192 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
           (106 2 (:REWRITE CANCEL-FLOOR-+))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
           (69 2 (:REWRITE FLOOR-ZERO . 3))
           (53 7 (:REWRITE INTEGERP-MINUS-X))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
           (36 2 (:REWRITE FLOOR-ZERO . 5))
           (34 4 (:REWRITE |(* (- x) y)|))
           (32 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
           (31 2 (:REWRITE FLOOR-ZERO . 4))
           (24 24 (:REWRITE DEFAULT-TIMES-2))
           (24 24 (:REWRITE DEFAULT-TIMES-1))
           (23 2 (:REWRITE FLOOR-=-X/Y . 3))
           (23 2 (:REWRITE FLOOR-=-X/Y . 2))
           (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
           (20 4 (:REWRITE DEFAULT-MINUS))
           (18 6
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (18 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (18 6 (:REWRITE DEFAULT-LESS-THAN-1))
           (18 4 (:REWRITE |(- (* c x))|))
           (13 13
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (10 2 (:REWRITE FLOOR-ZERO . 2))
           (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
           (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
           (10 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
           (10 2
               (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
           (10 2
               (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
           (9 6
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (9 6
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (8 8 (:REWRITE THE-FLOOR-BELOW))
           (6 6 (:TYPE-PRESCRIPTION ABS))
           (6 6 (:REWRITE SIMPLIFY-SUMS-<))
           (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (6 6 (:REWRITE INTEGERP-<-CONSTANT))
           (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
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
           (6 2 (:REWRITE FLOOR-CANCEL-*-CONST))
           (5 5 (:REWRITE REDUCE-INTEGERP-+))
           (5 5 (:META META-INTEGERP-CORRECT))
           (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (4 1 (:REWRITE |(n32p x)|))
           (2 2
              (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
           (2 2 (:REWRITE DEFAULT-FLOOR-2))
           (2 2 (:REWRITE DEFAULT-FLOOR-1))
           (2 2 (:REWRITE |(floor x (- y))| . 2))
           (2 2 (:REWRITE |(floor x (- y))| . 1))
           (2 2
              (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
           (2 2
              (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
           (2 2 (:REWRITE |(floor (- x) y)| . 2))
           (2 2 (:REWRITE |(floor (- x) y)| . 1))
           (2 2
              (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
           (1 1 (:REWRITE |(< 0 (/ x))|))
           (1 1 (:REWRITE |(< 0 (* x y))|))
           (1 1 (:REWRITE |(< (/ x) 0)|))
           (1 1
              (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
           (1 1 (:REWRITE |(< (* x y) 0)|))
           (1 1
              (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
           (1 1
              (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(CROCK-101
 (4784 104 (:REWRITE |(* (* x y) z)|))
 (2494 450 (:REWRITE DEFAULT-TIMES-1))
 (2448 450 (:REWRITE DEFAULT-TIMES-2))
 (2426 17 (:REWRITE FLOOR-ZERO . 3))
 (2321 17 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2188 17 (:REWRITE CANCEL-FLOOR-+))
 (2050
  2050
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2050
      2050
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2050
     2050
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2050 2050
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2014 69 (:REWRITE THE-FLOOR-ABOVE))
 (1829 17 (:REWRITE FLOOR-ZERO . 4))
 (1649 17 (:REWRITE FLOOR-ZERO . 5))
 (1474 17 (:REWRITE FLOOR-=-X/Y . 3))
 (1468 17 (:REWRITE FLOOR-=-X/Y . 2))
 (1128 17 (:REWRITE |(* (- x) y)|))
 (1111 17 (:REWRITE DEFAULT-FLOOR-RATIO))
 (830 15 (:REWRITE |(+ y x)|))
 (679 7 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (616 7 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (577 64 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (527 17 (:REWRITE |(integerp (- x))|))
 (496 16 (:REWRITE |(floor x 1)|))
 (493 37 (:REWRITE DEFAULT-PLUS-1))
 (487 37 (:REWRITE DEFAULT-PLUS-2))
 (460 64 (:REWRITE DEFAULT-LESS-THAN-1))
 (334 37
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (329 17 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (243 27
      (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (243 27
      (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
 (243 27
      (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
 (185 17 (:REWRITE FLOOR-ZERO . 2))
 (185 17 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (185 17 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (181 64 (:REWRITE DEFAULT-LESS-THAN-2))
 (177 24 (:REWRITE DEFAULT-MINUS))
 (161 17 (:REWRITE DEFAULT-FLOOR-1))
 (136 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (131 17 (:REWRITE FLOOR-CANCEL-*-CONST))
 (107 17
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (106 16
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (93 93 (:REWRITE REDUCE-INTEGERP-+))
 (93 93 (:REWRITE INTEGERP-MINUS-X))
 (93 93 (:META META-INTEGERP-CORRECT))
 (86 17
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (82 64 (:REWRITE SIMPLIFY-SUMS-<))
 (77 77 (:REWRITE |arith (expt x c)|))
 (77 77 (:REWRITE |arith (expt 1/c n)|))
 (70 16
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (69 69 (:REWRITE THE-FLOOR-BELOW))
 (64 64
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (64 64 (:REWRITE INTEGERP-<-CONSTANT))
 (64 64 (:REWRITE CONSTANT-<-INTEGERP))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< c (- x))|))
 (64 64
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (64 64
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< (/ x) (/ y))|))
 (64 64 (:REWRITE |(< (- x) c)|))
 (64 64 (:REWRITE |(< (- x) (- y))|))
 (55 11 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (50 50
     (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (50 5 (:REWRITE |(+ 0 x)|))
 (41 41
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (37 11 (:LINEAR EXPT->=-1-ONE))
 (37 11 (:LINEAR EXPT->-1-ONE))
 (36 36 (:REWRITE |arith (* c (* d x))|))
 (35 5 (:REWRITE |(/ (expt x n))|))
 (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 17 (:REWRITE DEFAULT-FLOOR-2))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (22 22
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (18 18 (:REWRITE |arith (- (* c x))|))
 (18 18 (:REWRITE |arith (* (- x) y)|))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(floor x (- y))| . 2))
 (17 17 (:REWRITE |(floor x (- y))| . 1))
 (17 17 (:REWRITE |(floor (- x) y)| . 2))
 (17 17 (:REWRITE |(floor (- x) y)| . 1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (17 17 (:REWRITE |(- (* c x))|))
 (16 16
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15 15
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (11 11
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (11 11 (:LINEAR EXPT-X->=-X))
 (11 11 (:LINEAR EXPT-X->-X))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:LINEAR EXPT->=-1-TWO))
 (11 11 (:LINEAR EXPT->-1-TWO))
 (11 11 (:LINEAR EXPT-<=-1-ONE))
 (11 11 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE |(- (- x))|))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS)))
(CROCK-102 (14 2 (:REWRITE DEFAULT-FLOOR-RATIO))
           (8 8 (:REWRITE DEFAULT-TIMES-2))
           (8 8 (:REWRITE DEFAULT-TIMES-1))
           (6 4
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (6 4
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (4 4 (:TYPE-PRESCRIPTION ABS))
           (4 4 (:REWRITE THE-FLOOR-BELOW))
           (4 4 (:REWRITE THE-FLOOR-ABOVE))
           (4 4 (:REWRITE SIMPLIFY-SUMS-<))
           (4 4
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (4 4
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (2 2 (:REWRITE DEFAULT-FLOOR-2))
           (2 2 (:REWRITE DEFAULT-FLOOR-1))
           (2 2 (:REWRITE |(< (/ x) 0)|))
           (2 2 (:REWRITE |(< (* x y) 0)|))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1
              (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
           (1 1 (:META META-INTEGERP-CORRECT)))
(CROCK-103 (124 4 (:LINEAR CROCK-102))
           (7 1 (:REWRITE DEFAULT-FLOOR-RATIO))
           (5 5 (:REWRITE DEFAULT-TIMES-2))
           (5 5 (:REWRITE DEFAULT-TIMES-1))
           (4 4 (:REWRITE THE-FLOOR-BELOW))
           (4 4 (:REWRITE THE-FLOOR-ABOVE))
           (4 4
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (4 4
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (4 4 (:REWRITE SIMPLIFY-SUMS-<))
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
           (4 4 (:REWRITE |(< (/ x) 0)|))
           (4 4 (:REWRITE |(< (/ x) (/ y))|))
           (4 4 (:REWRITE |(< (- x) c)|))
           (4 4 (:REWRITE |(< (- x) (- y))|))
           (4 4 (:REWRITE |(< (* x y) 0)|))
           (3 3
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1 (:REWRITE DEFAULT-FLOOR-2))
           (1 1 (:REWRITE DEFAULT-FLOOR-1))
           (1 1 (:META META-INTEGERP-CORRECT)))
(CROCK-200
 (190 190
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (175 5 (:REWRITE MOD-X-Y-=-X . 4))
 (110 5 (:REWRITE MOD-ZERO . 3))
 (90 5 (:REWRITE MOD-ZERO . 4))
 (55 5 (:REWRITE DEFAULT-MOD-RATIO))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40 10 (:REWRITE |(* y x)|))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (23 19 (:REWRITE DEFAULT-LOGAND-2))
 (20 20 (:REWRITE DEFAULT-TIMES-2))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:REWRITE DEFAULT-LOGAND-1))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-MOD-2))
 (5 5 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
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
 (5 5 (:META META-INTEGERP-CORRECT)))
(CROCK-203 (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
           (311 7 (:REWRITE DEFAULT-PLUS-1))
           (310 7 (:REWRITE DEFAULT-PLUS-2))
           (302 302
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
           (257 3 (:REWRITE FLOOR-ZERO . 3))
           (231 3 (:REWRITE CANCEL-FLOOR-+))
           (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
           (198 3 (:REWRITE FLOOR-X-Y-=-1 . 2))
           (163 3 (:REWRITE FLOOR-ZERO . 5))
           (157 3 (:REWRITE FLOOR-ZERO . 4))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
           (114 15 (:REWRITE INTEGERP-MINUS-X))
           (98 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (97 47 (:REWRITE DEFAULT-TIMES-2))
           (96 3 (:REWRITE FLOOR-=-X/Y . 3))
           (96 3 (:REWRITE FLOOR-=-X/Y . 2))
           (91 47 (:REWRITE DEFAULT-TIMES-1))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
           (75 6 (:REWRITE |(* (- x) y)|))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
           (51 3 (:REWRITE DEFAULT-FLOOR-RATIO))
           (48 8 (:LINEAR BINARY-LOGAND->=-0))
           (48 8 (:LINEAR BINARY-LOGAND-<=))
           (43 11
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (43 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (42 6 (:REWRITE DEFAULT-MINUS))
           (39 6 (:REWRITE |(- (* c x))|))
           (38 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
           (37 37 (:REWRITE LOGAND-CONSTANT-MASK))
           (37 37 (:REWRITE DEFAULT-LOGAND-2))
           (37 37 (:REWRITE DEFAULT-LOGAND-1))
           (33 11 (:REWRITE DEFAULT-LESS-THAN-1))
           (32 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
           (27 3 (:REWRITE FLOOR-X-Y-=--1 . 2))
           (25 25
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (21 11 (:REWRITE DEFAULT-LESS-THAN-2))
           (21 3 (:REWRITE FLOOR-ZERO . 2))
           (21 3 (:REWRITE FLOOR-X-Y-=-1 . 3))
           (21 3 (:REWRITE FLOOR-X-Y-=--1 . 3))
           (15 3
               (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
           (15 3 (:REWRITE FLOOR-CANCEL-*-CONST))
           (15 3
               (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
           (14 11
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (14 11
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (12 12 (:REWRITE REDUCE-INTEGERP-+))
           (12 12 (:META META-INTEGERP-CORRECT))
           (11 11 (:REWRITE THE-FLOOR-ABOVE))
           (11 11 (:REWRITE SIMPLIFY-SUMS-<))
           (11 11
               (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (11 11
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (11 11 (:REWRITE INTEGERP-<-CONSTANT))
           (11 11 (:REWRITE CONSTANT-<-INTEGERP))
           (11 11
               (:REWRITE |(< c (/ x)) positive c --- present in goal|))
           (11 11
               (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
           (11 11
               (:REWRITE |(< c (/ x)) negative c --- present in goal|))
           (11 11
               (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
           (11 11 (:REWRITE |(< c (- x))|))
           (11 11
               (:REWRITE |(< (/ x) c) positive c --- present in goal|))
           (11 11
               (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
           (11 11
               (:REWRITE |(< (/ x) c) negative c --- present in goal|))
           (11 11
               (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
           (11 11 (:REWRITE |(< (/ x) (/ y))|))
           (11 11 (:REWRITE |(< (- x) c)|))
           (11 11 (:REWRITE |(< (- x) (- y))|))
           (10 10 (:LINEAR LOGAND-BOUNDS-NEG . 2))
           (10 10 (:LINEAR LOGAND-BOUNDS-NEG . 1))
           (10 2
               (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
           (9 3
              (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
           (9 3 (:REWRITE DEFAULT-FLOOR-1))
           (9 3
              (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
           (6 6 (:TYPE-PRESCRIPTION ABS))
           (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (6 2
              (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
           (3 3 (:REWRITE DEFAULT-FLOOR-2))
           (3 3 (:REWRITE |(floor x (- y))| . 2))
           (3 3 (:REWRITE |(floor x (- y))| . 1))
           (3 3
              (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
           (3 3
              (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
           (3 3 (:REWRITE |(floor (- x) y)| . 2))
           (3 3 (:REWRITE |(floor (- x) y)| . 1))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
           (2 2 (:REWRITE |(< 0 (/ x))|))
           (2 2 (:REWRITE |(< 0 (* x y))|))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (1 1
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (1 1 (:REWRITE |(< (/ x) 0)|))
           (1 1 (:REWRITE |(< (* x y) 0)|)))
(CROCK-2000)
(CROCK-2001-3
 (17550 4 (:REWRITE FLOOR-=-X/Y . 4))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4993 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3278 49 (:REWRITE FLOOR-ZERO . 3))
 (3224 843 (:REWRITE DEFAULT-TIMES-2))
 (3185 75 (:REWRITE DEFAULT-PLUS-2))
 (2822 49 (:REWRITE CANCEL-FLOOR-+))
 (2801 75 (:REWRITE DEFAULT-PLUS-1))
 (2299 12 (:REWRITE MOD-X-Y-=-X . 3))
 (2154 49 (:REWRITE FLOOR-ZERO . 5))
 (2113 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2084 176 (:REWRITE INTEGERP-MINUS-X))
 (2020 49 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2013 12 (:REWRITE MOD-X-Y-=-X . 4))
 (1975 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1975 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1871 12 (:REWRITE CANCEL-MOD-+))
 (1870 49 (:REWRITE FLOOR-ZERO . 4))
 (1855 162 (:REWRITE THE-FLOOR-ABOVE))
 (1723 12 (:REWRITE MOD-ZERO . 4))
 (1594 14
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1516 8 (:LINEAR MOD-BOUNDS-1))
 (1513 126 (:REWRITE |(* (- x) y)|))
 (1473 843 (:REWRITE DEFAULT-TIMES-1))
 (1004 124 (:REWRITE DEFAULT-MINUS))
 (924 49 (:REWRITE FLOOR-=-X/Y . 3))
 (904 49 (:REWRITE FLOOR-=-X/Y . 2))
 (821 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (686 686
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (603 12 (:REWRITE MOD-ZERO . 3))
 (595 117 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (595 117 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (591 49 (:REWRITE DEFAULT-FLOOR-RATIO))
 (576 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (575 117
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (575 117
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (507 160
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (507 160
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (453 453
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (417 12 (:REWRITE DEFAULT-MOD-RATIO))
 (374 160 (:REWRITE DEFAULT-LESS-THAN-1))
 (356 162 (:REWRITE THE-FLOOR-BELOW))
 (325 49 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (293 160 (:REWRITE DEFAULT-LESS-THAN-2))
 (293 18 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (285 49 (:REWRITE FLOOR-ZERO . 2))
 (285 49 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (285 49 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (251 49 (:REWRITE FLOOR-CANCEL-*-CONST))
 (250 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (250 12 (:REWRITE MOD-X-Y-=-X . 2))
 (250 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (250 12
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (196 160
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (196 160
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (178 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (177 49
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (176 48
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (160 160 (:REWRITE SIMPLIFY-SUMS-<))
 (160 160
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (160 160
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (160 160 (:REWRITE INTEGERP-<-CONSTANT))
 (160 160 (:REWRITE CONSTANT-<-INTEGERP))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< c (- x))|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< (/ x) (/ y))|))
 (160 160 (:REWRITE |(< (- x) c)|))
 (160 160 (:REWRITE |(< (- x) (- y))|))
 (159 23
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (157 49
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (155 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (155 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (155 12 (:REWRITE MOD-CANCEL-*-CONST))
 (124 48
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (123 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (121 121
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (121 121
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (117 117 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (117 117
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (117 117
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (117 117
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (115 115 (:REWRITE REDUCE-INTEGERP-+))
 (115 115 (:META META-INTEGERP-CORRECT))
 (112 112 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (110 34
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (107 12 (:REWRITE DEFAULT-MOD-1))
 (104 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (89 49 (:REWRITE DEFAULT-FLOOR-1))
 (86 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (86 86 (:REWRITE DEFAULT-LOGAND-2))
 (86 86 (:REWRITE DEFAULT-LOGAND-1))
 (81 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (72 72 (:TYPE-PRESCRIPTION ABS))
 (72 34
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (49 49 (:REWRITE DEFAULT-FLOOR-2))
 (48 48 (:REWRITE |(floor x (- y))| . 2))
 (48 48 (:REWRITE |(floor x (- y))| . 1))
 (48 48
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (48 48
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (48 48 (:REWRITE |(floor (- x) y)| . 2))
 (48 48 (:REWRITE |(floor (- x) y)| . 1))
 (44 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (43 11
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (42 42 (:REWRITE |(< 0 (* x y))|))
 (40 8 (:LINEAR MOD-BOUNDS-2))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (23
   23
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (23
  23
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (23 11
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (22 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (21 21 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (21 21 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (20 4 (:LINEAR MOD-BOUNDS-3))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (12 12 (:REWRITE DEFAULT-MOD-2))
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
 (9 1 (:REWRITE MOD-POSITIVE . 3))
 (9 1 (:REWRITE FLOOR-POSITIVE . 2))
 (9 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 1 (:REWRITE MOD-NONPOSITIVE))
 (5 1 (:REWRITE FLOOR-POSITIVE . 4))
 (5 1 (:REWRITE FLOOR-POSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE MOD-POSITIVE . 2))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE FLOOR-ZERO . 1))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(CROCK-2001
 (111775 104
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80759 35 (:REWRITE |(equal (+ (- c) x) y)|))
 (71193 71193
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (71193 71193
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (60783 711 (:REWRITE DEFAULT-PLUS-2))
 (43680 16 (:REWRITE FLOOR-=-X/Y . 4))
 (33111 2547
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (32890 711 (:REWRITE DEFAULT-PLUS-1))
 (27711 175 (:REWRITE FLOOR-ZERO . 3))
 (22923 2547
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (22923 2547
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (22923 2547
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (19323 175 (:REWRITE FLOOR-ZERO . 4))
 (18397 5937
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (16980 175 (:REWRITE FLOOR-ZERO . 5))
 (16640 175 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (15466 290 (:REWRITE CANCEL-MOD-+))
 (15235 3047 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (15235 3047 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (15075 3047
        (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (15075 3047
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (14982 5102 (:REWRITE DEFAULT-TIMES-2))
 (14952 1490 (:REWRITE INTEGERP-MINUS-X))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (12735 2547
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (10405 797
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10123 953 (:REWRITE |(* (- x) y)|))
 (9610 104
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8630 5102 (:REWRITE DEFAULT-TIMES-1))
 (8150 800 (:REWRITE DEFAULT-LESS-THAN-1))
 (7518 175 (:REWRITE FLOOR-=-X/Y . 2))
 (7322 175 (:REWRITE FLOOR-=-X/Y . 3))
 (7219 305 (:REWRITE MOD-X-Y-=-X . 4))
 (7004 953 (:REWRITE DEFAULT-MINUS))
 (6405 41
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6321 305 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6237 305 (:REWRITE MOD-ZERO . 4))
 (5986 177 (:REWRITE DEFAULT-FLOOR-RATIO))
 (5937 5937
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5937 5937
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5937 5937
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5742 64 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5151 783
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4531 175 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3905 305 (:REWRITE DEFAULT-MOD-RATIO))
 (3756 7 (:REWRITE |(floor (+ x r) i)|))
 (3636 46 (:REWRITE |(* x (+ y z))|))
 (3361 305 (:REWRITE MOD-ZERO . 3))
 (3047 3047 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (3047 3047 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3047 3047
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3047 3047
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3047 3047
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3047 3047
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2916 800 (:REWRITE DEFAULT-LESS-THAN-2))
 (2821 2821
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2220 1020 (:META META-INTEGERP-CORRECT))
 (1861 305 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1816 296 (:REWRITE MOD-X-Y-=-X . 2))
 (1816 296
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1693 305 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1693 305 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1556 60 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1422 290 (:REWRITE MOD-CANCEL-*-CONST))
 (1350 270 (:LINEAR MOD-BOUNDS-2))
 (1323 175 (:REWRITE FLOOR-ZERO . 2))
 (1323 175 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1323 175 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1316 60 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1306 290
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1306 290
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1173 173 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1020 1020 (:REWRITE REDUCE-INTEGERP-+))
 (978 2 (:REWRITE |(* (if a b c) x)|))
 (961 177 (:REWRITE DEFAULT-FLOOR-1))
 (938 797
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (938 797
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (865 135 (:LINEAR MOD-BOUNDS-3))
 (841 173
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (812 140
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (785 785
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (785 785 (:REWRITE INTEGERP-<-CONSTANT))
 (785 785 (:REWRITE CONSTANT-<-INTEGERP))
 (785 785
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (785 785
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (785 785
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (785 785
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (785 785 (:REWRITE |(< c (- x))|))
 (785 785
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (785 785
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (785 785
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (785 785
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (785 785 (:REWRITE |(< (/ x) (/ y))|))
 (785 785 (:REWRITE |(< (- x) c)|))
 (785 785 (:REWRITE |(< (- x) (- y))|))
 (645 173
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (632 160
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (476 140
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (473 305 (:REWRITE DEFAULT-MOD-1))
 (434 290
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (434 290
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (412 160
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (356 120
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (305 305 (:REWRITE DEFAULT-MOD-2))
 (294 294 (:TYPE-PRESCRIPTION ABS))
 (290 290 (:REWRITE |(mod x (- y))| . 3))
 (290 290 (:REWRITE |(mod x (- y))| . 2))
 (290 290 (:REWRITE |(mod x (- y))| . 1))
 (290 290
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (290 290
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (290 290 (:REWRITE |(mod (- x) y)| . 3))
 (290 290 (:REWRITE |(mod (- x) y)| . 2))
 (290 290 (:REWRITE |(mod (- x) y)| . 1))
 (288 3 (:REWRITE O-INFP->NEQ-0))
 (246 246
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (192 192 (:REWRITE |(< 0 (* x y))|))
 (190 190
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (190 190
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (190 190 (:REWRITE |(< 0 (/ x))|))
 (177 177 (:REWRITE DEFAULT-FLOOR-2))
 (162 18 (:REWRITE MOD-POSITIVE . 3))
 (160 160 (:REWRITE |(floor x (- y))| . 2))
 (160 160 (:REWRITE |(floor x (- y))| . 1))
 (160 160
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (160 160
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (160 160 (:REWRITE |(floor (- x) y)| . 2))
 (160 160 (:REWRITE |(floor (- x) y)| . 1))
 (110 110
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (104 104
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (104 104 (:REWRITE |(equal c (/ x))|))
 (104 104 (:REWRITE |(equal c (- x))|))
 (104 104 (:REWRITE |(equal (/ x) c)|))
 (104 104 (:REWRITE |(equal (/ x) (/ y))|))
 (104 104 (:REWRITE |(equal (- x) c)|))
 (104 104 (:REWRITE |(equal (- x) (- y))|))
 (98 8 (:REWRITE |(n32p x)|))
 (90 18 (:REWRITE MOD-NONPOSITIVE))
 (80 2 (:LINEAR CROCK-100))
 (75 15
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (63 63 (:REWRITE FOLD-CONSTS-IN-+))
 (56 56 (:REWRITE |(< (+ c/d x) y)|))
 (54 6 (:REWRITE MOD-ZERO . 1))
 (46 46 (:REWRITE |(< (+ (- c) x) y)|))
 (40 40 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (30 6 (:REWRITE MOD-ZERO . 2))
 (18 18 (:REWRITE MOD-POSITIVE . 2))
 (18 18 (:REWRITE MOD-POSITIVE . 1))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (6 6 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (6 6 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (6 6 (:REWRITE DEFAULT-LOGAND-2))
 (6 6 (:REWRITE DEFAULT-LOGAND-1))
 (6 6
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (5
   5
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 5
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (5 5
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(equal (* x y) 0)|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(|(y86-p (sec_not_present-modify s))|
 (12739 5
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (7425 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (3623 1121 (:REWRITE DEFAULT-PLUS-2))
 (3360 72
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3298
  13
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (3198
   20
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (3178 20
       (:REWRITE |(good-32-address-p addr st)|))
 (3093 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (1979 1121 (:REWRITE DEFAULT-PLUS-1))
 (1902 65 (:REWRITE |(+ y (+ x z))|))
 (1773
  13
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (1676 49 (:REWRITE SIMPLIFY-SUMS-<))
 (1531 1531
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1449 5 (:REWRITE DISJOINT-3-ITEMS))
 (1196 716 (:REWRITE NORMALIZE-ADDENDS))
 (696 696
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (557 8
      (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (512 171 (:REWRITE DEFAULT-LOGAND-2))
 (511
  23
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (342 342
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (342 342 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (342 342 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (342 342
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (215 72 (:REWRITE DEFAULT-LESS-THAN-1))
 (198 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (192 130 (:REWRITE DEFAULT-TIMES-2))
 (183 171 (:REWRITE DEFAULT-LOGAND-1))
 (180 10 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (171 171 (:REWRITE LOGAND-CONSTANT-MASK))
 (156 72 (:REWRITE DEFAULT-LESS-THAN-2))
 (150 150 (:REWRITE FOLD-CONSTS-IN-+))
 (147
   147
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (147
  147
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (147 147
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (147
     147
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (147 147
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (147 147
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (130 130 (:REWRITE DEFAULT-TIMES-1))
 (112 112
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (99 24 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (99 24 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (72 72 (:REWRITE THE-FLOOR-BELOW))
 (72 72 (:REWRITE THE-FLOOR-ABOVE))
 (72 72
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (72 72
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (71 51
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (70 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (51 51 (:REWRITE INTEGERP-<-CONSTANT))
 (51 51 (:REWRITE CONSTANT-<-INTEGERP))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< c (- x))|))
 (51 51
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (51 51
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (51 51
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (51 51 (:REWRITE |(< (/ x) (/ y))|))
 (51 51 (:REWRITE |(< (- x) c)|))
 (51 51 (:REWRITE |(< (- x) (- y))|))
 (50 50 (:REWRITE |(< (+ c/d x) y)|))
 (40 32 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 10 (:REWRITE |(+ (* c x) (* d x))|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (31 31 (:REWRITE |(< (+ (- c) x) y)|))
 (29 29 (:TYPE-PRESCRIPTION SUBRANGEP))
 (28 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (28 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (22 22
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (20 20
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (20 10 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (20 10
     (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (19 19 (:REWRITE REDUCE-INTEGERP-+))
 (19 19 (:REWRITE INTEGERP-MINUS-X))
 (19 19 (:META META-INTEGERP-CORRECT))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(va-to-pa addr st)|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:REWRITE |(+ x (- x))|))
 (10 10 (:REWRITE |(* 0 x)|))
 (10 5
     (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (5 5 (:REWRITE |(< y (+ (- c) x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1
    (:TYPE-PRESCRIPTION Y86-SUPERVISOR-GUARD))
 (1 1
    (:TYPE-PRESCRIPTION Y86-REGISTER-GUARD))
 (1 1 (:TYPE-PRESCRIPTION Y86-FLAGS-GUARD)))
(|(memoryp (g :mem (sec_not_present-modify s)))|
 (16480 7
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (8450 7
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (5070
   28
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (5042 28
       (:REWRITE |(good-32-address-p addr st)|))
 (4923 7
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (4616
  17
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (4491 1331 (:REWRITE DEFAULT-PLUS-2))
 (3643 72
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2694 91 (:REWRITE |(+ y (+ x z))|))
 (2539 1331 (:REWRITE DEFAULT-PLUS-1))
 (2481
  17
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (2326 52 (:REWRITE SIMPLIFY-SUMS-<))
 (2325 7 (:REWRITE DISJOINT-3-ITEMS))
 (1878 1878
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1482 810 (:REWRITE NORMALIZE-ADDENDS))
 (1069 10
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (1007
  31
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (782 782
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (576 193 (:REWRITE DEFAULT-LOGAND-2))
 (348 348
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (348 348
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (252 14 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (217 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (205 193 (:REWRITE DEFAULT-LOGAND-1))
 (195 72 (:REWRITE DEFAULT-LESS-THAN-1))
 (193 193 (:REWRITE LOGAND-CONSTANT-MASK))
 (192 130 (:REWRITE DEFAULT-TIMES-2))
 (187 72 (:REWRITE DEFAULT-LESS-THAN-2))
 (186 186 (:REWRITE FOLD-CONSTS-IN-+))
 (139 34 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (139 34 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (130 130 (:REWRITE DEFAULT-TIMES-1))
 (108 108
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (98 28 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (94
   94
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (94
  94
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (94 94
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (74 54
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (72 72 (:REWRITE THE-FLOOR-BELOW))
 (72 72 (:REWRITE THE-FLOOR-ABOVE))
 (72 72
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (72 72
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 14 (:REWRITE |(+ (* c x) (* d x))|))
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
 (50 50 (:REWRITE |(< (+ c/d x) y)|))
 (43 43 (:TYPE-PRESCRIPTION SUBRANGEP))
 (39 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (34 34 (:REWRITE |(< (+ (- c) x) y)|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (31 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (31 16
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 28
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (28 14
     (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (26 26
     (:REWRITE |(g field (w32 addr val st))|))
 (22 22
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
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
 (14 14 (:REWRITE |(va-to-pa addr st)|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:REWRITE |(+ x (- x))|))
 (14 14 (:REWRITE |(* 0 x)|))
 (14 7
     (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (10 10
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (7 7 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< 0 (/ x))|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2
    (:REWRITE |(< x (/ y)) with (< y 0)|)))
(|(good-state-p (sec_not_present-modify s))|
 (27635 11
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (16149 11
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (14268 8973 (:REWRITE DEFAULT-PLUS-2))
 (10829 8973 (:REWRITE DEFAULT-PLUS-1))
 (7465
  238
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (7149 146
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6607 11
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (5158 4102 (:REWRITE NORMALIZE-ADDENDS))
 (4110
  238
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4058 4058
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3671 97 (:REWRITE SIMPLIFY-SUMS-<))
 (3435 11
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (3367 3367
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (3089 11 (:REWRITE DISJOINT-3-ITEMS))
 (969 323 (:REWRITE DEFAULT-LOGAND-2))
 (674 674
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (674 674 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (674 674 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (674 674
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (536
   536
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (536
  536
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (536 536
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (536
     536
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (536 536
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (536 536
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (451 146 (:REWRITE DEFAULT-LESS-THAN-1))
 (413 97 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (396 22 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (394 268 (:REWRITE DEFAULT-TIMES-2))
 (347 323 (:REWRITE DEFAULT-LOGAND-1))
 (327 146 (:REWRITE DEFAULT-LESS-THAN-2))
 (323 323 (:REWRITE LOGAND-CONSTANT-MASK))
 (312 312 (:REWRITE FOLD-CONSTS-IN-+))
 (268 268 (:REWRITE DEFAULT-TIMES-1))
 (222 222
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (171 42 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (171 42 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (154 44 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (146 146 (:REWRITE THE-FLOOR-BELOW))
 (146 146 (:REWRITE THE-FLOOR-ABOVE))
 (146 146
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (146 146
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (135 103
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (104 104 (:REWRITE |(< (+ c/d x) y)|))
 (103 103 (:REWRITE INTEGERP-<-CONSTANT))
 (103 103 (:REWRITE CONSTANT-<-INTEGERP))
 (103 103
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (103 103
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (103 103
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (103 103
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (103 103 (:REWRITE |(< c (- x))|))
 (103 103
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (103 103
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (103 103
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (103 103
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (103 103 (:REWRITE |(< (/ x) (/ y))|))
 (103 103 (:REWRITE |(< (- x) c)|))
 (103 103 (:REWRITE |(< (- x) (- y))|))
 (88 22 (:REWRITE |(+ (* c x) (* d x))|))
 (78 66 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (67 67 (:REWRITE |(< (+ (- c) x) y)|))
 (55 5 (:REWRITE DISJOINT-4-ITEMS))
 (51 26 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (51 26
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (51 26
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (44 44
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (44 22 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (44 22
     (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (28 28 (:REWRITE |(< (* x y) 0)|))
 (26 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (26 26 (:REWRITE |(equal c (/ x))|))
 (26 26 (:REWRITE |(equal c (- x))|))
 (26 26 (:REWRITE |(equal (/ x) c)|))
 (26 26 (:REWRITE |(equal (/ x) (/ y))|))
 (26 26 (:REWRITE |(equal (- x) c)|))
 (26 26 (:REWRITE |(equal (- x) (- y))|))
 (22 22 (:REWRITE |(va-to-pa addr st)|))
 (22 22 (:REWRITE |(< x (+ c/d y))|))
 (22 22 (:REWRITE |(+ x (- x))|))
 (22 22 (:REWRITE |(* 0 x)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (11 11
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (6 6
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (6 6 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|)))
(|(g :cr0 (sec_not_present-modify s))|
 (164510 4
         (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66391 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (50880 974 (:REWRITE DEFAULT-PLUS-2))
 (46109 24 (:REWRITE FLOOR-=-X/Y . 4))
 (41097 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (39602
   12
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (39586 12
        (:REWRITE |(good-32-address-p addr st)|))
 (33988 620
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28730 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (26249
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (24674 974 (:REWRITE DEFAULT-PLUS-1))
 (21582 2398
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (19639 31 (:REWRITE |(equal (+ (- c) x) y)|))
 (16899 2 (:REWRITE DISJOINT-3-ITEMS))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (14239
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (13694 601 (:REWRITE SIMPLIFY-SUMS-<))
 (13552 191 (:REWRITE CANCEL-FLOOR-+))
 (13118 191 (:REWRITE FLOOR-ZERO . 3))
 (12652 2799 (:REWRITE DEFAULT-TIMES-2))
 (11990 2398
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (9864 9864
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (9789 5
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (9758
  11
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (8105 727 (:REWRITE DEFAULT-LOGAND-2))
 (7740 191 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (7163 191 (:REWRITE FLOOR-ZERO . 4))
 (7108 191 (:REWRITE FLOOR-ZERO . 5))
 (7054 804 (:REWRITE INTEGERP-MINUS-X))
 (5212 2
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (4880 601
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4868 601
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4833 622 (:REWRITE DEFAULT-LESS-THAN-1))
 (4700 2799 (:REWRITE DEFAULT-TIMES-1))
 (4688 420 (:REWRITE |(* (- x) y)|))
 (4354 191 (:REWRITE FLOOR-=-X/Y . 2))
 (4339 191 (:REWRITE FLOOR-=-X/Y . 3))
 (3737 47
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3729 47
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2947 191 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2890 578
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2614 420 (:REWRITE DEFAULT-MINUS))
 (2494 420 (:REWRITE |(- (* c x))|))
 (2316 622 (:REWRITE DEFAULT-LESS-THAN-2))
 (2116 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1559 1559
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1527 191 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1282 35 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1241 191 (:REWRITE FLOOR-ZERO . 2))
 (1241 191 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1241 191 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1076 35 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1017 16 (:REWRITE CANCEL-MOD-+))
 (973 191
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (973 191
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (929 727 (:REWRITE DEFAULT-LOGAND-1))
 (792 191 (:REWRITE FLOOR-CANCEL-*-CONST))
 (746 620
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (727 727 (:REWRITE LOGAND-CONSTANT-MASK))
 (656 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (637 26 (:REWRITE MOD-X-Y-=-X . 4))
 (620 620
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (604 604 (:REWRITE INTEGERP-<-CONSTANT))
 (604 604 (:REWRITE CONSTANT-<-INTEGERP))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< c (- x))|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< (/ x) (/ y))|))
 (604 604 (:REWRITE |(< (- x) c)|))
 (604 604 (:REWRITE |(< (- x) (- y))|))
 (594 594 (:REWRITE REDUCE-INTEGERP-+))
 (594 594 (:META META-INTEGERP-CORRECT))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (578 578 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (574 126
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (477 191 (:REWRITE DEFAULT-FLOOR-1))
 (467 26 (:REWRITE MOD-ZERO . 3))
 (459 191
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 191
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (459 51
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (402 26 (:REWRITE MOD-ZERO . 4))
 (348 348
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (348 348
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (331 126
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (325 26 (:REWRITE DEFAULT-MOD-RATIO))
 (320 4 (:REWRITE |(+ (* c x) (* d x))|))
 (191 191 (:REWRITE DEFAULT-FLOOR-2))
 (191 191 (:REWRITE |(floor x (- y))| . 2))
 (191 191 (:REWRITE |(floor x (- y))| . 1))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (191 191 (:REWRITE |(floor (- x) y)| . 2))
 (191 191 (:REWRITE |(floor (- x) y)| . 1))
 (162 23
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (156 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (143 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (143 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (128 8 (:LINEAR MOD-BOUNDS-3))
 (124 124 (:REWRITE |(< 0 (/ x))|))
 (124 124 (:REWRITE |(< 0 (* x y))|))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (106 16 (:REWRITE MOD-X-Y-=-X . 2))
 (106 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (106 16
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (93 16
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (93 16 (:REWRITE MOD-CANCEL-*-CONST))
 (93 16
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (88 16 (:LINEAR MOD-BOUNDS-2))
 (83 83 (:REWRITE FOLD-CONSTS-IN-+))
 (67 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (55 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (47 47
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (47 47 (:REWRITE |(equal c (/ x))|))
 (47 47 (:REWRITE |(equal c (- x))|))
 (47 47 (:REWRITE |(equal (/ x) c)|))
 (47 47 (:REWRITE |(equal (/ x) (/ y))|))
 (47 47 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(equal (- x) (- y))|))
 (43 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (39 26 (:REWRITE DEFAULT-MOD-1))
 (37 37 (:REWRITE |(< (+ (- c) x) y)|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (21 21
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (17 17 (:TYPE-PRESCRIPTION SUBRANGEP))
 (16 16
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (16 16
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 3 (:REWRITE ACL2-NUMBERP-X))
 (8 4
    (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 3 (:REWRITE |(floor (+ x r) i)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(va-to-pa addr st)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(* 0 x)|))
 (4 2
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(|(g :eip (sec_not_present-modify s))|
 (164510 4
         (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66391 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (50880 974 (:REWRITE DEFAULT-PLUS-2))
 (46109 24 (:REWRITE FLOOR-=-X/Y . 4))
 (41097 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (39602
   12
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (39586 12
        (:REWRITE |(good-32-address-p addr st)|))
 (33988 620
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28730 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (26249
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (24674 974 (:REWRITE DEFAULT-PLUS-1))
 (21582 2398
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (19639 31 (:REWRITE |(equal (+ (- c) x) y)|))
 (16899 2 (:REWRITE DISJOINT-3-ITEMS))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (14239
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (13694 601 (:REWRITE SIMPLIFY-SUMS-<))
 (13552 191 (:REWRITE CANCEL-FLOOR-+))
 (13118 191 (:REWRITE FLOOR-ZERO . 3))
 (12652 2799 (:REWRITE DEFAULT-TIMES-2))
 (11990 2398
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (9864 9864
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (9789 5
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (9758
  11
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (8105 727 (:REWRITE DEFAULT-LOGAND-2))
 (7740 191 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (7163 191 (:REWRITE FLOOR-ZERO . 4))
 (7108 191 (:REWRITE FLOOR-ZERO . 5))
 (7054 804 (:REWRITE INTEGERP-MINUS-X))
 (5212 2
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (4880 601
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4868 601
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4833 622 (:REWRITE DEFAULT-LESS-THAN-1))
 (4700 2799 (:REWRITE DEFAULT-TIMES-1))
 (4688 420 (:REWRITE |(* (- x) y)|))
 (4354 191 (:REWRITE FLOOR-=-X/Y . 2))
 (4339 191 (:REWRITE FLOOR-=-X/Y . 3))
 (3737 47
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3729 47
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2947 191 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2890 578
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2614 420 (:REWRITE DEFAULT-MINUS))
 (2494 420 (:REWRITE |(- (* c x))|))
 (2316 622 (:REWRITE DEFAULT-LESS-THAN-2))
 (2116 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1559 1559
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1527 191 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1282 35 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1241 191 (:REWRITE FLOOR-ZERO . 2))
 (1241 191 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1241 191 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1076 35 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1017 16 (:REWRITE CANCEL-MOD-+))
 (973 191
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (973 191
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (929 727 (:REWRITE DEFAULT-LOGAND-1))
 (792 191 (:REWRITE FLOOR-CANCEL-*-CONST))
 (746 620
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (727 727 (:REWRITE LOGAND-CONSTANT-MASK))
 (656 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (637 26 (:REWRITE MOD-X-Y-=-X . 4))
 (620 620
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (604 604 (:REWRITE INTEGERP-<-CONSTANT))
 (604 604 (:REWRITE CONSTANT-<-INTEGERP))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< c (- x))|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< (/ x) (/ y))|))
 (604 604 (:REWRITE |(< (- x) c)|))
 (604 604 (:REWRITE |(< (- x) (- y))|))
 (594 594 (:REWRITE REDUCE-INTEGERP-+))
 (594 594 (:META META-INTEGERP-CORRECT))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (578 578 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (574 126
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (477 191 (:REWRITE DEFAULT-FLOOR-1))
 (467 26 (:REWRITE MOD-ZERO . 3))
 (459 191
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 191
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (459 51
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (402 26 (:REWRITE MOD-ZERO . 4))
 (351 351
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (351 351 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (351 351 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (351 351
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (331 126
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (325 26 (:REWRITE DEFAULT-MOD-RATIO))
 (320 4 (:REWRITE |(+ (* c x) (* d x))|))
 (191 191 (:REWRITE DEFAULT-FLOOR-2))
 (191 191 (:REWRITE |(floor x (- y))| . 2))
 (191 191 (:REWRITE |(floor x (- y))| . 1))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (191 191 (:REWRITE |(floor (- x) y)| . 2))
 (191 191 (:REWRITE |(floor (- x) y)| . 1))
 (162 23
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (156 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (143 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (143 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (128 8 (:LINEAR MOD-BOUNDS-3))
 (124 124 (:REWRITE |(< 0 (/ x))|))
 (124 124 (:REWRITE |(< 0 (* x y))|))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (106 16 (:REWRITE MOD-X-Y-=-X . 2))
 (106 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (106 16
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (93 16
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (93 16 (:REWRITE MOD-CANCEL-*-CONST))
 (93 16
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (88 16 (:LINEAR MOD-BOUNDS-2))
 (83 83 (:REWRITE FOLD-CONSTS-IN-+))
 (67 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (55 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (47 47
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (47 47 (:REWRITE |(equal c (/ x))|))
 (47 47 (:REWRITE |(equal c (- x))|))
 (47 47 (:REWRITE |(equal (/ x) c)|))
 (47 47 (:REWRITE |(equal (/ x) (/ y))|))
 (47 47 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(equal (- x) (- y))|))
 (43 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (39 26 (:REWRITE DEFAULT-MOD-1))
 (37 37 (:REWRITE |(< (+ (- c) x) y)|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (21 21
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (17 17 (:TYPE-PRESCRIPTION SUBRANGEP))
 (16 16
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (16 16
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 3 (:REWRITE ACL2-NUMBERP-X))
 (8 4
    (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 3 (:REWRITE |(floor (+ x r) i)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(va-to-pa addr st)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(* 0 x)|))
 (4 2
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (2 2
    (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(|(g :ebp (sec_not_present-modify s))|
 (164510 4
         (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66391 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (50880 974 (:REWRITE DEFAULT-PLUS-2))
 (46109 24 (:REWRITE FLOOR-=-X/Y . 4))
 (41097 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (39602
   12
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (39586 12
        (:REWRITE |(good-32-address-p addr st)|))
 (33988 620
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28730 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (26249
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (24674 974 (:REWRITE DEFAULT-PLUS-1))
 (21582 2398
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (19639 31 (:REWRITE |(equal (+ (- c) x) y)|))
 (16899 2 (:REWRITE DISJOINT-3-ITEMS))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (14239
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (13694 601 (:REWRITE SIMPLIFY-SUMS-<))
 (13552 191 (:REWRITE CANCEL-FLOOR-+))
 (13118 191 (:REWRITE FLOOR-ZERO . 3))
 (12652 2799 (:REWRITE DEFAULT-TIMES-2))
 (11990 2398
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (9864 9864
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (9789 5
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (9758
  11
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (8105 727 (:REWRITE DEFAULT-LOGAND-2))
 (7740 191 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (7163 191 (:REWRITE FLOOR-ZERO . 4))
 (7108 191 (:REWRITE FLOOR-ZERO . 5))
 (7054 804 (:REWRITE INTEGERP-MINUS-X))
 (5212 2
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (4880 601
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4868 601
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4833 622 (:REWRITE DEFAULT-LESS-THAN-1))
 (4700 2799 (:REWRITE DEFAULT-TIMES-1))
 (4688 420 (:REWRITE |(* (- x) y)|))
 (4354 191 (:REWRITE FLOOR-=-X/Y . 2))
 (4339 191 (:REWRITE FLOOR-=-X/Y . 3))
 (3737 47
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3729 47
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2947 191 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2890 578
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2614 420 (:REWRITE DEFAULT-MINUS))
 (2494 420 (:REWRITE |(- (* c x))|))
 (2316 622 (:REWRITE DEFAULT-LESS-THAN-2))
 (2116 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1559 1559
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1527 191 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1282 35 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1241 191 (:REWRITE FLOOR-ZERO . 2))
 (1241 191 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1241 191 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1076 35 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1017 16 (:REWRITE CANCEL-MOD-+))
 (973 191
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (973 191
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (929 727 (:REWRITE DEFAULT-LOGAND-1))
 (792 191 (:REWRITE FLOOR-CANCEL-*-CONST))
 (746 620
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (727 727 (:REWRITE LOGAND-CONSTANT-MASK))
 (656 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (637 26 (:REWRITE MOD-X-Y-=-X . 4))
 (620 620
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (604 604 (:REWRITE INTEGERP-<-CONSTANT))
 (604 604 (:REWRITE CONSTANT-<-INTEGERP))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< c (- x))|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< (/ x) (/ y))|))
 (604 604 (:REWRITE |(< (- x) c)|))
 (604 604 (:REWRITE |(< (- x) (- y))|))
 (594 594 (:REWRITE REDUCE-INTEGERP-+))
 (594 594 (:META META-INTEGERP-CORRECT))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (578 578 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (574 126
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (477 191 (:REWRITE DEFAULT-FLOOR-1))
 (467 26 (:REWRITE MOD-ZERO . 3))
 (459 191
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 191
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (459 51
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (402 26 (:REWRITE MOD-ZERO . 4))
 (348 348
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (348 348
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (331 126
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (325 26 (:REWRITE DEFAULT-MOD-RATIO))
 (320 4 (:REWRITE |(+ (* c x) (* d x))|))
 (191 191 (:REWRITE DEFAULT-FLOOR-2))
 (191 191 (:REWRITE |(floor x (- y))| . 2))
 (191 191 (:REWRITE |(floor x (- y))| . 1))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (191 191 (:REWRITE |(floor (- x) y)| . 2))
 (191 191 (:REWRITE |(floor (- x) y)| . 1))
 (162 23
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (156 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (143 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (143 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (128 8 (:LINEAR MOD-BOUNDS-3))
 (124 124 (:REWRITE |(< 0 (/ x))|))
 (124 124 (:REWRITE |(< 0 (* x y))|))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (106 16 (:REWRITE MOD-X-Y-=-X . 2))
 (106 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (106 16
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (93 16
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (93 16 (:REWRITE MOD-CANCEL-*-CONST))
 (93 16
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (88 16 (:LINEAR MOD-BOUNDS-2))
 (83 83 (:REWRITE FOLD-CONSTS-IN-+))
 (67 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (55 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (47 47
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (47 47 (:REWRITE |(equal c (/ x))|))
 (47 47 (:REWRITE |(equal c (- x))|))
 (47 47 (:REWRITE |(equal (/ x) c)|))
 (47 47 (:REWRITE |(equal (/ x) (/ y))|))
 (47 47 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(equal (- x) (- y))|))
 (43 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (39 26 (:REWRITE DEFAULT-MOD-1))
 (37 37 (:REWRITE |(< (+ (- c) x) y)|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (21 21
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (17 17 (:TYPE-PRESCRIPTION SUBRANGEP))
 (16 16
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (16 16
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 3 (:REWRITE ACL2-NUMBERP-X))
 (8 4
    (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 3 (:REWRITE |(floor (+ x r) i)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(va-to-pa addr st)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(* 0 x)|))
 (4 2
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (2 2
    (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(|(g :esp (sec_not_present-modify s))|
 (164510 4
         (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (66674 66674
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (66391 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (50883 977 (:REWRITE DEFAULT-PLUS-2))
 (46109 24 (:REWRITE FLOOR-=-X/Y . 4))
 (41097 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (39602
   12
   (:REWRITE |(good-32-address-p addr (sec_not_present-modify-loop-1 i s))|))
 (39586 12
        (:REWRITE |(good-32-address-p addr st)|))
 (33988 620
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28730 4
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (28593 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (26249
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (24677 977 (:REWRITE DEFAULT-PLUS-1))
 (21582 2398
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (19640 32 (:REWRITE |(equal (+ (- c) x) y)|))
 (16899 2 (:REWRITE DISJOINT-3-ITEMS))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (15885 3177
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (14239
  7
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (13694 601 (:REWRITE SIMPLIFY-SUMS-<))
 (13552 191 (:REWRITE CANCEL-FLOOR-+))
 (13118 191 (:REWRITE FLOOR-ZERO . 3))
 (12652 2799 (:REWRITE DEFAULT-TIMES-2))
 (11990 2398
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (9864 9864
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (9789 5
       (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (9758
  11
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (8105 727 (:REWRITE DEFAULT-LOGAND-2))
 (7740 191 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (7163 191 (:REWRITE FLOOR-ZERO . 4))
 (7108 191 (:REWRITE FLOOR-ZERO . 5))
 (7054 804 (:REWRITE INTEGERP-MINUS-X))
 (5212 2
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify-loop-1 i s)))|))
 (4880 601
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4868 601
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4833 622 (:REWRITE DEFAULT-LESS-THAN-1))
 (4700 2799 (:REWRITE DEFAULT-TIMES-1))
 (4688 420 (:REWRITE |(* (- x) y)|))
 (4354 191 (:REWRITE FLOOR-=-X/Y . 2))
 (4339 191 (:REWRITE FLOOR-=-X/Y . 3))
 (3737 47
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3729 47
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3527 3527
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2947 191 (:REWRITE DEFAULT-FLOOR-RATIO))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2890 578 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2890 578
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2614 420 (:REWRITE DEFAULT-MINUS))
 (2494 420 (:REWRITE |(- (* c x))|))
 (2316 622 (:REWRITE DEFAULT-LESS-THAN-2))
 (2116 24 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1559 1559
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1527 191 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1282 35 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1241 191 (:REWRITE FLOOR-ZERO . 2))
 (1241 191 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1241 191 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1191 158 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1076 35 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1017 16 (:REWRITE CANCEL-MOD-+))
 (973 191
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (973 191
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (929 727 (:REWRITE DEFAULT-LOGAND-1))
 (792 191 (:REWRITE FLOOR-CANCEL-*-CONST))
 (746 620
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (727 727 (:REWRITE LOGAND-CONSTANT-MASK))
 (656 26 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (637 26 (:REWRITE MOD-X-Y-=-X . 4))
 (623 623
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (604 604 (:REWRITE INTEGERP-<-CONSTANT))
 (604 604 (:REWRITE CONSTANT-<-INTEGERP))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< c (- x))|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (604 604
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (604 604 (:REWRITE |(< (/ x) (/ y))|))
 (604 604 (:REWRITE |(< (- x) c)|))
 (604 604 (:REWRITE |(< (- x) (- y))|))
 (594 594 (:REWRITE REDUCE-INTEGERP-+))
 (594 594 (:META META-INTEGERP-CORRECT))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (578 578
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (578 578 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (574 126
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (477 191 (:REWRITE DEFAULT-FLOOR-1))
 (467 26 (:REWRITE MOD-ZERO . 3))
 (459 191
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 191
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (459 51
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (402 26 (:REWRITE MOD-ZERO . 4))
 (348 348
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (348 348 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (348 348
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (331 126
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (325 26 (:REWRITE DEFAULT-MOD-RATIO))
 (320 4 (:REWRITE |(+ (* c x) (* d x))|))
 (191 191 (:REWRITE DEFAULT-FLOOR-2))
 (191 191 (:REWRITE |(floor x (- y))| . 2))
 (191 191 (:REWRITE |(floor x (- y))| . 1))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (191 191
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (191 191 (:REWRITE |(floor (- x) y)| . 2))
 (191 191 (:REWRITE |(floor (- x) y)| . 1))
 (162 23
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (156 26 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (143 26 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (143 26 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (128 8 (:LINEAR MOD-BOUNDS-3))
 (124 124 (:REWRITE |(< 0 (/ x))|))
 (124 124 (:REWRITE |(< 0 (* x y))|))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (123 123
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (106 16 (:REWRITE MOD-X-Y-=-X . 2))
 (106 16 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (106 16
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (93 16
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (93 16 (:REWRITE MOD-CANCEL-*-CONST))
 (93 16
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (88 16 (:LINEAR MOD-BOUNDS-2))
 (83 83 (:REWRITE FOLD-CONSTS-IN-+))
 (67 54
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (55 9 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (47 47
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (47 47 (:REWRITE |(equal c (/ x))|))
 (47 47 (:REWRITE |(equal c (- x))|))
 (47 47 (:REWRITE |(equal (/ x) c)|))
 (47 47 (:REWRITE |(equal (/ x) (/ y))|))
 (47 47 (:REWRITE |(equal (- x) c)|))
 (47 47 (:REWRITE |(equal (- x) (- y))|))
 (43 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (39 26 (:REWRITE DEFAULT-MOD-1))
 (37 37 (:REWRITE |(< (+ (- c) x) y)|))
 (33 3 (:REWRITE DISJOINT-4-ITEMS))
 (28
   28
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (28
  28
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (28 28
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (26 26 (:REWRITE DEFAULT-MOD-2))
 (21 21
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (17 17 (:TYPE-PRESCRIPTION SUBRANGEP))
 (16 16
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (16 16
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (16 16 (:REWRITE |(mod x (- y))| . 3))
 (16 16 (:REWRITE |(mod x (- y))| . 2))
 (16 16 (:REWRITE |(mod x (- y))| . 1))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (16 16
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (16 16 (:REWRITE |(mod (- x) y)| . 3))
 (16 16 (:REWRITE |(mod (- x) y)| . 2))
 (16 16 (:REWRITE |(mod (- x) y)| . 1))
 (16 16
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 3 (:REWRITE ACL2-NUMBERP-X))
 (8 4
    (:REWRITE |(va-to-pa addr (sec_not_present-modify-loop-1 i s))|))
 (6 6 (:REWRITE |(subrangep x x)|))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 3 (:REWRITE |(floor (+ x r) i)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(va-to-pa addr st)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(* 0 x)|))
 (4 2
    (:REWRITE |(paging-p (sec_not_present-modify-loop-1 i s))|))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (2 2
    (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(|(r32 addr (sec_not_present-modify s))|
 (37472 13
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (34702 17551 (:REWRITE DEFAULT-PLUS-2))
 (20996 17551 (:REWRITE DEFAULT-PLUS-1))
 (18747 13
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (13065 13065
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (12960 13
        (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (9077 18 (:REWRITE DISJOINT-3-ITEMS))
 (8930
  389
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (8498 222
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (8249 8249
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6639 140 (:REWRITE SIMPLIFY-SUMS-<))
 (5784 1580 (:REWRITE DEFAULT-LOGAND-2))
 (4965
  389
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (3551
   3551
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3551
  3551
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3551
      3551
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3551
     3551
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3551 3551
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3551 3551
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3482 101 (:REWRITE |(< (+ (- c) x) y)|))
 (2724 2724
       (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (2724 2724 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (2724 2724 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (2724 2724
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2340 2340
       (:REWRITE |(g field (w32 addr val st))|))
 (2340 4
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify s)))|))
 (2091 1513 (:REWRITE DEFAULT-TIMES-2))
 (1683 420 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (1683 420 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1628 1580 (:REWRITE DEFAULT-LOGAND-1))
 (1580 1580 (:REWRITE LOGAND-CONSTANT-MASK))
 (1513 1513 (:REWRITE DEFAULT-TIMES-1))
 (1448 1448
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1171 1171 (:REWRITE FOLD-CONSTS-IN-+))
 (692 222 (:REWRITE DEFAULT-LESS-THAN-1))
 (569 222 (:REWRITE DEFAULT-LESS-THAN-2))
 (486 28 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (391 391
      (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (322 80 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (291 13 (:REWRITE DISJOINT-4-ITEMS))
 (222 222 (:REWRITE THE-FLOOR-BELOW))
 (222 222 (:REWRITE THE-FLOOR-ABOVE))
 (222 222
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (222 222
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (161 157 (:REWRITE |(< (- x) (- y))|))
 (157 157
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (157 157
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (157 157
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (157 157
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (157 157 (:REWRITE |(< c (- x))|))
 (157 157
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (157 157
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (157 157
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (157 157
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (157 157 (:REWRITE |(< (/ x) (/ y))|))
 (153 153 (:REWRITE INTEGERP-<-CONSTANT))
 (153 153 (:REWRITE CONSTANT-<-INTEGERP))
 (147 147 (:REWRITE |(< (+ c/d x) y)|))
 (121 106 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (114 28 (:REWRITE |(+ (* c x) (* d x))|))
 (101 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (101 35
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (101 35
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (71 71 (:REWRITE |(< x (+ c/d y))|))
 (58 58 (:REWRITE |(< y (+ (- c) x))|))
 (44 44
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (42 23 (:REWRITE DEFAULT-MINUS))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (35 35
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (35 35 (:REWRITE |(equal c (/ x))|))
 (35 35 (:REWRITE |(equal c (- x))|))
 (35 35 (:REWRITE |(equal (/ x) c)|))
 (35 35 (:REWRITE |(equal (/ x) (/ y))|))
 (35 35 (:REWRITE |(equal (- x) c)|))
 (35 35 (:REWRITE |(equal (- x) (- y))|))
 (35 35 (:REWRITE |(< (* x y) 0)|))
 (28 28 (:REWRITE |(* 0 x)|))
 (17 17 (:REWRITE |(< 0 (* x y))|))
 (17 17 (:REWRITE |(< (/ x) 0)|))
 (14 9 (:TYPE-PRESCRIPTION MAX))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 13 (:REWRITE |(equal (+ (- c) x) y)|))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (8 8
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (8 8
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (8 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE |(* (- x) y)|))
 (5 5 (:META META-INTEGERP-CORRECT)))
(|(r32 addr (sec_not_present-modify s)) --- written to 1|
 (20351 268 (:REWRITE SIMPLIFY-SUMS-<))
 (16567 6348 (:REWRITE DEFAULT-PLUS-2))
 (15130 9
        (:REWRITE |(r32 addr (sec_not_present-modify-loop-1 i s))|))
 (13698 5
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (12845 6348 (:REWRITE DEFAULT-PLUS-1))
 (8025 2883 (:REWRITE NORMALIZE-ADDENDS))
 (6754
  112
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (6629 6629
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (6511 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (4975 323
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4954 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (4671
  112
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4664 8
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify s)))|))
 (4120 405
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3796 5 (:REWRITE DISJOINT-3-ITEMS))
 (2635 2635
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1542 277
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1388 762 (:REWRITE DEFAULT-TIMES-2))
 (1366 248 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1035 9 (:DEFINITION MAX))
 (1028 91 (:REWRITE |(* y (* x z))|))
 (958 405 (:REWRITE DEFAULT-LESS-THAN-2))
 (920 920
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (920 920 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (920 920 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (920 920
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (863 299 (:REWRITE DEFAULT-LOGAND-2))
 (822
   822
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (822
  822
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (822
     822
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (822 822
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (762 762 (:REWRITE DEFAULT-TIMES-1))
 (752 405 (:REWRITE DEFAULT-LESS-THAN-1))
 (544 544
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (478 18 (:REWRITE DISJOINT-4-ITEMS))
 (465 465 (:REWRITE FOLD-CONSTS-IN-+))
 (442 442
      (:REWRITE |(g field (w32 addr val st))|))
 (440 220 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (405 405 (:REWRITE THE-FLOOR-BELOW))
 (405 405 (:REWRITE THE-FLOOR-ABOVE))
 (359 299 (:REWRITE DEFAULT-LOGAND-1))
 (323 323
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (306 28 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (299 299 (:REWRITE LOGAND-CONSTANT-MASK))
 (293 280
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (289 280 (:REWRITE |(< (- x) c)|))
 (289 280 (:REWRITE |(< (- x) (- y))|))
 (280 280 (:REWRITE INTEGERP-<-CONSTANT))
 (280 280 (:REWRITE CONSTANT-<-INTEGERP))
 (280 280
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (280 280
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (280 280
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (280 280
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (280 280 (:REWRITE |(< c (- x))|))
 (280 280
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (280 280
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (280 280
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (280 280
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (280 280 (:REWRITE |(< (/ x) (/ y))|))
 (229 229 (:REWRITE |(+ x (- x))|))
 (199 199 (:REWRITE |(< (+ c/d x) y)|))
 (170 170 (:REWRITE |(< (* x y) 0)|))
 (117 9 (:REWRITE |(* x (- y))|))
 (100 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (100 91 (:REWRITE |(* a (/ a) b)|))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (85 19 (:REWRITE |(+ (* c x) (* d x))|))
 (82 82 (:TYPE-PRESCRIPTION ABS))
 (81 81
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (81 81
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (81 81 (:REWRITE |(< (/ x) 0)|))
 (79 79 (:REWRITE |(< x (+ c/d y))|))
 (76 76
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (73 73
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (71 71 (:REWRITE |(< y (+ (- c) x))|))
 (54 9 (:REWRITE |(- (* c x))|))
 (38 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (38 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (36 18 (:REWRITE DEFAULT-MINUS))
 (26 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 24
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (19 19 (:REWRITE |(* 0 x)|))
 (15 3 (:REWRITE O-INFP->NEQ-0))
 (15 3 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (15 3 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(* (- x) y)|))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (2 2 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(|(r32 addr (sec_not_present-modify s)) --- written to 2|
 (35668 487 (:REWRITE SIMPLIFY-SUMS-<))
 (25627 834
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (17404 9
        (:REWRITE |(r32 addr (sec_not_present-modify-loop-1 i s))|))
 (17278 7114 (:REWRITE DEFAULT-PLUS-2))
 (16821 980
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13961 7114 (:REWRITE DEFAULT-PLUS-1))
 (13382 5
        (:DEFINITION SEC_NOT_PRESENT-MODIFY-LOOP-1))
 (8282 3140 (:REWRITE NORMALIZE-ADDENDS))
 (7033
  112
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (6766 6766
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (6511 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (5317 718 (:REWRITE |(< c (- x))|))
 (4860
  112
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4664 8
       (:REWRITE |(memoryp (g :mem (sec_not_present-modify s)))|))
 (4638 5
       (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (4455 75
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (4236 75
       (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (4222 572 (:REWRITE INTEGERP-<-CONSTANT))
 (3480 5 (:REWRITE DISJOINT-3-ITEMS))
 (2892 2892
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1761 496
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1746 1219 (:REWRITE DEFAULT-TIMES-2))
 (1503 980 (:REWRITE DEFAULT-LESS-THAN-2))
 (1366 248 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1348 980 (:REWRITE DEFAULT-LESS-THAN-1))
 (1219 1219 (:REWRITE DEFAULT-TIMES-1))
 (1126 834
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1035 9 (:DEFINITION MAX))
 (980 980 (:REWRITE THE-FLOOR-BELOW))
 (980 980 (:REWRITE THE-FLOOR-ABOVE))
 (949 73 (:REWRITE |(* y (* x z))|))
 (920 920
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (920 920 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (920 920 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (920 920
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (897
   897
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (897
  897
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (897 897
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (897
     897
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (897 897
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (897 897
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (891 891
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (863 299 (:REWRITE DEFAULT-LOGAND-2))
 (730 730 (:TYPE-PRESCRIPTION ABS))
 (727 718 (:REWRITE |(< (- x) (- y))|))
 (718 718
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (718 718
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (718 718
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (718 718
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (718 718
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (718 718
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (718 718
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (718 718
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (718 718 (:REWRITE |(< (/ x) (/ y))|))
 (638 155 (:REWRITE |(- (* c x))|))
 (581 572 (:REWRITE |(< (- x) c)|))
 (579 579 (:REWRITE FOLD-CONSTS-IN-+))
 (572 572 (:REWRITE CONSTANT-<-INTEGERP))
 (520 520 (:REWRITE |(* (- x) y)|))
 (512 499
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (478 18 (:REWRITE DISJOINT-4-ITEMS))
 (442 442
      (:REWRITE |(g field (w32 addr val st))|))
 (440 220 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (365 73 (:REWRITE |(* c (* d x))|))
 (359 299 (:REWRITE DEFAULT-LOGAND-1))
 (306 28 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (299 299 (:REWRITE LOGAND-CONSTANT-MASK))
 (269 269 (:REWRITE |(< (+ c/d x) y)|))
 (229 229 (:REWRITE |(+ x (- x))|))
 (190 82 (:REWRITE |(* x (- y))|))
 (182 164 (:REWRITE DEFAULT-MINUS))
 (97 97 (:REWRITE |(< (* x y) 0)|))
 (91 91 (:REWRITE |(< x (+ c/d y))|))
 (85 19 (:REWRITE |(+ (* c x) (* d x))|))
 (76 76
     (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (75 75
     (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (73 73 (:REWRITE |(* a (/ a) b)|))
 (72 72 (:REWRITE |(< y (+ (- c) x))|))
 (38 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (38 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (26 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 24
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (19 19 (:REWRITE |(* 0 x)|))
 (15 3 (:REWRITE O-INFP->NEQ-0))
 (15 3 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (15 3 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (14 14
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:META META-INTEGERP-CORRECT)))
(SEC_NOT_PRESENT-ASSERTION)
(CROCK-100 (590 10 (:REWRITE DEFAULT-PLUS-1))
           (588 10 (:REWRITE DEFAULT-PLUS-2))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (344 344
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
           (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
           (192 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
           (106 2 (:REWRITE CANCEL-FLOOR-+))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
           (69 2 (:REWRITE FLOOR-ZERO . 3))
           (53 7 (:REWRITE INTEGERP-MINUS-X))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
           (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
           (36 2 (:REWRITE FLOOR-ZERO . 5))
           (34 4 (:REWRITE |(* (- x) y)|))
           (32 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
           (31 2 (:REWRITE FLOOR-ZERO . 4))
           (24 24 (:REWRITE DEFAULT-TIMES-2))
           (24 24 (:REWRITE DEFAULT-TIMES-1))
           (23 2 (:REWRITE FLOOR-=-X/Y . 3))
           (23 2 (:REWRITE FLOOR-=-X/Y . 2))
           (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
           (20 4 (:REWRITE DEFAULT-MINUS))
           (18 6
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (18 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (18 6 (:REWRITE DEFAULT-LESS-THAN-1))
           (18 4 (:REWRITE |(- (* c x))|))
           (13 13
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (10 2 (:REWRITE FLOOR-ZERO . 2))
           (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
           (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
           (10 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
           (10 2
               (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
           (10 2
               (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
           (9 6
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (9 6
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (8 8 (:REWRITE THE-FLOOR-BELOW))
           (6 6 (:TYPE-PRESCRIPTION ABS))
           (6 6 (:REWRITE SIMPLIFY-SUMS-<))
           (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (6 6 (:REWRITE INTEGERP-<-CONSTANT))
           (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
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
           (6 2 (:REWRITE FLOOR-CANCEL-*-CONST))
           (5 5 (:REWRITE REDUCE-INTEGERP-+))
           (5 5 (:META META-INTEGERP-CORRECT))
           (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (4 1 (:REWRITE |(n32p x)|))
           (2 2
              (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
           (2 2 (:REWRITE DEFAULT-FLOOR-2))
           (2 2 (:REWRITE DEFAULT-FLOOR-1))
           (2 2 (:REWRITE |(floor x (- y))| . 2))
           (2 2 (:REWRITE |(floor x (- y))| . 1))
           (2 2
              (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
           (2 2
              (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
           (2 2 (:REWRITE |(floor (- x) y)| . 2))
           (2 2 (:REWRITE |(floor (- x) y)| . 1))
           (2 2
              (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
           (1 1 (:REWRITE |(< 0 (/ x))|))
           (1 1 (:REWRITE |(< 0 (* x y))|))
           (1 1 (:REWRITE |(< (/ x) 0)|))
           (1 1
              (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
           (1 1 (:REWRITE |(< (* x y) 0)|))
           (1 1
              (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
           (1 1
              (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(CROCK-101
 (4784 104 (:REWRITE |(* (* x y) z)|))
 (2494 450 (:REWRITE DEFAULT-TIMES-1))
 (2448 450 (:REWRITE DEFAULT-TIMES-2))
 (2426 17 (:REWRITE FLOOR-ZERO . 3))
 (2321 17 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2188 17 (:REWRITE CANCEL-FLOOR-+))
 (2050
  2050
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2050
      2050
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2050
     2050
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2050 2050
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2014 69 (:REWRITE THE-FLOOR-ABOVE))
 (1829 17 (:REWRITE FLOOR-ZERO . 4))
 (1649 17 (:REWRITE FLOOR-ZERO . 5))
 (1474 17 (:REWRITE FLOOR-=-X/Y . 3))
 (1468 17 (:REWRITE FLOOR-=-X/Y . 2))
 (1128 17 (:REWRITE |(* (- x) y)|))
 (1111 17 (:REWRITE DEFAULT-FLOOR-RATIO))
 (830 15 (:REWRITE |(+ y x)|))
 (679 7 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (616 7 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (577 64 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (527 17 (:REWRITE |(integerp (- x))|))
 (496 16 (:REWRITE |(floor x 1)|))
 (493 37 (:REWRITE DEFAULT-PLUS-1))
 (487 37 (:REWRITE DEFAULT-PLUS-2))
 (460 64 (:REWRITE DEFAULT-LESS-THAN-1))
 (334 37
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (329 17 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (243 27
      (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (243 27
      (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2))
 (243 27
      (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
 (185 17 (:REWRITE FLOOR-ZERO . 2))
 (185 17 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (185 17 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (181 181 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (181 181
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (181 64 (:REWRITE DEFAULT-LESS-THAN-2))
 (177 24 (:REWRITE DEFAULT-MINUS))
 (161 17 (:REWRITE DEFAULT-FLOOR-1))
 (136 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (131 17 (:REWRITE FLOOR-CANCEL-*-CONST))
 (107 17
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (106 16
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (93 93 (:REWRITE REDUCE-INTEGERP-+))
 (93 93 (:REWRITE INTEGERP-MINUS-X))
 (93 93 (:META META-INTEGERP-CORRECT))
 (86 17
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (82 64 (:REWRITE SIMPLIFY-SUMS-<))
 (77 77 (:REWRITE |arith (expt x c)|))
 (77 77 (:REWRITE |arith (expt 1/c n)|))
 (70 16
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (69 69 (:REWRITE THE-FLOOR-BELOW))
 (64 64
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (64 64
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (64 64
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (64 64 (:REWRITE INTEGERP-<-CONSTANT))
 (64 64 (:REWRITE CONSTANT-<-INTEGERP))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< c (- x))|))
 (64 64
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (64 64
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (64 64
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (64 64 (:REWRITE |(< (/ x) (/ y))|))
 (64 64 (:REWRITE |(< (- x) c)|))
 (64 64 (:REWRITE |(< (- x) (- y))|))
 (55 11 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (50 50
     (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (50 5 (:REWRITE |(+ 0 x)|))
 (41 41
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (37 11 (:LINEAR EXPT->=-1-ONE))
 (37 11 (:LINEAR EXPT->-1-ONE))
 (36 36 (:REWRITE |arith (* c (* d x))|))
 (35 5 (:REWRITE |(/ (expt x n))|))
 (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (26 17 (:REWRITE DEFAULT-FLOOR-2))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (22 22
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (18 18 (:REWRITE |arith (- (* c x))|))
 (18 18 (:REWRITE |arith (* (- x) y)|))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(floor x (- y))| . 2))
 (17 17 (:REWRITE |(floor x (- y))| . 1))
 (17 17 (:REWRITE |(floor (- x) y)| . 2))
 (17 17 (:REWRITE |(floor (- x) y)| . 1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (17 17 (:REWRITE |(- (* c x))|))
 (16 16
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (15 15
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (11 11
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (11 11 (:LINEAR EXPT-X->=-X))
 (11 11 (:LINEAR EXPT-X->-X))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:LINEAR EXPT->=-1-TWO))
 (11 11 (:LINEAR EXPT->-1-TWO))
 (11 11 (:LINEAR EXPT-<=-1-ONE))
 (11 11 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE |(- (- x))|))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE ARITH-NORMALIZE-ADDENDS)))
(CROCK-102 (14 2 (:REWRITE DEFAULT-FLOOR-RATIO))
           (8 8 (:REWRITE DEFAULT-TIMES-2))
           (8 8 (:REWRITE DEFAULT-TIMES-1))
           (6 4
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (6 4
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (4 4 (:TYPE-PRESCRIPTION ABS))
           (4 4 (:REWRITE THE-FLOOR-BELOW))
           (4 4 (:REWRITE THE-FLOOR-ABOVE))
           (4 4 (:REWRITE SIMPLIFY-SUMS-<))
           (4 4
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (4 4
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (2 2 (:REWRITE DEFAULT-FLOOR-2))
           (2 2 (:REWRITE DEFAULT-FLOOR-1))
           (2 2 (:REWRITE |(< (/ x) 0)|))
           (2 2 (:REWRITE |(< (* x y) 0)|))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1
              (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
           (1 1 (:META META-INTEGERP-CORRECT)))
(CROCK-103 (124 4 (:LINEAR CROCK-102))
           (7 1 (:REWRITE DEFAULT-FLOOR-RATIO))
           (5 5 (:REWRITE DEFAULT-TIMES-2))
           (5 5 (:REWRITE DEFAULT-TIMES-1))
           (4 4 (:REWRITE THE-FLOOR-BELOW))
           (4 4 (:REWRITE THE-FLOOR-ABOVE))
           (4 4
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (4 4
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (4 4 (:REWRITE SIMPLIFY-SUMS-<))
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
           (4 4 (:REWRITE |(< (/ x) 0)|))
           (4 4 (:REWRITE |(< (/ x) (/ y))|))
           (4 4 (:REWRITE |(< (- x) c)|))
           (4 4 (:REWRITE |(< (- x) (- y))|))
           (4 4 (:REWRITE |(< (* x y) 0)|))
           (3 3
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1 (:REWRITE DEFAULT-FLOOR-2))
           (1 1 (:REWRITE DEFAULT-FLOOR-1))
           (1 1 (:META META-INTEGERP-CORRECT)))
(CROCK-200
 (190 190
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (175 5 (:REWRITE MOD-X-Y-=-X . 4))
 (110 5 (:REWRITE MOD-ZERO . 3))
 (90 5 (:REWRITE MOD-ZERO . 4))
 (55 5 (:REWRITE DEFAULT-MOD-RATIO))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40 10 (:REWRITE |(* y x)|))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (23 19 (:REWRITE DEFAULT-LOGAND-2))
 (20 20 (:REWRITE DEFAULT-TIMES-2))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:REWRITE DEFAULT-LOGAND-1))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-MOD-2))
 (5 5 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
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
 (5 5 (:META META-INTEGERP-CORRECT)))
(CROCK-203 (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
           (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
           (365 365
                (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
           (311 7 (:REWRITE DEFAULT-PLUS-1))
           (310 7 (:REWRITE DEFAULT-PLUS-2))
           (302 302
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
           (257 3 (:REWRITE FLOOR-ZERO . 3))
           (231 3 (:REWRITE CANCEL-FLOOR-+))
           (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
           (198 3 (:REWRITE FLOOR-X-Y-=-1 . 2))
           (163 3 (:REWRITE FLOOR-ZERO . 5))
           (157 3 (:REWRITE FLOOR-ZERO . 4))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
           (144 16
                (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
           (114 15 (:REWRITE INTEGERP-MINUS-X))
           (98 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (97 47 (:REWRITE DEFAULT-TIMES-2))
           (96 3 (:REWRITE FLOOR-=-X/Y . 3))
           (96 3 (:REWRITE FLOOR-=-X/Y . 2))
           (91 47 (:REWRITE DEFAULT-TIMES-1))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
           (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
           (80 16
               (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
           (75 6 (:REWRITE |(* (- x) y)|))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
           (69 69 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
           (51 3 (:REWRITE DEFAULT-FLOOR-RATIO))
           (48 8 (:LINEAR BINARY-LOGAND->=-0))
           (48 8 (:LINEAR BINARY-LOGAND-<=))
           (43 11
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (43 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (42 6 (:REWRITE DEFAULT-MINUS))
           (39 6 (:REWRITE |(- (* c x))|))
           (38 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
           (37 37 (:REWRITE LOGAND-CONSTANT-MASK))
           (37 37 (:REWRITE DEFAULT-LOGAND-2))
           (37 37 (:REWRITE DEFAULT-LOGAND-1))
           (33 11 (:REWRITE DEFAULT-LESS-THAN-1))
           (32 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
           (27 3 (:REWRITE FLOOR-X-Y-=--1 . 2))
           (25 25
               (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
           (21 11 (:REWRITE DEFAULT-LESS-THAN-2))
           (21 3 (:REWRITE FLOOR-ZERO . 2))
           (21 3 (:REWRITE FLOOR-X-Y-=-1 . 3))
           (21 3 (:REWRITE FLOOR-X-Y-=--1 . 3))
           (15 3
               (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
           (15 3 (:REWRITE FLOOR-CANCEL-*-CONST))
           (15 3
               (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
           (14 11
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (14 11
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (12 12 (:REWRITE REDUCE-INTEGERP-+))
           (12 12 (:META META-INTEGERP-CORRECT))
           (11 11 (:REWRITE THE-FLOOR-ABOVE))
           (11 11 (:REWRITE SIMPLIFY-SUMS-<))
           (11 11
               (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (11 11
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (11 11 (:REWRITE INTEGERP-<-CONSTANT))
           (11 11 (:REWRITE CONSTANT-<-INTEGERP))
           (11 11
               (:REWRITE |(< c (/ x)) positive c --- present in goal|))
           (11 11
               (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
           (11 11
               (:REWRITE |(< c (/ x)) negative c --- present in goal|))
           (11 11
               (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
           (11 11 (:REWRITE |(< c (- x))|))
           (11 11
               (:REWRITE |(< (/ x) c) positive c --- present in goal|))
           (11 11
               (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
           (11 11
               (:REWRITE |(< (/ x) c) negative c --- present in goal|))
           (11 11
               (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
           (11 11 (:REWRITE |(< (/ x) (/ y))|))
           (11 11 (:REWRITE |(< (- x) c)|))
           (11 11 (:REWRITE |(< (- x) (- y))|))
           (10 10 (:LINEAR LOGAND-BOUNDS-NEG . 2))
           (10 10 (:LINEAR LOGAND-BOUNDS-NEG . 1))
           (10 2
               (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
           (9 3
              (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
           (9 3 (:REWRITE DEFAULT-FLOOR-1))
           (9 3
              (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
           (6 6 (:TYPE-PRESCRIPTION ABS))
           (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (6 2
              (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
           (3 3 (:REWRITE DEFAULT-FLOOR-2))
           (3 3 (:REWRITE |(floor x (- y))| . 2))
           (3 3 (:REWRITE |(floor x (- y))| . 1))
           (3 3
              (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
           (3 3
              (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
           (3 3 (:REWRITE |(floor (- x) y)| . 2))
           (3 3 (:REWRITE |(floor (- x) y)| . 1))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
           (2 2 (:REWRITE |(< 0 (/ x))|))
           (2 2 (:REWRITE |(< 0 (* x y))|))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
           (1 1
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (1 1 (:REWRITE |(< (/ x) 0)|))
           (1 1 (:REWRITE |(< (* x y) 0)|)))
(CROCK-2000)
(CROCK-2001-3
 (17550 4 (:REWRITE FLOOR-=-X/Y . 4))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9353 9353
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4993 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (3505 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3278 49 (:REWRITE FLOOR-ZERO . 3))
 (3224 843 (:REWRITE DEFAULT-TIMES-2))
 (3185 75 (:REWRITE DEFAULT-PLUS-2))
 (2822 49 (:REWRITE CANCEL-FLOOR-+))
 (2801 75 (:REWRITE DEFAULT-PLUS-1))
 (2299 12 (:REWRITE MOD-X-Y-=-X . 3))
 (2154 49 (:REWRITE FLOOR-ZERO . 5))
 (2113 12 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2084 176 (:REWRITE INTEGERP-MINUS-X))
 (2020 49 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2013 12 (:REWRITE MOD-X-Y-=-X . 4))
 (1975 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1975 393 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1975 393
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1871 12 (:REWRITE CANCEL-MOD-+))
 (1870 49 (:REWRITE FLOOR-ZERO . 4))
 (1855 162 (:REWRITE THE-FLOOR-ABOVE))
 (1723 12 (:REWRITE MOD-ZERO . 4))
 (1594 14
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1516 8 (:LINEAR MOD-BOUNDS-1))
 (1513 126 (:REWRITE |(* (- x) y)|))
 (1473 843 (:REWRITE DEFAULT-TIMES-1))
 (1004 124 (:REWRITE DEFAULT-MINUS))
 (924 49 (:REWRITE FLOOR-=-X/Y . 3))
 (904 49 (:REWRITE FLOOR-=-X/Y . 2))
 (821 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (766 766
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (686 686
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (603 12 (:REWRITE MOD-ZERO . 3))
 (595 117 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (595 117 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (591 49 (:REWRITE DEFAULT-FLOOR-RATIO))
 (576 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (575 117
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (575 117
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (507 160
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (507 160
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (453 453
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (417 12 (:REWRITE DEFAULT-MOD-RATIO))
 (374 160 (:REWRITE DEFAULT-LESS-THAN-1))
 (356 162 (:REWRITE THE-FLOOR-BELOW))
 (325 49 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (293 160 (:REWRITE DEFAULT-LESS-THAN-2))
 (293 18 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (285 49 (:REWRITE FLOOR-ZERO . 2))
 (285 49 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (285 49 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (251 49 (:REWRITE FLOOR-CANCEL-*-CONST))
 (250 12 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (250 12 (:REWRITE MOD-X-Y-=-X . 2))
 (250 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (250 12
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (196 160
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (196 160
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (178 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (177 49
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (176 48
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (160 160 (:REWRITE SIMPLIFY-SUMS-<))
 (160 160
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (160 160
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (160 160 (:REWRITE INTEGERP-<-CONSTANT))
 (160 160 (:REWRITE CONSTANT-<-INTEGERP))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< c (- x))|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (160 160
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (160 160 (:REWRITE |(< (/ x) (/ y))|))
 (160 160 (:REWRITE |(< (- x) c)|))
 (160 160 (:REWRITE |(< (- x) (- y))|))
 (159 23
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (157 49
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (155 12 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (155 12 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (155 12 (:REWRITE MOD-CANCEL-*-CONST))
 (124 48
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (123 12
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (121 121
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (121 121
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (117 117 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (117 117
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (117 117
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (117 117
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (115 115 (:REWRITE REDUCE-INTEGERP-+))
 (115 115 (:META META-INTEGERP-CORRECT))
 (112 112 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (110 34
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (107 12 (:REWRITE DEFAULT-MOD-1))
 (104 10 (:REWRITE |(equal (+ (- c) x) y)|))
 (89 49 (:REWRITE DEFAULT-FLOOR-1))
 (86 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (86 86 (:REWRITE DEFAULT-LOGAND-2))
 (86 86 (:REWRITE DEFAULT-LOGAND-1))
 (81 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (72 72 (:TYPE-PRESCRIPTION ABS))
 (72 34
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (49 49 (:REWRITE DEFAULT-FLOOR-2))
 (48 48 (:REWRITE |(floor x (- y))| . 2))
 (48 48 (:REWRITE |(floor x (- y))| . 1))
 (48 48
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (48 48
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (48 48 (:REWRITE |(floor (- x) y)| . 2))
 (48 48 (:REWRITE |(floor (- x) y)| . 1))
 (44 12
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (43 11
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< 0 (/ x))|))
 (42 42 (:REWRITE |(< 0 (* x y))|))
 (40 8 (:LINEAR MOD-BOUNDS-2))
 (27 27
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (23
   23
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (23
  23
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (23 23
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (23 11
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (22 4
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (21 21 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (21 21 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (20 4 (:LINEAR MOD-BOUNDS-3))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (14 14
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (14 14 (:REWRITE |(equal c (/ x))|))
 (14 14 (:REWRITE |(equal c (- x))|))
 (14 14 (:REWRITE |(equal (/ x) c)|))
 (14 14 (:REWRITE |(equal (/ x) (/ y))|))
 (14 14 (:REWRITE |(equal (- x) c)|))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (12 12 (:REWRITE DEFAULT-MOD-2))
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
 (9 1 (:REWRITE MOD-POSITIVE . 3))
 (9 1 (:REWRITE FLOOR-POSITIVE . 2))
 (9 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 1 (:REWRITE MOD-NONPOSITIVE))
 (5 1 (:REWRITE FLOOR-POSITIVE . 4))
 (5 1 (:REWRITE FLOOR-POSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (5 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(+ x (- x))|))
 (1 1 (:REWRITE MOD-POSITIVE . 2))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE FLOOR-ZERO . 1))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (1 1 (:REWRITE |(+ c (+ d x))|)))
(CROCK-2001
 (111644 85
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80758 34 (:REWRITE |(equal (+ (- c) x) y)|))
 (57713 57713
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (57713 57713
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (50725 589 (:REWRITE DEFAULT-PLUS-2))
 (43680 16 (:REWRITE FLOOR-=-X/Y . 4))
 (30771 2367
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (28624 589 (:REWRITE DEFAULT-PLUS-1))
 (21303 2367
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (21303 2367
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (21303 2367
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (14118 148 (:REWRITE FLOOR-ZERO . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (11835 2367
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (9479 85
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8609 148 (:REWRITE FLOOR-ZERO . 4))
 (8548 3380 (:REWRITE DEFAULT-TIMES-2))
 (8373 4089
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8228 148 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (8163 148 (:REWRITE FLOOR-ZERO . 5))
 (7997 999 (:REWRITE INTEGERP-MINUS-X))
 (7365 1473 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (7365 1473 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (7205 1473
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (7205 1473
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6399 633 (:REWRITE DEFAULT-LESS-THAN-1))
 (5931 111 (:REWRITE CANCEL-MOD-+))
 (5872 32
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (5626 60 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5235 529 (:REWRITE |(* (- x) y)|))
 (4612 3380 (:REWRITE DEFAULT-TIMES-1))
 (4486 148 (:REWRITE FLOOR-=-X/Y . 2))
 (4414 148 (:REWRITE FLOOR-=-X/Y . 3))
 (4089 4089
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4089 4089
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4089 4089
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3974 622
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (3937 630
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3484 529 (:REWRITE DEFAULT-MINUS))
 (3106 149 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3096 122 (:REWRITE MOD-X-Y-=-X . 4))
 (2562 122 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (2434 122 (:REWRITE MOD-ZERO . 4))
 (2357 633 (:REWRITE DEFAULT-LESS-THAN-2))
 (2013 148 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1937 737 (:META META-INTEGERP-CORRECT))
 (1863 4 (:REWRITE |(floor (+ x r) i)|))
 (1830 1830
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1556 60 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1535 122 (:REWRITE MOD-ZERO . 3))
 (1533 122 (:REWRITE DEFAULT-MOD-RATIO))
 (1473 1473 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (1473 1473 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1473 1473
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1473 1473
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1473 1473
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1473 1473
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1394 25 (:REWRITE |(* x (+ y z))|))
 (1316 60 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (908 148 (:REWRITE FLOOR-ZERO . 2))
 (908 148 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (908 148 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (763 147 (:REWRITE FLOOR-CANCEL-*-CONST))
 (747 630
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (747 630
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (737 737 (:REWRITE REDUCE-INTEGERP-+))
 (722 122 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (677 113 (:REWRITE MOD-X-Y-=-X . 2))
 (677 113
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (666 122 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (666 122 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (624 624
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (624 624 (:REWRITE INTEGERP-<-CONSTANT))
 (624 624 (:REWRITE CONSTANT-<-INTEGERP))
 (624 624
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (624 624
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (624 624
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (624 624
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (624 624 (:REWRITE |(< c (- x))|))
 (624 624
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (624 624
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (624 624
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (624 624
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (624 624 (:REWRITE |(< (/ x) (/ y))|))
 (624 624 (:REWRITE |(< (- x) c)|))
 (624 624 (:REWRITE |(< (- x) (- y))|))
 (619 147
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (614 142
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (543 111 (:REWRITE MOD-CANCEL-*-CONST))
 (510 102 (:LINEAR MOD-BOUNDS-2))
 (455 111
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (455 111
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (431 147
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (429 149 (:REWRITE DEFAULT-FLOOR-1))
 (411 51 (:LINEAR MOD-BOUNDS-3))
 (349 1 (:REWRITE |(* (if a b c) x)|))
 (340 116
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (337 101
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (288 3 (:REWRITE O-INFP->NEQ-0))
 (266 142
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (246 246 (:TYPE-PRESCRIPTION ABS))
 (228 116
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (211 111
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (211 111
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (183 183
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (178 122 (:REWRITE DEFAULT-MOD-1))
 (155 155 (:REWRITE |(< 0 (* x y))|))
 (154 154
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (154 154
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (154 154 (:REWRITE |(< 0 (/ x))|))
 (149 149 (:REWRITE DEFAULT-FLOOR-2))
 (142 142 (:REWRITE |(floor x (- y))| . 2))
 (142 142 (:REWRITE |(floor x (- y))| . 1))
 (142 142
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (142 142
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (142 142 (:REWRITE |(floor (- x) y)| . 2))
 (142 142 (:REWRITE |(floor (- x) y)| . 1))
 (122 122 (:REWRITE DEFAULT-MOD-2))
 (111 111 (:REWRITE |(mod x (- y))| . 3))
 (111 111 (:REWRITE |(mod x (- y))| . 2))
 (111 111 (:REWRITE |(mod x (- y))| . 1))
 (111 111
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (111 111
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (111 111 (:REWRITE |(mod (- x) y)| . 3))
 (111 111 (:REWRITE |(mod (- x) y)| . 2))
 (111 111 (:REWRITE |(mod (- x) y)| . 1))
 (98 8 (:REWRITE |(n32p x)|))
 (91 91
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (85 85
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (85 85 (:REWRITE |(equal c (/ x))|))
 (85 85 (:REWRITE |(equal c (- x))|))
 (85 85 (:REWRITE |(equal (/ x) c)|))
 (85 85 (:REWRITE |(equal (/ x) (/ y))|))
 (85 85 (:REWRITE |(equal (- x) c)|))
 (85 85 (:REWRITE |(equal (- x) (- y))|))
 (80 2 (:LINEAR CROCK-100))
 (75 15
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (54 6 (:REWRITE MOD-POSITIVE . 3))
 (46 46
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (40 40 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (37 37 (:REWRITE |(< (+ c/d x) y)|))
 (32 32 (:REWRITE |(< (+ (- c) x) y)|))
 (30 6 (:REWRITE MOD-NONPOSITIVE))
 (18 2 (:REWRITE MOD-ZERO . 1))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (10 2 (:REWRITE MOD-ZERO . 2))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE MOD-POSITIVE . 2))
 (6 6 (:REWRITE MOD-POSITIVE . 1))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE DEFAULT-LOGAND-2))
 (4 4 (:REWRITE DEFAULT-LOGAND-1))
 (4 4 (:REWRITE |(equal (* x y) 0)|))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (2 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (2 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (2 2
    (:REWRITE |(equal (mod (+ x y) z) x)|))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
($$$INSUB)
($$$PRESUB)
($$$MODIFYSUB)
($$$NO-MAIN-CUTPOINT-IN-SUB)
($$$IN-SUB-IMPLIES-IN-MAIN)
($$$PRESUB-IMPLIES-INSUB)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-test|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-base|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-step|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-fn|
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1|
 (1
   1
   (:TYPE-PRESCRIPTION |$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-defpun-stn|)))
(|$$$STEPS-TO-EXITPOINT-SUB-TAIL-arity-1-DEF|)
($$$STEPS-TO-EXITPOINT-SUB-TAIL)
($$$STEPS-TO-EXITPOINT-SUB-TAIL-DEF (4 4 (:REWRITE DEFAULT-CAR))
                                    (2 2 (:REWRITE DEFAULT-CDR)))
($$$STEPS-TO-EXITPOINT-SUB-TAIL$DEF)
($$$STEPS-TO-EXITPOINT-SUB (8 2 (:TYPE-PRESCRIPTION RETURN-LAST))
                           (2 2
                              (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR)))
($$$NEXT-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB)
($$$EXISTS-EXITPOINT-SUB-SUFF)
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn| (4 4 (:REWRITE DEFAULT-<-2))
                                           (4 4 (:REWRITE DEFAULT-<-1))
                                           (1 1 (:REWRITE ZP-OPEN))
                                           (1 1 (:REWRITE DEFAULT-+-2))
                                           (1 1 (:REWRITE DEFAULT-+-1)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF)
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION
 (25485 396 (:DEFINITION BINARY-LOGAND))
 (6498 4543 (:REWRITE DEFAULT-+-2))
 (6038 4543 (:REWRITE DEFAULT-+-1))
 (4374 3141 (:REWRITE DEFAULT-*-2))
 (3648 3141 (:REWRITE DEFAULT-*-1))
 (2890 1986 (:REWRITE DEFAULT-<-1))
 (2360 1986 (:REWRITE DEFAULT-<-2))
 (2185 260 (:REWRITE ZIP-OPEN))
 (1190 725 (:REWRITE DEFAULT-DENOMINATOR))
 (1178 719 (:REWRITE DEFAULT-NUMERATOR))
 (986 640 (:REWRITE DEFAULT-UNARY-MINUS))
 (932 932
      (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
 (932 932 (:REWRITE INIT_PDTS-LOADED-THM-32))
 (932 932 (:REWRITE INIT_PDPT-LOADED-THM-32))
 (932 932
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (815 260 (:REWRITE O-INFP->NEQ-0))
 (588 98 (:DEFINITION EVENP))
 (413 43 (:REWRITE DISJOINT-4-ITEMS))
 (222 37
      (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (74 74 (:REWRITE |(subrangep x x)|))
 (37 37 (:TYPE-PRESCRIPTION SUBRANGEP))
 (37
  37
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (37
  37
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (37
  37
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|)))
($$$ASSERTION-MAIN-IMPLIES-POST
     (14 7 (:REWRITE DEFAULT-+-2))
     (12 6 (:REWRITE DEFAULT-<-2))
     (10 6 (:REWRITE DEFAULT-<-1))
     (7 7 (:REWRITE DEFAULT-+-1))
     (3 3
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
     (1 1 (:REWRITE INIT_PDTS-LOADED-THM-32))
     (1 1 (:REWRITE INIT_PDPT-LOADED-THM-32))
     (1 1
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32)))
($$$ASSERTION-IMPLIES-CUTPOINT (38 19 (:REWRITE DEFAULT-+-2))
                               (19 19 (:REWRITE DEFAULT-+-1))
                               (18 9 (:REWRITE DEFAULT-<-2))
                               (12 9 (:REWRITE DEFAULT-<-1))
                               (4 4
                                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                               (1 1
                                  (:REWRITE SEC_NOT_PRESENT-LOADED-THM-32))
                               (1 1 (:REWRITE INIT_PDTS-LOADED-THM-32))
                               (1 1 (:REWRITE INIT_PDPT-LOADED-THM-32))
                               (1 1
                                  (:REWRITE CREATE_NESTED_PT-LOADED-THM-32)))
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
(SIMULATION-DEFAULT-HINT (5 5 (:TYPE-PRESCRIPTION LAST)))
(SIMULATE-MAIN-START
 (106587 79492 (:REWRITE DEFAULT-PLUS-2))
 (95431 79492 (:REWRITE DEFAULT-PLUS-1))
 (76273 3234
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (39860 39860
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16452 1701 (:REWRITE INIT_PDTS-LOADED-THM-08))
 (16452 1701 (:REWRITE INIT_PDPT-LOADED-THM-08))
 (16452 1701
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
 (14375 14375
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (9253 3707 (:REWRITE DEFAULT-LOGAND-2))
 (8824 215 (:REWRITE |(n32-to-i32 x) --- 2|))
 (8802
   8802
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8802
  8802
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8802
      8802
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8802
     8802
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8802 8802
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8802 8802
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6757 3235 (:REWRITE DEFAULT-LESS-THAN-1))
 (5075 2138
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4665 2437 (:REWRITE DEFAULT-TIMES-2))
 (4330 3235 (:REWRITE DEFAULT-LESS-THAN-2))
 (3725 3707 (:REWRITE DEFAULT-LOGAND-1))
 (3285 3235
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3235 3235 (:REWRITE THE-FLOOR-BELOW))
 (3235 3235 (:REWRITE THE-FLOOR-ABOVE))
 (3234 3234
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3045 2139
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2858 703
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2818 1496 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2447 2437 (:REWRITE DEFAULT-TIMES-1))
 (2408 2408
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2139 2139 (:REWRITE INTEGERP-<-CONSTANT))
 (2139 2139 (:REWRITE CONSTANT-<-INTEGERP))
 (2139 2139
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2139 2139
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2139 2139
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2139 2139
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2139 2139 (:REWRITE |(< c (- x))|))
 (2139 2139
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2139 2139
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2139 2139
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2139 2139
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2139 2139 (:REWRITE |(< (/ x) (/ y))|))
 (2139 2139 (:REWRITE |(< (- x) c)|))
 (2139 2139 (:REWRITE |(< (- x) (- y))|))
 (1888 1888 (:REWRITE |(< (+ c/d x) y)|))
 (1661 151 (:REWRITE DISJOINT-4-ITEMS))
 (1658 703
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1650 450 (:REWRITE ACL2-NUMBERP-X))
 (1628 8
       (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (1569 1267
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1000 1000 (:REWRITE FOLD-CONSTS-IN-+))
 (960 8 (:REWRITE DISJOINT-3-ITEMS))
 (794 794 (:REWRITE |(< (+ (- c) x) y)|))
 (777 777 (:REWRITE |(< x (+ c/d y))|))
 (703 703
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (703 703
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (703 703
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (703 703 (:REWRITE |(equal c (/ x))|))
 (703 703 (:REWRITE |(equal c (- x))|))
 (703 703 (:REWRITE |(equal (/ x) c)|))
 (703 703 (:REWRITE |(equal (/ x) (/ y))|))
 (703 703 (:REWRITE |(equal (- x) c)|))
 (703 703 (:REWRITE |(equal (- x) (- y))|))
 (623 160 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (623 160 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (600 150 (:REWRITE RATIONALP-X))
 (503 22 (:REWRITE DEFAULT-MOD-RATIO))
 (396 396 (:REWRITE |(< y (+ (- c) x))|))
 (302 302 (:REWRITE |(subrangep x x)|))
 (272 136 (:REWRITE DEFAULT-MINUS))
 (153 153 (:REWRITE |(< 0 (* x y))|))
 (152 152
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (152 152
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (152 152 (:REWRITE |(< 0 (/ x))|))
 (151 151 (:REWRITE REDUCE-INTEGERP-+))
 (151 151 (:REWRITE INTEGERP-MINUS-X))
 (151 151 (:REWRITE |(< (* x y) 0)|))
 (151 151 (:META META-INTEGERP-CORRECT))
 (150 150 (:REWRITE REDUCE-RATIONALP-+))
 (150 150 (:REWRITE REDUCE-RATIONALP-*))
 (150 150 (:REWRITE RATIONALP-MINUS-X))
 (150 150 (:META META-RATIONALP-CORRECT))
 (113 22 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (99 99 (:REWRITE |(equal (+ (- c) x) y)|))
 (90 60 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (75 1 (:REWRITE MOD-X-Y-=-X . 4))
 (58 1 (:REWRITE MOD-ZERO . 4))
 (56 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (37 1 (:REWRITE MOD-ZERO . 3))
 (25 22 (:REWRITE DEFAULT-MOD-1))
 (22 22 (:REWRITE DEFAULT-MOD-2))
 (21 21
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (14 1 (:REWRITE |(* y (* x z))|))
 (11 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (8 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (3 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 1 (:REWRITE |(* a (/ a) b)|))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(SIMULATE-MAIN-LOOP-LOOP
 (55463 3263
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (32643 25397 (:REWRITE DEFAULT-PLUS-1))
 (24000 24000
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (14797 14797
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13906 716 (:REWRITE INIT_PDTS-LOADED-THM-08))
 (13906 716 (:REWRITE INIT_PDPT-LOADED-THM-08))
 (13906 716
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-08))
 (7537 2017
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6081 2017
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4768 3289 (:REWRITE DEFAULT-LESS-THAN-1))
 (4714 3289 (:REWRITE DEFAULT-LESS-THAN-2))
 (4686 2384
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3694 734 (:REWRITE ACL2-NUMBERP-X))
 (3503 1493 (:REWRITE DEFAULT-LOGAND-2))
 (3365 3265
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3289 3289 (:REWRITE THE-FLOOR-BELOW))
 (3289 3289 (:REWRITE THE-FLOOR-ABOVE))
 (3277 2394
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3263 3263
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2654 1330 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2499 1709
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2476 2396 (:REWRITE |(< (- x) c)|))
 (2398 2396 (:REWRITE |(< (- x) (- y))|))
 (2396 2396
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2396 2396
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2396 2396
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2396 2396
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2396 2396 (:REWRITE |(< c (- x))|))
 (2396 2396
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2396 2396
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2396 2396
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2396 2396
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2396 2396 (:REWRITE |(< (/ x) (/ y))|))
 (2394 2394 (:REWRITE INTEGERP-<-CONSTANT))
 (2394 2394 (:REWRITE CONSTANT-<-INTEGERP))
 (2122 1132 (:REWRITE DEFAULT-TIMES-2))
 (2057 187 (:REWRITE DISJOINT-4-ITEMS))
 (2033 2025 (:REWRITE |(equal (/ x) (/ y))|))
 (2026 2026
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2026 2026
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2025 2025 (:REWRITE |(equal c (/ x))|))
 (2025 2025 (:REWRITE |(equal (- x) (- y))|))
 (2017 2017
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2017 2017 (:REWRITE |(equal c (- x))|))
 (2017 2017 (:REWRITE |(equal (- x) c)|))
 (1539 1539 (:REWRITE |(< (+ c/d x) y)|))
 (1509 1493 (:REWRITE DEFAULT-LOGAND-1))
 (1480 370 (:REWRITE RATIONALP-X))
 (1410
   1410
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1410
  1410
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1410
      1410
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1410
     1410
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1410 1410
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1410 1410
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1152 1132 (:REWRITE DEFAULT-TIMES-1))
 (1026 1026
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (882 38 (:REWRITE DEFAULT-MOD-RATIO))
 (678 678 (:REWRITE |(< x (+ c/d y))|))
 (674 674 (:REWRITE |(< (+ (- c) x) y)|))
 (600 198 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (600 198 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (520 260 (:REWRITE O-INFP->NEQ-0))
 (478 234 (:REWRITE DEFAULT-MINUS))
 (460 460 (:REWRITE FOLD-CONSTS-IN-+))
 (456 38 (:REWRITE |(* x (+ y z))|))
 (396 396 (:REWRITE |(< y (+ (- c) x))|))
 (374 374 (:REWRITE REDUCE-INTEGERP-+))
 (374 374 (:REWRITE INTEGERP-MINUS-X))
 (374 374 (:REWRITE |(subrangep x x)|))
 (374 374 (:META META-INTEGERP-CORRECT))
 (370 370 (:REWRITE REDUCE-RATIONALP-+))
 (370 370 (:REWRITE REDUCE-RATIONALP-*))
 (370 370 (:REWRITE RATIONALP-MINUS-X))
 (370 370 (:META META-RATIONALP-CORRECT))
 (306 10
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (260 260
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (221 213 (:REWRITE |(< 0 (/ x))|))
 (218 20 (:REWRITE |(n32 n)|))
 (215 215 (:REWRITE |(< 0 (* x y))|))
 (213 213
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (213 213
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (207
  207
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (192 38 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (189 189 (:REWRITE |(< (* x y) 0)|))
 (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (120 24 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (120 24
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (120 24
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (96 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (90 90 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (88 2 (:REWRITE MOD-X-Y-=-X . 3))
 (86 86 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (86 86 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (76 8 (:REWRITE |(* (- x) y)|))
 (70 2 (:REWRITE MOD-ZERO . 3))
 (70 2 (:LINEAR MOD-BOUNDS-3))
 (54 54
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (46 46 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (44 4 (:REWRITE SIMULATE-MAIN-START))
 (40 38 (:REWRITE DEFAULT-MOD-1))
 (38 38 (:REWRITE DEFAULT-MOD-2))
 (32 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (28 2 (:REWRITE |(* y (* x z))|))
 (26 10
     (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (26 10
     (:REWRITE |(< x (/ y)) with (< y 0)|))
 (24 24 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (24 24
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (24 24 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (24 24 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (24 24
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (24 8 (:REWRITE |(equal x (/ y))|))
 (22 4 (:REWRITE |(- (* c x))|))
 (20 4 (:LINEAR MOD-BOUNDS-2))
 (16 8 (:REWRITE DEFAULT-DIVIDE))
 (16 8 (:REWRITE |(not (equal x (/ y)))|))
 (10 2 (:REWRITE MOD-ZERO . 4))
 (10 2 (:REWRITE MOD-X-Y-=-X . 4))
 (10 2 (:REWRITE MOD-X-Y-=-X . 2))
 (10 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (10 2 (:REWRITE MOD-CANCEL-*-CONST))
 (10 2
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (10 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (10 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (10 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 2 (:REWRITE |(* a (/ a) b)|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
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
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (2 2 (:REWRITE |(< (/ x) 0)|)))
(ASSERTION-INVARIANT-DEFAULT-HINT-1)
(ASSERTION-INVARIANT-DEFAULT-HINT)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS
 (948769 712050 (:REWRITE DEFAULT-PLUS-1))
 (647544 162 (:DEFINITION NATP))
 (512142 3096
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (367215 2316 (:REWRITE DISJOINT-3-ITEMS))
 (359565 359565
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (237924 237924
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (227349 3438 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (227349 3438 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (183703 36271 (:REWRITE DEFAULT-LOGAND-2))
 (138708 1236
         (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (112531 22371 (:REWRITE ACL2-NUMBERP-X))
 (98883
   98883
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (98883
  98883
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (98883
      98883
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (98883
     98883
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (98883 98883
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (98883 98883
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (62773 33731 (:REWRITE DEFAULT-TIMES-2))
 (51669 11098
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (45080 11270 (:REWRITE RATIONALP-X))
 (41253 41253 (:REWRITE FOLD-CONSTS-IN-+))
 (37693 36271 (:REWRITE DEFAULT-LOGAND-1))
 (36271 36271 (:REWRITE LOGAND-CONSTANT-MASK))
 (34097 33731 (:REWRITE DEFAULT-TIMES-1))
 (32930 32930
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (30933 11098
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29784 19575 (:REWRITE DEFAULT-LESS-THAN-2))
 (19575 19575 (:REWRITE THE-FLOOR-BELOW))
 (19575 19575 (:REWRITE THE-FLOOR-ABOVE))
 (19493 19493
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19493 19493
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14723 14720 (:REWRITE |(< (- x) c)|))
 (14723 14720 (:REWRITE |(< (- x) (- y))|))
 (14720 14720 (:REWRITE INTEGERP-<-CONSTANT))
 (14720 14720 (:REWRITE CONSTANT-<-INTEGERP))
 (14720 14720
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (14720 14720
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (14720 14720
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (14720 14720
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (14720 14720 (:REWRITE |(< c (- x))|))
 (14720 14720
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (14720 14720
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (14720 14720
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (14720 14720
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (14720 14720 (:REWRITE |(< (/ x) (/ y))|))
 (11456 11456 (:REWRITE REDUCE-INTEGERP-+))
 (11456 11456 (:REWRITE INTEGERP-MINUS-X))
 (11456 11456 (:META META-INTEGERP-CORRECT))
 (11270 11270 (:REWRITE REDUCE-RATIONALP-+))
 (11270 11270 (:REWRITE REDUCE-RATIONALP-*))
 (11270 11270 (:REWRITE RATIONALP-MINUS-X))
 (11270 11270 (:META META-RATIONALP-CORRECT))
 (11158 11158
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11158 11158
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11122 11110 (:REWRITE |(equal (/ x) (/ y))|))
 (11110 11110 (:REWRITE |(equal c (/ x))|))
 (11110 11110 (:REWRITE |(equal (- x) (- y))|))
 (11098 11098
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (11098 11098 (:REWRITE |(equal c (- x))|))
 (11098 11098 (:REWRITE |(equal (- x) c)|))
 (10555 10555 (:REWRITE |(< (+ c/d x) y)|))
 (9420 9420
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (6650 4315 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5881 5881 (:REWRITE |(< (+ (- c) x) y)|))
 (5724 318 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (5355 384
       (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (3228 3228 (:REWRITE |(< (* x y) 0)|))
 (2712 2712 (:REWRITE |(< x (+ c/d y))|))
 (1695 1695 (:REWRITE |(< (/ x) 0)|))
 (1644 1644
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1644 1644
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1302 186
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1187 1187 (:REWRITE |(< 0 (* x y))|))
 (1100 1088 (:REWRITE |(< 0 (/ x))|))
 (1095 1095 (:REWRITE |(< y (+ (- c) x))|))
 (1077 528 (:REWRITE O-INFP->NEQ-0))
 (980 980
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (980 980
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (936 936
      (:REWRITE |(G field (sec_not_present-modify-loop-1 i s))|))
 (807 111
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (528 528
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (408 111
      (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (408 111
      (:REWRITE |(< x (/ y)) with (< y 0)|))
 (162 162 (:TYPE-PRESCRIPTION NATP))
 (36 12 (:REWRITE |(equal x (/ y))|))
 (24 12 (:REWRITE DEFAULT-DIVIDE))
 (24 12 (:REWRITE |(not (equal x (/ y)))|))
 (12 6 (:REWRITE DEFAULT-MINUS))
 (3 3 (:REWRITE |(* (- x) y)|)))
(SEC_NOT_PRESENT-CORRECT)
(IN-CREATE_NESTED_PT)
(CREATE_NESTED_PT-CUTPOINT-P)
(CREATE_NESTED_PT-PRE)
(CREATE_NESTED_PT-MODIFY)
(ASH-THM-100
     (590 10 (:REWRITE DEFAULT-PLUS-1))
     (588 10 (:REWRITE DEFAULT-PLUS-2))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (192 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (106 2 (:REWRITE CANCEL-FLOOR-+))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (69 2 (:REWRITE FLOOR-ZERO . 3))
     (53 7 (:REWRITE INTEGERP-MINUS-X))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (36 2 (:REWRITE FLOOR-ZERO . 5))
     (34 4 (:REWRITE |(* (- x) y)|))
     (32 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (31 2 (:REWRITE FLOOR-ZERO . 4))
     (24 24 (:REWRITE DEFAULT-TIMES-2))
     (24 24 (:REWRITE DEFAULT-TIMES-1))
     (23 2 (:REWRITE FLOOR-=-X/Y . 3))
     (23 2 (:REWRITE FLOOR-=-X/Y . 2))
     (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (18 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (18 4 (:REWRITE |(- (* c x))|))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 2 (:REWRITE FLOOR-ZERO . 2))
     (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (10 2
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (10 2
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (9 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (6 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 1 (:REWRITE |(n32p x)|))
     (2 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(BREAK-LOGAND-APART
     (15998 28 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (15444 30 (:DEFINITION NATP))
     (12860 222 (:REWRITE THE-FLOOR-ABOVE))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5374 12 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (5374 12 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (4619 139 (:REWRITE DEFAULT-PLUS-1))
     (4545 139 (:REWRITE DEFAULT-PLUS-2))
     (4373 47 (:REWRITE NORMALIZE-ADDENDS))
     (2620 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2594 290
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (1636 28 (:REWRITE FLOOR-ZERO . 3))
     (1484 28 (:REWRITE CANCEL-FLOOR-+))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1428 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1428 14 (:DEFINITION FIX))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (952 28 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (920 226 (:REWRITE |(* y x)|))
     (906 638 (:REWRITE DEFAULT-TIMES-2))
     (850 206 (:REWRITE INTEGERP-MINUS-X))
     (844 28 (:REWRITE FLOOR-ZERO . 5))
     (844 28 (:REWRITE FLOOR-ZERO . 4))
     (802 208
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (748 28 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (684 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (684 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (654 638 (:REWRITE DEFAULT-TIMES-1))
     (616 28 (:REWRITE FLOOR-=-X/Y . 3))
     (616 28 (:REWRITE FLOOR-=-X/Y . 2))
     (538 34 (:REWRITE |(floor x 2)| . 2))
     (476 56 (:REWRITE |(* (- x) y)|))
     (422 34 (:REWRITE DEFAULT-FLOOR-RATIO))
     (364 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (360 208 (:REWRITE DEFAULT-LESS-THAN-1))
     (354 354
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (308 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (290 194
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (290 194
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (280 56 (:REWRITE DEFAULT-MINUS))
     (274 274
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (252 56 (:REWRITE |(- (* c x))|))
     (237 237
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (222 222 (:REWRITE THE-FLOOR-BELOW))
     (218 194
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (208 208 (:REWRITE DEFAULT-LESS-THAN-2))
     (194 194 (:REWRITE SIMPLIFY-SUMS-<))
     (194 194
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (194 194
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (194 194 (:REWRITE INTEGERP-<-CONSTANT))
     (194 194 (:REWRITE CONSTANT-<-INTEGERP))
     (194 194
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (194 194
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (194 194
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (194 194
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (194 194 (:REWRITE |(< c (- x))|))
     (194 194
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (194 194 (:REWRITE |(< (/ x) (/ y))|))
     (194 194 (:REWRITE |(< (- x) c)|))
     (194 194 (:REWRITE |(< (- x) (- y))|))
     (178 178 (:REWRITE REDUCE-INTEGERP-+))
     (178 178 (:META META-INTEGERP-CORRECT))
     (160 160 (:REWRITE |(< (* x y) 0)|))
     (146 146
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (146 146
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (146 146 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (146 146 (:REWRITE |(< (/ x) 0)|))
     (140 140 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (140 140 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (140 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (140 140 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (140 28 (:REWRITE FLOOR-ZERO . 2))
     (140 28 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (140 28 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (140 28
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (140 28
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (124 28 (:REWRITE FLOOR-CANCEL-*-CONST))
     (110 10 (:REWRITE DEFAULT-MOD-RATIO))
     (88 4 (:LINEAR MOD-BOUNDS-3))
     (62 62 (:TYPE-PRESCRIPTION ABS))
     (50 34 (:REWRITE DEFAULT-FLOOR-1))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (38 38
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (34 34 (:REWRITE DEFAULT-FLOOR-2))
     (33 33
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (28 28 (:REWRITE |(floor x (- y))| . 2))
     (28 28 (:REWRITE |(floor x (- y))| . 1))
     (28 28
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (28 28
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (28 28 (:REWRITE |(floor (- x) y)| . 2))
     (28 28 (:REWRITE |(floor (- x) y)| . 1))
     (28 28
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< 0 (/ x))|))
     (24 24 (:REWRITE |(< 0 (* x y))|))
     (20 20 (:TYPE-PRESCRIPTION NATP))
     (20 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (17 17 (:REWRITE LOGAND-CONSTANT-MASK))
     (14 14 (:REWRITE |(+ x (- x))|))
     (10 10 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (10 2 (:REWRITE O-INFP->NEQ-0))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(LOGIOR-THM-100
     (11551 5 (:REWRITE FLOOR-=-X/Y . 4))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7483 263 (:REWRITE THE-FLOOR-ABOVE))
     (3369 6 (:LINEAR BINARY-LOGAND->=-0))
     (3254 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3243 383
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3222 386 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3222 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3211 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3120 6 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (3114 6 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (3114 6 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (3097 59 (:REWRITE DEFAULT-PLUS-1))
     (2908 6 (:DEFINITION NATP))
     (2769 59 (:REWRITE DEFAULT-PLUS-2))
     (2486 14 (:REWRITE NORMALIZE-ADDENDS))
     (2056 20 (:REWRITE FLOOR-ZERO . 3))
     (1906 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1906 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1895 383
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1886 386 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1886 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1886 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (1875 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1875 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1732 20 (:REWRITE FLOOR-ZERO . 5))
     (1648 20 (:REWRITE CANCEL-FLOOR-+))
     (1586 370 (:REWRITE DEFAULT-TIMES-2))
     (1314 1314
           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (1314 1314
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (1314 1314
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (1136 20 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1092 12 (:REWRITE |(< 0 (logior x y))|))
     (1012 20 (:REWRITE FLOOR-ZERO . 4))
     (1008 40 (:REWRITE |(< (logior x y) 0)|))
     (992 20 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (835 370 (:REWRITE DEFAULT-TIMES-1))
     (816 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (816 8 (:DEFINITION FIX))
     (773 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (773 8
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (758 118 (:REWRITE INTEGERP-MINUS-X))
     (668 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (608 20 (:REWRITE FLOOR-=-X/Y . 3))
     (608 20 (:REWRITE FLOOR-=-X/Y . 2))
     (604 70 (:LINEAR LOGIOR-BOUNDS-POS . 2))
     (604 70 (:LINEAR LOGIOR-BOUNDS-POS . 1))
     (587 70 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (580 40 (:REWRITE |(* (- x) y)|))
     (555 211
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (483 211 (:REWRITE DEFAULT-LESS-THAN-1))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (443 203
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (443 203
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (320 40 (:REWRITE DEFAULT-MINUS))
     (300 40 (:REWRITE |(- (* c x))|))
     (285 9
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (281 281
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (263 263 (:REWRITE THE-FLOOR-BELOW))
     (233 6 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (223 203
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (211 211 (:REWRITE DEFAULT-LESS-THAN-2))
     (203 203 (:REWRITE SIMPLIFY-SUMS-<))
     (203 203
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (203 203
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (203 203 (:REWRITE INTEGERP-<-CONSTANT))
     (203 203 (:REWRITE CONSTANT-<-INTEGERP))
     (203 203
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (203 203
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (203 203
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (203 203
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (203 203 (:REWRITE |(< c (- x))|))
     (203 203
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (203 203
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (203 203
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (203 203
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (203 203 (:REWRITE |(< (/ x) (/ y))|))
     (203 203 (:REWRITE |(< (- x) c)|))
     (203 203 (:REWRITE |(< (- x) (- y))|))
     (187 187
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (174 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (163 163 (:REWRITE |(< (* x y) 0)|))
     (160 20 (:REWRITE FLOOR-ZERO . 2))
     (160 20 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (160 20 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (160 20 (:REWRITE FLOOR-CANCEL-*-CONST))
     (155 155
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (155 155
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (155 155 (:REWRITE |(< (/ x) 0)|))
     (142 142 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (106 1 (:REWRITE O-INFP->NEQ-0))
     (98 98 (:REWRITE REDUCE-INTEGERP-+))
     (98 98 (:META META-INTEGERP-CORRECT))
     (96 12 (:REWRITE RATIONALP-X))
     (94 70 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (90 20
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (90 20
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (90 20
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (90 20
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (66 22 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (50 50 (:TYPE-PRESCRIPTION ABS))
     (50 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (50 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (34 2 (:REWRITE |(* (if a b c) x)|))
     (30 4
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (28 28
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (26 26 (:REWRITE DEFAULT-FLOOR-2))
     (26 26 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< 0 (* x y))|))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (22 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (22 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20 (:REWRITE |(floor x (- y))| . 2))
     (20 20 (:REWRITE |(floor x (- y))| . 1))
     (20 20
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (20 20
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (20 20 (:REWRITE |(floor (- x) y)| . 2))
     (20 20 (:REWRITE |(floor (- x) y)| . 1))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (13 13 (:REWRITE DEFAULT-LOGAND-1))
     (12 12 (:REWRITE RATIONALP-MINUS-X))
     (11 11 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (11 11 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE LOGAND-CONSTANT-MASK))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE DEFAULT-LOGIOR-1))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(+ x (- x))|))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:LINEAR BINARY-LOGAND-<=))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(CROCK-200
 (190 190
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (175 5 (:REWRITE MOD-X-Y-=-X . 4))
 (110 5 (:REWRITE MOD-ZERO . 3))
 (90 5 (:REWRITE MOD-ZERO . 4))
 (55 5 (:REWRITE DEFAULT-MOD-RATIO))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (40 40 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (40 10 (:REWRITE |(* y x)|))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (25 5 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (23 19 (:REWRITE DEFAULT-LOGAND-2))
 (20 20 (:REWRITE DEFAULT-TIMES-2))
 (20 20 (:REWRITE DEFAULT-TIMES-1))
 (19 19 (:REWRITE DEFAULT-LOGAND-1))
 (17
   17
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (17
  17
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (17 17
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (15 15 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (9 5 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-MOD-2))
 (5 5 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
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
 (5 5 (:META META-INTEGERP-CORRECT)))
(ASH-THM-103
     (168 168
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (122 122
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (122 122
          (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (72 16 (:REWRITE DEFAULT-LOGAND-2))
     (38 1 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (25 4 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (25 4 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (16 16 (:REWRITE LOGAND-CONSTANT-MASK))
     (16 16 (:REWRITE DEFAULT-LOGAND-1))
     (12 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (12 1
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (12 1
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (8 4 (:REWRITE DEFAULT-LOGIOR-2))
     (6 6
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
     (4 4 (:REWRITE DEFAULT-LOGIOR-1))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 1 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1 (:REWRITE |(equal c (/ x))|))
     (1 1 (:REWRITE |(equal c (- x))|))
     (1 1 (:REWRITE |(equal (/ x) c)|))
     (1 1 (:REWRITE |(equal (/ x) (/ y))|))
     (1 1 (:REWRITE |(equal (- x) c)|))
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(ASH-THM-101
     (2537 25 (:REWRITE THE-FLOOR-BELOW))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (482 482
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (385 5 (:REWRITE CANCEL-FLOOR-+))
     (353 5 (:REWRITE FLOOR-ZERO . 3))
     (325 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (312 1 (:REWRITE FLOOR-=-X/Y . 4))
     (292 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (225 25 (:REWRITE DEFAULT-LESS-THAN-2))
     (214 5 (:REWRITE FLOOR-ZERO . 5))
     (203 5 (:REWRITE FLOOR-ZERO . 4))
     (198 18 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (191 26 (:REWRITE INTEGERP-MINUS-X))
     (175 83 (:REWRITE DEFAULT-TIMES-2))
     (163 3
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (161 83 (:REWRITE DEFAULT-TIMES-1))
     (161 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (161 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (160 5 (:REWRITE FLOOR-=-X/Y . 3))
     (160 5 (:REWRITE FLOOR-=-X/Y . 2))
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
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (125 10 (:REWRITE |(* (- x) y)|))
     (123 15 (:LINEAR BINARY-LOGAND-<=))
     (107 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (101 2
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (101 2
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (94 15 (:LINEAR BINARY-LOGAND->=-0))
     (93 3 (:DEFINITION NATP))
     (76 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (70 10 (:REWRITE DEFAULT-MINUS))
     (65 10 (:REWRITE |(- (* c x))|))
     (64 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (59 25 (:REWRITE DEFAULT-LESS-THAN-1))
     (45 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (43 43
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (35 5 (:REWRITE FLOOR-ZERO . 2))
     (35 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (35 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (34 34 (:REWRITE LOGAND-CONSTANT-MASK))
     (34 34 (:REWRITE DEFAULT-LOGAND-1))
     (27 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (27 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (25 25 (:REWRITE THE-FLOOR-ABOVE))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
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
     (23 5
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (23 5 (:REWRITE FLOOR-CANCEL-*-CONST))
     (23 5
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (21 21 (:REWRITE REDUCE-INTEGERP-+))
     (21 21 (:META META-INTEGERP-CORRECT))
     (18 18 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (18 18 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (18 6 (:REWRITE DEFAULT-FLOOR-1))
     (17 5
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (17 5
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 4 (:REWRITE DEFAULT-PLUS-2))
     (16 4 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:TYPE-PRESCRIPTION NATP))
     (15 3
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (11 1 (:REWRITE |(* (if a b c) x)|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 3
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (7 7 (:TYPE-PRESCRIPTION ABS))
     (7 1
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE |(floor x (- y))| . 2))
     (5 5 (:REWRITE |(floor x (- y))| . 1))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (5 5 (:REWRITE |(floor (- x) y)| . 2))
     (5 5 (:REWRITE |(floor (- x) y)| . 1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 1 (:REWRITE |(* a (/ a) b)|))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(ASH-THM-102
     (303 5 (:REWRITE DEFAULT-PLUS-1))
     (302 5 (:REWRITE DEFAULT-PLUS-2))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (234 2 (:REWRITE FLOOR-ZERO . 3))
     (203 203
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (154 2 (:REWRITE CANCEL-FLOOR-+))
     (143 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (140 2 (:REWRITE FLOOR-ZERO . 5))
     (134 2 (:REWRITE FLOOR-ZERO . 4))
     (133 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (128 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (98 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (78 12 (:REWRITE INTEGERP-MINUS-X))
     (78 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (68 34 (:REWRITE DEFAULT-TIMES-2))
     (68 34 (:REWRITE DEFAULT-TIMES-1))
     (64 2 (:REWRITE FLOOR-=-X/Y . 3))
     (64 2 (:REWRITE FLOOR-=-X/Y . 2))
     (60 8 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (55 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (55 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (50 4 (:REWRITE |(* (- x) y)|))
     (48 8 (:LINEAR BINARY-LOGAND->=-0))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (39 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 4 (:REWRITE DEFAULT-MINUS))
     (26 4 (:REWRITE |(- (* c x))|))
     (22 2 (:REWRITE |(* (if a b c) x)|))
     (18 18 (:REWRITE LOGAND-CONSTANT-MASK))
     (18 18 (:REWRITE DEFAULT-LOGAND-1))
     (18 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (17 17
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (16 8 (:LINEAR BINARY-LOGAND-<=))
     (14 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 2 (:REWRITE FLOOR-ZERO . 2))
     (14 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (14 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (14 2
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (14 2
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (12 9
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 9
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 4 (:REWRITE DEFAULT-FLOOR-1))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:META META-INTEGERP-CORRECT))
     (10 2
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
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
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (8 8 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (8 8 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 2
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(init_pdpt-pre s)|
 (2293 1988 (:REWRITE DEFAULT-PLUS-2))
 (2168 1988 (:REWRITE DEFAULT-PLUS-1))
 (1478 58
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1175 1175
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1140
  51
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (815 815
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (592 6
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (380 380
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (380 380
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (360 3 (:REWRITE DISJOINT-3-ITEMS))
 (247 77 (:REWRITE DEFAULT-LOGAND-2))
 (236
   236
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (236
  236
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (236
     236
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (194 194
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (143 62 (:REWRITE DEFAULT-LESS-THAN-1))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (80 17 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (80 17 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (78 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (77 77 (:REWRITE DEFAULT-LOGAND-1))
 (73 73 (:REWRITE LOGAND-CONSTANT-MASK))
 (73 62 (:REWRITE DEFAULT-LESS-THAN-2))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (60 34
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (58 58
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (58 58
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 31 (:REWRITE DEFAULT-TIMES-2))
 (55 31 (:REWRITE DEFAULT-TIMES-1))
 (46 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 39
     (:REWRITE |(g field (w32 addr val st))|))
 (39 39 (:REWRITE |(< (+ c/d x) y)|))
 (36 12 (:REWRITE DEFAULT-LOGIOR-2))
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
 (33 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 26 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:REWRITE DEFAULT-LOGIOR-1))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (11 1 (:REWRITE DISJOINT-8-ITEMS))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(init_pdts-pre s)|
 (11992 8991 (:REWRITE DEFAULT-PLUS-2))
 (10145 8991 (:REWRITE DEFAULT-PLUS-1))
 (6786 6
       (:REWRITE |(good-state-p (s field val) s) --- n01p|))
 (5843 5843
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3409 3409
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (1849
  1244
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1493 1493
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1157
   1157
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1157
  1157
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1157
      1157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1157
     1157
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1157 1157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1157 1157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1098 48
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1019 745 (:REWRITE DEFAULT-LOGAND-2))
 (745 745 (:REWRITE LOGAND-CONSTANT-MASK))
 (745 745 (:REWRITE DEFAULT-LOGAND-1))
 (662 19
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (386 386
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (386 386
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (328 287 (:REWRITE DEFAULT-TIMES-2))
 (287 287
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (287 287 (:REWRITE DEFAULT-TIMES-1))
 (246 246 (:REWRITE FOLD-CONSTS-IN-+))
 (196 172 (:REWRITE DEFAULT-LOGIOR-2))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (172 172 (:REWRITE DEFAULT-LOGIOR-1))
 (115 115
      (:REWRITE |(g field (w32 addr val st))|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (73 48 (:REWRITE DEFAULT-LESS-THAN-1))
 (73 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (68 13 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (68 13 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (59 48 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (55 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (48 48 (:REWRITE THE-FLOOR-BELOW))
 (48 48 (:REWRITE THE-FLOOR-ABOVE))
 (48 48
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (46 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (33 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (29 29 (:REWRITE |(< (- x) (- y))|))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (18 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(create_nested_pt-pre s)|
 (186370 141115 (:REWRITE DEFAULT-PLUS-2))
 (159959 141115 (:REWRITE DEFAULT-PLUS-1))
 (100315 100315
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (65352 48
        (:REWRITE |(good-state-p (s field val) s) --- n01p|))
 (63804 63804
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (38519
  23456
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (34791 899
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28484 512
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (21770 15456 (:REWRITE DEFAULT-LOGAND-2))
 (21390 21390
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (20838
   20838
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20838
  20838
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20838
      20838
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20838
     20838
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20838 20838
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20838 20838
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15528 15456 (:REWRITE DEFAULT-LOGAND-1))
 (15456 15456 (:REWRITE LOGAND-CONSTANT-MASK))
 (4768 4768
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4768 4768 (:REWRITE FOLD-CONSTS-IN-+))
 (4768 4768 (:REWRITE DEFAULT-TIMES-2))
 (4768 4768 (:REWRITE DEFAULT-TIMES-1))
 (3892 112
       (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (3694 3694
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (3694 3694
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (3396 3212 (:REWRITE DEFAULT-LOGIOR-2))
 (3212 3212 (:REWRITE DEFAULT-LOGIOR-1))
 (2767 881 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (2767 881 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (2644 2644
       (:REWRITE |(g field (w32 addr val st))|))
 (1694 899 (:REWRITE DEFAULT-LESS-THAN-1))
 (1688 120 (:REWRITE |(n32-to-i32 x) --- 2|))
 (1656 120 (:REWRITE |(n32-to-i32 x) --- 1|))
 (974 899 (:REWRITE DEFAULT-LESS-THAN-2))
 (931 492
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (931 492
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (920 20 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (899 899 (:REWRITE THE-FLOOR-BELOW))
 (899 899 (:REWRITE THE-FLOOR-ABOVE))
 (899 899
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (899 899
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (599 599 (:REWRITE |(< (+ c/d x) y)|))
 (508 508 (:REWRITE INTEGERP-<-CONSTANT))
 (508 508 (:REWRITE CONSTANT-<-INTEGERP))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< c (- x))|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< (/ x) (/ y))|))
 (508 508 (:REWRITE |(< (- x) c)|))
 (508 508 (:REWRITE |(< (- x) (- y))|))
 (448 84
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (448 84
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (432 84 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (416 384 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (208 208 (:REWRITE |(< (+ (- c) x) y)|))
 (187 187 (:REWRITE |(< x (+ c/d y))|))
 (120 120 (:REWRITE |(< (* x y) 0)|))
 (84 84
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (84 84 (:REWRITE |(equal c (/ x))|))
 (84 84 (:REWRITE |(equal c (- x))|))
 (84 84 (:REWRITE |(equal (/ x) c)|))
 (84 84 (:REWRITE |(equal (/ x) (/ y))|))
 (84 84 (:REWRITE |(equal (- x) c)|))
 (84 84 (:REWRITE |(equal (- x) (- y))|))
 (60 20 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (40 40 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (36 36 (:REWRITE |(< 0 (/ x))|))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(|(y86-p (create_nested_pt-modify s))|
 (8510 5098 (:REWRITE DEFAULT-PLUS-2))
 (6908 5098 (:REWRITE DEFAULT-PLUS-1))
 (6078
  6078
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (5989 5989
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (4528 4528
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4528 4528 (:REWRITE NORMALIZE-ADDENDS))
 (4000 252
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3289 1
       (:REWRITE |(g :esp (sec_not_present-modify s))|))
 (3289 1
       (:REWRITE |(g :eip (sec_not_present-modify s))|))
 (3289 1
       (:REWRITE |(g :ebp (sec_not_present-modify s))|))
 (2986 2986
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2801 1467 (:REWRITE DEFAULT-LOGAND-2))
 (2427 75 (:REWRITE |(n32-to-i32 x) --- 2|))
 (2379 75 (:REWRITE |(n32-to-i32 x) --- 1|))
 (2144 2144
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2144 2144
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2144 2144
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1468 384 (:REWRITE DEFAULT-LESS-THAN-1))
 (1467 1467 (:REWRITE DEFAULT-LOGAND-1))
 (1335 1335 (:REWRITE LOGAND-CONSTANT-MASK))
 (870
  870
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (870
  870
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (760 760
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (760 760
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (624 511 (:REWRITE DEFAULT-TIMES-2))
 (608
   608
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (608
  608
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (608 608
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (608
     608
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (608 608
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (608 608
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (591 511 (:REWRITE DEFAULT-TIMES-1))
 (420 250 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (420 250 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (396 384 (:REWRITE DEFAULT-LESS-THAN-2))
 (384 384 (:REWRITE THE-FLOOR-BELOW))
 (384 384 (:REWRITE THE-FLOOR-ABOVE))
 (371 371
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (330 330 (:REWRITE FOLD-CONSTS-IN-+))
 (252 252
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (252 252
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (234 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (234 36
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (234 36
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (234 14 (:REWRITE |(+ y (+ x z))|))
 (228 140
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (220 140 (:REWRITE DEFAULT-LOGIOR-2))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (180 140
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (180 140
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (174 174 (:REWRITE REDUCE-INTEGERP-+))
 (174 174 (:REWRITE INTEGERP-MINUS-X))
 (174 174 (:META META-INTEGERP-CORRECT))
 (146 140 (:REWRITE SIMPLIFY-SUMS-<))
 (140 140 (:REWRITE INTEGERP-<-CONSTANT))
 (140 140 (:REWRITE DEFAULT-LOGIOR-1))
 (140 140 (:REWRITE CONSTANT-<-INTEGERP))
 (140 140
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (140 140
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (140 140
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (140 140
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (140 140 (:REWRITE |(< c (- x))|))
 (140 140
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (140 140
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (140 140
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (140 140 (:REWRITE |(< (/ x) (/ y))|))
 (140 140 (:REWRITE |(< (- x) c)|))
 (140 140 (:REWRITE |(< (- x) (- y))|))
 (134 58 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (116 116 (:REWRITE |(< (+ c/d x) y)|))
 (36 36
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (36 36
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (36 36
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (36 36 (:REWRITE |(equal c (/ x))|))
 (36 36 (:REWRITE |(equal c (- x))|))
 (36 36 (:REWRITE |(equal (/ x) c)|))
 (36 36 (:REWRITE |(equal (/ x) (/ y))|))
 (36 36 (:REWRITE |(equal (- x) c)|))
 (36 36 (:REWRITE |(equal (- x) (- y))|))
 (25 25 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(< (* x y) 0)|)))
(|(g :cr0 (create_nested_pt-modify s))|
 (1373 1373
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1014 564 (:REWRITE DEFAULT-PLUS-2))
 (788 564 (:REWRITE DEFAULT-PLUS-1))
 (589
  589
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (565 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (492 492
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (492 492 (:REWRITE NORMALIZE-ADDENDS))
 (394 164 (:REWRITE DEFAULT-LOGAND-2))
 (380 380
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (380 380
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (331 331
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (288 288
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (288 288
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (288 288
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (201 49 (:REWRITE DEFAULT-LESS-THAN-1))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (164 164 (:REWRITE DEFAULT-LOGAND-1))
 (148 148 (:REWRITE LOGAND-CONSTANT-MASK))
 (117 7 (:REWRITE |(+ y (+ x z))|))
 (104 76 (:REWRITE DEFAULT-TIMES-2))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (100 76 (:REWRITE DEFAULT-TIMES-1))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (92 29 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (92 29 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (85
  85
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (85
  85
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (65 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (63
   63
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (63
  63
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (63 63
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (63 63
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (63 63
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (63 63
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (59 49 (:REWRITE DEFAULT-LESS-THAN-2))
 (52 52
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (48 24 (:REWRITE DEFAULT-LOGIOR-2))
 (45 21
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (45 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (45 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (40 40 (:REWRITE FOLD-CONSTS-IN-+))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (33 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:REWRITE DEFAULT-LOGIOR-1))
 (24 24 (:META META-INTEGERP-CORRECT))
 (24 21 (:REWRITE SIMPLIFY-SUMS-<))
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
 (14 14 (:REWRITE |(< (+ c/d x) y)|))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(r32 addr (create_nested_pt-modify s)) --- init_pdpt|
 (2972614 2220863 (:REWRITE DEFAULT-PLUS-2))
 (2533227 2220863 (:REWRITE DEFAULT-PLUS-1))
 (1534927 1534927
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (943700 943700
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (848016
  347380
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (771746 6548
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (322528 222084 (:REWRITE DEFAULT-LOGAND-2))
 (306128
   306128
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (306128
  306128
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (306128
      306128
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (306128
     306128
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (306128 306128
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (306128 306128
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (261938 261938
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (222084 222084 (:REWRITE LOGAND-CONSTANT-MASK))
 (222084 222084 (:REWRITE DEFAULT-LOGAND-1))
 (216986 11034 (:REWRITE SIMPLIFY-SUMS-<))
 (90300 80084 (:REWRITE DEFAULT-TIMES-2))
 (80124 80084 (:REWRITE DEFAULT-TIMES-1))
 (79172 79172
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (75308 75308 (:REWRITE FOLD-CONSTS-IN-+))
 (67623 67623
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (67623 67623
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (50088 3048 (:REWRITE |(n32-to-i32 x) --- 2|))
 (49880 47536 (:REWRITE DEFAULT-LOGIOR-2))
 (49128 3048 (:REWRITE |(n32-to-i32 x) --- 1|))
 (47536 47536 (:REWRITE DEFAULT-LOGIOR-1))
 (40808 1108
        (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (36548 36548
        (:REWRITE |(g field (w32 addr val st))|))
 (35936 10504 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (35936 10504 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (30646 20766
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30490 20766 (:REWRITE DEFAULT-LESS-THAN-1))
 (23090 20766 (:REWRITE DEFAULT-LESS-THAN-2))
 (20766 20766 (:REWRITE THE-FLOOR-BELOW))
 (20766 20766 (:REWRITE THE-FLOOR-ABOVE))
 (20726 20646
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (19142 11366
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15776 15776 (:REWRITE |(< (+ c/d x) y)|))
 (15744 12884 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (14918 11366
        (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (13086 11506 (:REWRITE |(< c (- x))|))
 (12766 11446 (:REWRITE CONSTANT-<-INTEGERP))
 (12726 11406 (:REWRITE INTEGERP-<-CONSTANT))
 (11838 11506 (:REWRITE |(< (- x) (- y))|))
 (11696 1648
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11696 1648
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11680 1648 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (11506 11506
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (11506 11506
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (11506 11506
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (11506 11506
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (11506 11506
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (11506 11506
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (11506 11506
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (11506 11506
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (11506 11506 (:REWRITE |(< (/ x) (/ y))|))
 (9932 302 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (6636 6636 (:REWRITE |(< (+ (- c) x) y)|))
 (6340 3292
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5808 5808 (:REWRITE |(< x (+ c/d y))|))
 (3040 40
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1648 1648
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1648 1648
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1648 1648
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1648 1648 (:REWRITE |(equal c (/ x))|))
 (1648 1648 (:REWRITE |(equal c (- x))|))
 (1648 1648 (:REWRITE |(equal (/ x) c)|))
 (1648 1648 (:REWRITE |(equal (/ x) (/ y))|))
 (1648 1648 (:REWRITE |(equal (- x) c)|))
 (1648 1648 (:REWRITE |(equal (- x) (- y))|))
 (1608 784 (:REWRITE DEFAULT-MINUS))
 (1604 1604 (:REWRITE |(< (* x y) 0)|))
 (1200 80 (:REWRITE |(* y (* x z))|))
 (1016 1016
       (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (588 588 (:REWRITE |(* (- x) y)|))
 (412 412 (:REWRITE |(< y (+ (- c) x))|))
 (406 406 (:REWRITE |(< 0 (/ x))|))
 (406 406 (:REWRITE |(< 0 (* x y))|))
 (386 386
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (386 386
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (352 352 (:REWRITE |(< (/ x) 0)|))
 (338 302 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (332 332
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (332 332
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (280 280 (:TYPE-PRESCRIPTION ABS))
 (240 40 (:REWRITE |(* y x)|))
 (240 40 (:REWRITE |(* c (* d x))|))
 (160 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (160 80 (:REWRITE |(* a (/ a) b)|))
 (84 84 (:REWRITE |(equal (+ (- c) x) y)|))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (80 40
     (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(|(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
 (6661918 68
          (:REWRITE |(r32 addr (sec_not_present-modify s))|))
 (726560 547736 (:REWRITE DEFAULT-PLUS-2))
 (625428 547736 (:REWRITE DEFAULT-PLUS-1))
 (396790 380092 (:REWRITE NORMALIZE-ADDENDS))
 (377644 377644
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (260806 1728 (:REWRITE SIMPLIFY-SUMS-<))
 (232140 232140
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (120992 1120
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (102398 3254
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (80946 55760 (:REWRITE DEFAULT-LOGAND-2))
 (74139
   74139
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (74139
  74139
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (74139
      74139
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (74139
     74139
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (74139 74139
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (74139 74139
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (57259 57259
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (55760 55760 (:REWRITE LOGAND-CONSTANT-MASK))
 (55760 55760 (:REWRITE DEFAULT-LOGAND-1))
 (21748 19712 (:REWRITE DEFAULT-TIMES-2))
 (19735 19712 (:REWRITE DEFAULT-TIMES-1))
 (19452 19452
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (18730 18730 (:REWRITE FOLD-CONSTS-IN-+))
 (11826 11584 (:REWRITE DEFAULT-LOGIOR-2))
 (11584 11584 (:REWRITE DEFAULT-LOGIOR-1))
 (10542 3353
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10195 3030 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (10195 3030 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (7655 7655
       (:REWRITE |(g field (w32 addr val st))|))
 (7130 62 (:DEFINITION MAX))
 (6441 1790
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4624 2312 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (4385 3703 (:DEFINITION FIX))
 (4154 3353 (:REWRITE DEFAULT-LESS-THAN-1))
 (3896 270 (:REWRITE |(n32-to-i32 x) --- 2|))
 (3882 3353 (:REWRITE DEFAULT-LESS-THAN-2))
 (3822 270 (:REWRITE |(n32-to-i32 x) --- 1|))
 (3353 3353 (:REWRITE THE-FLOOR-BELOW))
 (3353 3353 (:REWRITE THE-FLOOR-ABOVE))
 (3304 3254
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2886 1857 (:REWRITE CONSTANT-<-INTEGERP))
 (2882 2448 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2853 1824 (:REWRITE INTEGERP-<-CONSTANT))
 (2843 1882 (:REWRITE |(< c (- x))|))
 (2779 1790
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2666 2666 (:REWRITE |(< (+ c/d x) y)|))
 (2440 2440 (:REWRITE |(+ x (- x))|))
 (2386 2386
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2386 2386
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1944 1882 (:REWRITE |(< (- x) (- y))|))
 (1919 1857 (:REWRITE |(< (- x) c)|))
 (1889 1791
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1882 1882
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1882 1882
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1882 1882
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1882 1882
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1882 1882
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1882 1882
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1882 1882
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1882 1882
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1882 1882 (:REWRITE |(< (/ x) (/ y))|))
 (1880 33
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1271 199
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1271 199
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1182 1182 (:REWRITE |(< x (+ c/d y))|))
 (1143 199 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (930 66 (:REWRITE |(* y (* x z))|))
 (888 136 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (831 87 (:REWRITE |(* x (- y))|))
 (582 13 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (495 87 (:REWRITE |(- (* c x))|))
 (296 149 (:REWRITE DEFAULT-MINUS))
 (252 252 (:REWRITE |(* (- x) y)|))
 (205 1
      (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (199 199 (:TYPE-PRESCRIPTION ABS))
 (199 199
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (199 199
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (199 199
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (199 199 (:REWRITE |(equal c (/ x))|))
 (199 199 (:REWRITE |(equal c (- x))|))
 (199 199 (:REWRITE |(equal (/ x) c)|))
 (199 199 (:REWRITE |(equal (/ x) (/ y))|))
 (199 199 (:REWRITE |(equal (- x) c)|))
 (199 199 (:REWRITE |(equal (- x) (- y))|))
 (188 33 (:REWRITE |(* c (* d x))|))
 (148 25 (:REWRITE |(* y x)|))
 (143 143 (:REWRITE |(< (* x y) 0)|))
 (139 20 (:REWRITE O-INFP->NEQ-0))
 (134 134 (:REWRITE |(< y (+ (- c) x))|))
 (112 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (112 66 (:REWRITE |(* a (/ a) b)|))
 (90 90 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (78 6 (:DEFINITION NATP))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (66 66 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (56 33
     (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (34 34 (:REWRITE |(< (/ x) 0)|))
 (32 8 (:REWRITE |(+ (* c x) (* d x))|))
 (31 13 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (27 27
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (27 27 (:REWRITE |(< 0 (/ x))|))
 (27 27 (:REWRITE |(< 0 (* x y))|))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 14 (:REWRITE REDUCE-INTEGERP-+))
 (14 14 (:REWRITE INTEGERP-MINUS-X))
 (14 14 (:REWRITE |(equal (+ (- c) x) y)|))
 (14 14 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(* 0 x)|))
 (6 6 (:TYPE-PRESCRIPTION NATP)))
(CROCK-333-1)
(CROCK-333 (111 27 (:REWRITE ACL2-NUMBERP-X))
           (110 11
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
           (65 58 (:REWRITE DEFAULT-PLUS-1))
           (58 58 (:REWRITE DEFAULT-PLUS-2))
           (42 9 (:REWRITE RATIONALP-X))
           (26 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (26 11
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (22 22 (:REWRITE REDUCE-INTEGERP-+))
           (22 22 (:REWRITE INTEGERP-MINUS-X))
           (22 22 (:META META-INTEGERP-CORRECT))
           (19 19 (:REWRITE THE-FLOOR-BELOW))
           (19 19 (:REWRITE THE-FLOOR-ABOVE))
           (19 19
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (19 19
               (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (19 19
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (19 19
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (19 19
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (19 19 (:REWRITE INTEGERP-<-CONSTANT))
           (19 19 (:REWRITE DEFAULT-LESS-THAN-2))
           (19 19 (:REWRITE DEFAULT-LESS-THAN-1))
           (19 19 (:REWRITE CONSTANT-<-INTEGERP))
           (19 19
               (:REWRITE |(< c (/ x)) positive c --- present in goal|))
           (19 19
               (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
           (19 19
               (:REWRITE |(< c (/ x)) negative c --- present in goal|))
           (19 19
               (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
           (19 19 (:REWRITE |(< c (- x))|))
           (19 19
               (:REWRITE |(< (/ x) c) positive c --- present in goal|))
           (19 19
               (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
           (19 19
               (:REWRITE |(< (/ x) c) negative c --- present in goal|))
           (19 19
               (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
           (19 19 (:REWRITE |(< (/ x) (/ y))|))
           (19 19 (:REWRITE |(< (- x) c)|))
           (19 19 (:REWRITE |(< (- x) (- y))|))
           (12 12 (:REWRITE SIMPLIFY-SUMS-<))
           (12 10 (:REWRITE DEFAULT-CDR))
           (12 10 (:REWRITE DEFAULT-CAR))
           (11 11
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
           (11 11
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
           (11 11
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
           (11 11 (:REWRITE |(equal c (/ x))|))
           (11 11 (:REWRITE |(equal c (- x))|))
           (11 11 (:REWRITE |(equal (/ x) c)|))
           (11 11 (:REWRITE |(equal (/ x) (/ y))|))
           (11 11 (:REWRITE |(equal (- x) c)|))
           (11 11 (:REWRITE |(equal (- x) (- y))|))
           (9 9 (:REWRITE REDUCE-RATIONALP-+))
           (9 9 (:REWRITE REDUCE-RATIONALP-*))
           (9 9 (:REWRITE RATIONALP-MINUS-X))
           (9 9
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (9 9 (:META META-RATIONALP-CORRECT))
           (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (7 7 (:REWRITE DEFAULT-MINUS))
           (7 7 (:REWRITE |(< (/ x) 0)|))
           (7 7 (:REWRITE |(< (+ c/d x) y)|))
           (7 7 (:REWRITE |(< (+ (- c) x) y)|))
           (7 7 (:REWRITE |(< (* x y) 0)|)))
(CROCK-334 (111 27 (:REWRITE ACL2-NUMBERP-X))
           (111 12
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
           (104 4 (:REWRITE CROCK-333))
           (73 64 (:REWRITE DEFAULT-PLUS-1))
           (64 64 (:REWRITE DEFAULT-PLUS-2))
           (48 23
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (42 9 (:REWRITE RATIONALP-X))
           (28 13 (:REWRITE |(equal (/ x) c)|))
           (27 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (27 12
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (23 23 (:REWRITE THE-FLOOR-BELOW))
           (23 23 (:REWRITE THE-FLOOR-ABOVE))
           (23 23
               (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (23 23
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (23 23
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (23 23
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (23 23 (:REWRITE INTEGERP-<-CONSTANT))
           (23 23 (:REWRITE DEFAULT-LESS-THAN-2))
           (23 23 (:REWRITE DEFAULT-LESS-THAN-1))
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
           (22 22 (:REWRITE REDUCE-INTEGERP-+))
           (22 22 (:REWRITE INTEGERP-MINUS-X))
           (22 22 (:META META-INTEGERP-CORRECT))
           (19 19 (:REWRITE REMOVE-WEAK-INEQUALITIES))
           (13 13
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
           (13 13
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
           (13 13 (:REWRITE |(equal c (/ x))|))
           (13 13 (:REWRITE |(equal (/ x) (/ y))|))
           (13 13 (:REWRITE |(equal (- x) (- y))|))
           (12 12
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
           (12 12 (:REWRITE |(equal c (- x))|))
           (12 12 (:REWRITE |(equal (- x) c)|))
           (12 10 (:REWRITE DEFAULT-CDR))
           (12 10 (:REWRITE DEFAULT-CAR))
           (9 9 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (9 9 (:REWRITE REDUCE-RATIONALP-+))
           (9 9 (:REWRITE REDUCE-RATIONALP-*))
           (9 9 (:REWRITE RATIONALP-MINUS-X))
           (9 9
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (9 9 (:META META-RATIONALP-CORRECT))
           (7 7 (:REWRITE DEFAULT-MINUS))
           (7 7 (:REWRITE |(< (/ x) 0)|))
           (7 7 (:REWRITE |(< (+ c/d x) y)|))
           (7 7 (:REWRITE |(< (+ (- c) x) y)|))
           (7 7 (:REWRITE |(< (* x y) 0)|))
           (1 1
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
           (1 1 (:REWRITE O-INFP->NEQ-0))
           (1 1 (:REWRITE DEFAULT-DIVIDE))
           (1 1 (:REWRITE |(not (equal x (/ y)))|))
           (1 1 (:REWRITE |(equal x (/ y))|))
           (1 1 (:REWRITE |(/ (/ x))|)))
(CROCK-335-1 (154 42 (:REWRITE ACL2-NUMBERP-X))
             (140 14
                  (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (65 58 (:REWRITE DEFAULT-PLUS-1))
             (58 58 (:REWRITE DEFAULT-PLUS-2))
             (56 14 (:REWRITE RATIONALP-X))
             (35 35 (:REWRITE REDUCE-INTEGERP-+))
             (35 35 (:REWRITE INTEGERP-MINUS-X))
             (35 35 (:META META-INTEGERP-CORRECT))
             (28 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (28 14
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (16 14 (:REWRITE DEFAULT-CDR))
             (16 14 (:REWRITE DEFAULT-CAR))
             (16 4 (:REWRITE CROCK-334))
             (16 4 (:REWRITE CROCK-333))
             (14 14 (:REWRITE THE-FLOOR-BELOW))
             (14 14 (:REWRITE THE-FLOOR-ABOVE))
             (14 14
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
             (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
             (14 14
                 (:REWRITE REMOVE-STRICT-INEQUALITIES))
             (14 14 (:REWRITE REDUCE-RATIONALP-+))
             (14 14 (:REWRITE REDUCE-RATIONALP-*))
             (14 14
                 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
             (14 14
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (14 14
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
             (14 14
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (14 14
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
             (14 14 (:REWRITE RATIONALP-MINUS-X))
             (14 14 (:REWRITE INTEGERP-<-CONSTANT))
             (14 14
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
             (14 14 (:REWRITE DEFAULT-LESS-THAN-1))
             (14 14 (:REWRITE CONSTANT-<-INTEGERP))
             (14 14 (:REWRITE |(equal c (/ x))|))
             (14 14 (:REWRITE |(equal c (- x))|))
             (14 14 (:REWRITE |(equal (/ x) c)|))
             (14 14 (:REWRITE |(equal (/ x) (/ y))|))
             (14 14 (:REWRITE |(equal (- x) c)|))
             (14 14 (:REWRITE |(equal (- x) (- y))|))
             (14 14
                 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
             (14 14
                 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
             (14 14
                 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
             (14 14
                 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
             (14 14 (:REWRITE |(< c (- x))|))
             (14 14
                 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
             (14 14
                 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
             (14 14
                 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
             (14 14
                 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
             (14 14 (:REWRITE |(< (/ x) (/ y))|))
             (14 14 (:REWRITE |(< (- x) c)|))
             (14 14 (:REWRITE |(< (- x) (- y))|))
             (14 14 (:META META-RATIONALP-CORRECT))
             (9 9
                (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (7 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
             (7 7 (:REWRITE SIMPLIFY-SUMS-<))
             (7 7 (:REWRITE DEFAULT-MINUS))
             (7 7 (:REWRITE |(< (/ x) 0)|))
             (7 7 (:REWRITE |(< (+ c/d x) y)|))
             (7 7 (:REWRITE |(< (+ (- c) x) y)|))
             (7 7 (:REWRITE |(< (* x y) 0)|)))
(CROCK-335 (131 111 (:REWRITE DEFAULT-PLUS-1))
           (111 111 (:REWRITE DEFAULT-PLUS-2))
           (104 14
                (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
           (100 24 (:REWRITE ACL2-NUMBERP-X))
           (84 4 (:REWRITE CROCK-334))
           (79 29
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (46 16 (:REWRITE |(equal (/ x) c)|))
           (38 8 (:REWRITE RATIONALP-X))
           (36 36 (:REWRITE THE-FLOOR-BELOW))
           (36 36 (:REWRITE THE-FLOOR-ABOVE))
           (36 36
               (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
           (36 36
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
           (36 36
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
           (36 36 (:REWRITE DEFAULT-LESS-THAN-2))
           (36 36 (:REWRITE DEFAULT-LESS-THAN-1))
           (32 32
               (:REWRITE REMOVE-STRICT-INEQUALITIES))
           (32 32 (:REWRITE INTEGERP-<-CONSTANT))
           (32 32 (:REWRITE CONSTANT-<-INTEGERP))
           (32 32
               (:REWRITE |(< c (/ x)) positive c --- present in goal|))
           (32 32
               (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
           (32 32
               (:REWRITE |(< c (/ x)) negative c --- present in goal|))
           (32 32
               (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
           (32 32 (:REWRITE |(< c (- x))|))
           (32 32
               (:REWRITE |(< (/ x) c) positive c --- present in goal|))
           (32 32
               (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
           (32 32
               (:REWRITE |(< (/ x) c) negative c --- present in goal|))
           (32 32
               (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
           (32 32 (:REWRITE |(< (/ x) (/ y))|))
           (32 32 (:REWRITE |(< (- x) c)|))
           (32 32 (:REWRITE |(< (- x) (- y))|))
           (28 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (28 14
               (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (20 20 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
           (20 20 (:REWRITE REDUCE-INTEGERP-+))
           (20 20
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (20 20 (:REWRITE INTEGERP-MINUS-X))
           (20 20 (:META META-INTEGERP-CORRECT))
           (16 16
               (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
           (16 16
               (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
           (16 16 (:REWRITE |(equal c (/ x))|))
           (16 16 (:REWRITE |(equal (/ x) (/ y))|))
           (16 16 (:REWRITE |(equal (- x) (- y))|))
           (14 14
               (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
           (14 14 (:REWRITE |(equal c (- x))|))
           (14 14 (:REWRITE |(equal (- x) c)|))
           (14 12 (:REWRITE DEFAULT-CAR))
           (12 12 (:REWRITE DEFAULT-MINUS))
           (12 12 (:REWRITE |(< (+ c/d x) y)|))
           (12 10 (:REWRITE DEFAULT-CDR))
           (8 8 (:REWRITE REDUCE-RATIONALP-+))
           (8 8 (:REWRITE REDUCE-RATIONALP-*))
           (8 8 (:REWRITE RATIONALP-MINUS-X))
           (8 8 (:REWRITE |(< (/ x) 0)|))
           (8 8 (:REWRITE |(< (* x y) 0)|))
           (8 8 (:META META-RATIONALP-CORRECT))
           (4 4 (:REWRITE CROCK-333))
           (4 4 (:REWRITE |(< y (+ (- c) x))|))
           (4 4 (:REWRITE |(< x (+ c/d y))|))
           (2 2
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
           (2 2 (:REWRITE O-INFP->NEQ-0))
           (2 2 (:REWRITE DEFAULT-DIVIDE))
           (2 2 (:REWRITE CDR-CONS))
           (2 2 (:REWRITE |(not (equal x (/ y)))|))
           (2 2 (:REWRITE |(equal x (/ y))|))
           (2 2 (:REWRITE |(/ (/ x))|)))
(EXTRA-DISJOINTP-THM
     (909 9 (:DEFINITION RANGE-1))
     (441 27 (:REWRITE |(+ (+ x y) z)|))
     (241 106 (:REWRITE NORMALIZE-ADDENDS))
     (225 207 (:REWRITE DEFAULT-PLUS-1))
     (214 21 (:REWRITE |(< (+ (- c) x) y)|))
     (207 207 (:REWRITE DEFAULT-PLUS-2))
     (144 9 (:REWRITE |(+ y (+ x z))|))
     (93 48 (:REWRITE |(+ c (+ d x))|))
     (88 88
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (63 9 (:REWRITE |(- (+ x y))|))
     (45 9 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
     (40 40 (:REWRITE THE-FLOOR-BELOW))
     (40 40 (:REWRITE THE-FLOOR-ABOVE))
     (40 40
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (40 40
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (40 40 (:REWRITE DEFAULT-LESS-THAN-2))
     (40 40 (:REWRITE DEFAULT-LESS-THAN-1))
     (34 34 (:REWRITE SIMPLIFY-SUMS-<))
     (34 34
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (34 34
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (34 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
     (30 30 (:REWRITE FOLD-CONSTS-IN-+))
     (27 27 (:REWRITE DEFAULT-MINUS))
     (25 25 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21 (:REWRITE |(< y (+ (- c) x))|))
     (21 21 (:REWRITE |(< x (+ c/d y))|))
     (21 21 (:REWRITE |(< (+ c/d x) y)|))
     (18 18 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (18 18 (:REWRITE |(+ x (- x))|))
     (18 18 (:REWRITE |(+ 0 x)|))
     (18 18 (:DEFINITION FIX))
     (18 9 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (18 6 (:REWRITE CROCK-335-1))
     (16 16 (:REWRITE REDUCE-INTEGERP-+))
     (16 16 (:REWRITE INTEGERP-MINUS-X))
     (16 16 (:META META-INTEGERP-CORRECT))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:REWRITE DEFAULT-CDR))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (4 4 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE |(< 0 (/ x))|))
     (4 4 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE |(equal (if a b c) x)|))
     (1 1
        (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|)))
(|(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
 (2926453 2145412 (:REWRITE DEFAULT-PLUS-2))
 (2471015 2145412 (:REWRITE DEFAULT-PLUS-1))
 (1420466 1420466
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (851026 851026
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (278964 201035 (:REWRITE DEFAULT-LOGAND-2))
 (278309
   278309
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (278309
  278309
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (278309
      278309
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (278309
     278309
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (278309 278309
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (278309 278309
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (267370 4226
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (201035 201035 (:REWRITE LOGAND-CONSTANT-MASK))
 (201035 201035 (:REWRITE DEFAULT-LOGAND-1))
 (191645 191645
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (157994 4980 (:REWRITE SIMPLIFY-SUMS-<))
 (118305 67893 (:REWRITE DEFAULT-TIMES-2))
 (67914 67893 (:REWRITE DEFAULT-TIMES-1))
 (66903 66903 (:REWRITE FOLD-CONSTS-IN-+))
 (66324 66324
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (42298 42186 (:REWRITE DEFAULT-LOGIOR-2))
 (42186 42186 (:REWRITE DEFAULT-LOGIOR-1))
 (32520 10563 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (32520 10563 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (28639 28639
        (:REWRITE |(g field (w32 addr val st))|))
 (12708 3868 (:REWRITE |(< (+ (- c) x) y)|))
 (11588 9741 (:REWRITE DEFAULT-LESS-THAN-1))
 (10871 9741 (:REWRITE DEFAULT-LESS-THAN-2))
 (10397 5544 (:REWRITE CONSTANT-<-INTEGERP))
 (10216 5363 (:REWRITE INTEGERP-<-CONSTANT))
 (9741 9741 (:REWRITE THE-FLOOR-BELOW))
 (9741 9741 (:REWRITE THE-FLOOR-ABOVE))
 (9344 9344
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (9344 9344
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (9242 9192
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (9098 7608 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8763 531 (:REWRITE |(n32-to-i32 x) --- 2|))
 (8595 531 (:REWRITE |(n32-to-i32 x) --- 1|))
 (7426 7426 (:REWRITE |(< (+ c/d x) y)|))
 (7340 5166
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6386 5566 (:REWRITE |(< c (- x))|))
 (5732 5566 (:REWRITE |(< (- x) (- y))|))
 (5566 5566
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5566 5566
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5566 5566
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5566 5566
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5566 5566
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5566 5566
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5566 5566
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5566 5566
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5566 5566 (:REWRITE |(< (/ x) (/ y))|))
 (3417 3417 (:REWRITE |(< x (+ c/d y))|))
 (1756 181
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1736 281
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1736 281
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1684 281 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1168 1168 (:REWRITE |(* (- x) y)|))
 (736 397 (:REWRITE DEFAULT-MINUS))
 (685 685 (:REWRITE |(< y (+ (- c) x))|))
 (434 434 (:REWRITE |(< (* x y) 0)|))
 (428 378
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (378 378
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (378 378
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (378 378
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (281 281
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (281 281
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (281 281
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (281 281 (:REWRITE |(equal c (/ x))|))
 (281 281 (:REWRITE |(equal c (- x))|))
 (281 281 (:REWRITE |(equal (/ x) c)|))
 (281 281 (:REWRITE |(equal (/ x) (/ y))|))
 (281 281 (:REWRITE |(equal (- x) c)|))
 (281 281 (:REWRITE |(equal (- x) (- y))|))
 (264 98
      (:REWRITE |(subrangep (range base offset length) (list x)|))
 (202 181
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (177 177
      (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (154 1
      (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (97 97 (:REWRITE |(< 0 (* x y))|))
 (96 88 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (95 95 (:REWRITE |(< 0 (/ x))|))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (44 44 (:REWRITE |(< (/ x) 0)|))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (36 36 (:REWRITE REDUCE-INTEGERP-+))
 (36 36 (:REWRITE INTEGERP-MINUS-X))
 (36 36 (:META META-INTEGERP-CORRECT))
 (26 13 (:REWRITE O-INFP->NEQ-0))
 (24 24 (:REWRITE |(equal (+ (- c) x) y)|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(|(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
 (1811981 1340571 (:REWRITE DEFAULT-PLUS-2))
 (1540398 1340571 (:REWRITE DEFAULT-PLUS-1))
 (891505 891505
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (534924 534924
         (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (372553
  199944
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (176156 126319 (:REWRITE DEFAULT-LOGAND-2))
 (175106 2654
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (174559
   174559
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (174559
  174559
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (174559
      174559
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (174559
     174559
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (174559 174559
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (174559 174559
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (126319 126319 (:REWRITE LOGAND-CONSTANT-MASK))
 (126319 126319 (:REWRITE DEFAULT-LOGAND-1))
 (119361 119361
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (92406 3002 (:REWRITE SIMPLIFY-SUMS-<))
 (66813 43101 (:REWRITE DEFAULT-TIMES-2))
 (43119 43101 (:REWRITE DEFAULT-TIMES-1))
 (42176 42176
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (41919 41919 (:REWRITE FOLD-CONSTS-IN-+))
 (26648 26536 (:REWRITE DEFAULT-LOGIOR-2))
 (26536 26536 (:REWRITE DEFAULT-LOGIOR-1))
 (24170 5978
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (20601 6607 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (20601 6607 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (17959 17959
        (:REWRITE |(g field (w32 addr val st))|))
 (7020 5978 (:REWRITE DEFAULT-LESS-THAN-1))
 (6942 6942
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6942 6942
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (6663 5978 (:REWRITE DEFAULT-LESS-THAN-2))
 (6541 3370 (:REWRITE CONSTANT-<-INTEGERP))
 (6424 3253 (:REWRITE INTEGERP-<-CONSTANT))
 (5978 5978 (:REWRITE THE-FLOOR-BELOW))
 (5978 5978 (:REWRITE THE-FLOOR-ABOVE))
 (5935 447 (:REWRITE |(n32-to-i32 x) --- 2|))
 (5823 447 (:REWRITE |(n32-to-i32 x) --- 1|))
 (5669 5627
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5370 4464 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4475 4475 (:REWRITE |(< (+ c/d x) y)|))
 (4356 3120
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4191 3392 (:REWRITE |(< c (- x))|))
 (3510 3392 (:REWRITE |(< (- x) (- y))|))
 (3392 3392
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3392 3392
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3392 3392
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3392 3392
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3392 3392
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3392 3392
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3392 3392
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3392 3392
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3392 3392 (:REWRITE |(< (/ x) (/ y))|))
 (2916 234 (:REWRITE |(* y (* x z))|))
 (2240 2240 (:REWRITE |(< (+ (- c) x) y)|))
 (1970 1970 (:REWRITE |(< x (+ c/d y))|))
 (1650 117
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1210 205
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1210 205
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1178 205 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (744 744 (:REWRITE |(* (- x) y)|))
 (521 261 (:REWRITE DEFAULT-MINUS))
 (435 435 (:TYPE-PRESCRIPTION ABS))
 (286 286 (:REWRITE |(< (* x y) 0)|))
 (285 285 (:REWRITE |(< y (+ (- c) x))|))
 (270 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (270 234 (:REWRITE |(* a (/ a) b)|))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (234 234
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (205 205
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (205 205
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (205 205
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (205 205 (:REWRITE |(equal c (/ x))|))
 (205 205 (:REWRITE |(equal c (- x))|))
 (205 205 (:REWRITE |(equal (/ x) c)|))
 (205 205 (:REWRITE |(equal (/ x) (/ y))|))
 (205 205 (:REWRITE |(equal (- x) c)|))
 (205 205 (:REWRITE |(equal (- x) (- y))|))
 (150 1
      (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (149 149
      (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (135 117
      (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (72 64 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (69 69 (:REWRITE |(< 0 (/ x))|))
 (69 69 (:REWRITE |(< 0 (* x y))|))
 (68 68
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (68 68
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< (/ x) 0)|))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:REWRITE INTEGERP-MINUS-X))
 (28 28 (:META META-INTEGERP-CORRECT))
 (18 10 (:REWRITE O-INFP->NEQ-0))
 (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(CREATE_NESTED_PT-ASSERTION)
(ASH-THM-100
     (590 10 (:REWRITE DEFAULT-PLUS-1))
     (588 10 (:REWRITE DEFAULT-PLUS-2))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (344 344
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (208 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (192 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (144 16
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (106 2 (:REWRITE CANCEL-FLOOR-+))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (80 16 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (80 16
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (69 2 (:REWRITE FLOOR-ZERO . 3))
     (53 7 (:REWRITE INTEGERP-MINUS-X))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (47 47 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (36 2 (:REWRITE FLOOR-ZERO . 5))
     (34 4 (:REWRITE |(* (- x) y)|))
     (32 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (31 2 (:REWRITE FLOOR-ZERO . 4))
     (24 24 (:REWRITE DEFAULT-TIMES-2))
     (24 24 (:REWRITE DEFAULT-TIMES-1))
     (23 2 (:REWRITE FLOOR-=-X/Y . 3))
     (23 2 (:REWRITE FLOOR-=-X/Y . 2))
     (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (18 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 6 (:REWRITE DEFAULT-LESS-THAN-1))
     (18 4 (:REWRITE |(- (* c x))|))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 2 (:REWRITE FLOOR-ZERO . 2))
     (10 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (10 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (10 2
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (10 2
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (9 6
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (8 8 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (6 6 (:REWRITE INTEGERP-<-CONSTANT))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (6 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:META META-INTEGERP-CORRECT))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 1 (:REWRITE |(n32p x)|))
     (2 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE DEFAULT-FLOOR-2))
     (2 2 (:REWRITE DEFAULT-FLOOR-1))
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (1 1
        (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|)))
(BREAK-LOGAND-APART
     (15998 28 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
     (15444 30 (:DEFINITION NATP))
     (12860 222 (:REWRITE THE-FLOOR-ABOVE))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (7262 7262
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (5374 12 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (5374 12 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (4619 139 (:REWRITE DEFAULT-PLUS-1))
     (4545 139 (:REWRITE DEFAULT-PLUS-2))
     (4373 47 (:REWRITE NORMALIZE-ADDENDS))
     (2620 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (2612 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (2594 290
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (1636 28 (:REWRITE FLOOR-ZERO . 3))
     (1484 28 (:REWRITE CANCEL-FLOOR-+))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (1460 292 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (1460 292
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1428 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (1428 14 (:DEFINITION FIX))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1012 1012
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (952 28 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (920 226 (:REWRITE |(* y x)|))
     (906 638 (:REWRITE DEFAULT-TIMES-2))
     (850 206 (:REWRITE INTEGERP-MINUS-X))
     (844 28 (:REWRITE FLOOR-ZERO . 5))
     (844 28 (:REWRITE FLOOR-ZERO . 4))
     (802 208
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (748 28 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (700 140 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (684 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (684 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (654 638 (:REWRITE DEFAULT-TIMES-1))
     (616 28 (:REWRITE FLOOR-=-X/Y . 3))
     (616 28 (:REWRITE FLOOR-=-X/Y . 2))
     (538 34 (:REWRITE |(floor x 2)| . 2))
     (476 56 (:REWRITE |(* (- x) y)|))
     (422 34 (:REWRITE DEFAULT-FLOOR-RATIO))
     (364 14 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (360 208 (:REWRITE DEFAULT-LESS-THAN-1))
     (354 354
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (308 14 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (290 194
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (290 194
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (280 56 (:REWRITE DEFAULT-MINUS))
     (274 274
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (252 56 (:REWRITE |(- (* c x))|))
     (237 237
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
     (222 222 (:REWRITE THE-FLOOR-BELOW))
     (218 194
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (208 208 (:REWRITE DEFAULT-LESS-THAN-2))
     (194 194 (:REWRITE SIMPLIFY-SUMS-<))
     (194 194
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (194 194
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (194 194 (:REWRITE INTEGERP-<-CONSTANT))
     (194 194 (:REWRITE CONSTANT-<-INTEGERP))
     (194 194
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (194 194
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (194 194
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (194 194
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (194 194 (:REWRITE |(< c (- x))|))
     (194 194
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (194 194
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (194 194 (:REWRITE |(< (/ x) (/ y))|))
     (194 194 (:REWRITE |(< (- x) c)|))
     (194 194 (:REWRITE |(< (- x) (- y))|))
     (178 178 (:REWRITE REDUCE-INTEGERP-+))
     (178 178 (:META META-INTEGERP-CORRECT))
     (160 160 (:REWRITE |(< (* x y) 0)|))
     (146 146
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (146 146
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (146 146 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (146 146 (:REWRITE |(< (/ x) 0)|))
     (140 140 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
     (140 140 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (140 140
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (140 140
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (140 140 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (140 28 (:REWRITE FLOOR-ZERO . 2))
     (140 28 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (140 28 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (140 28
          (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (140 28
          (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (124 28 (:REWRITE FLOOR-CANCEL-*-CONST))
     (110 10 (:REWRITE DEFAULT-MOD-RATIO))
     (88 4 (:LINEAR MOD-BOUNDS-3))
     (62 62 (:TYPE-PRESCRIPTION ABS))
     (50 34 (:REWRITE DEFAULT-FLOOR-1))
     (40 8 (:LINEAR MOD-BOUNDS-2))
     (38 38
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (34 34 (:REWRITE DEFAULT-FLOOR-2))
     (33 33
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (28 28 (:REWRITE |(floor x (- y))| . 2))
     (28 28 (:REWRITE |(floor x (- y))| . 1))
     (28 28
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (28 28
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (28 28 (:REWRITE |(floor (- x) y)| . 2))
     (28 28 (:REWRITE |(floor (- x) y)| . 1))
     (28 28
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (28 14 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (24 24 (:REWRITE |(< 0 (/ x))|))
     (24 24 (:REWRITE |(< 0 (* x y))|))
     (20 20 (:TYPE-PRESCRIPTION NATP))
     (20 4
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (20 4
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (17 17 (:REWRITE LOGAND-CONSTANT-MASK))
     (14 14 (:REWRITE |(+ x (- x))|))
     (10 10 (:REWRITE DEFAULT-MOD-2))
     (10 10 (:REWRITE DEFAULT-MOD-1))
     (10 10 (:REWRITE |(mod x 2)| . 2))
     (10 2 (:REWRITE O-INFP->NEQ-0))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (4 4
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 4))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 3))
     (4 4
        (:REWRITE |(integerp (* 1/2 (logand x y)))| . 2))
     (4 4 (:REWRITE |(equal c (/ x))|))
     (4 4 (:REWRITE |(equal c (- x))|))
     (4 4 (:REWRITE |(equal (/ x) c)|))
     (4 4 (:REWRITE |(equal (/ x) (/ y))|))
     (4 4 (:REWRITE |(equal (- x) c)|))
     (4 4 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(LOGIOR-THM-100
     (11551 5 (:REWRITE FLOOR-=-X/Y . 4))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (8228 8228
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (7500 280 (:REWRITE THE-FLOOR-ABOVE))
     (3369 6 (:LINEAR BINARY-LOGAND->=-0))
     (3254 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (3243 383
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (3222 386 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (3222 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
     (3211 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (3120 6 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (3114 6 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (3114 6 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (3097 59 (:REWRITE DEFAULT-PLUS-1))
     (2908 6 (:DEFINITION NATP))
     (2769 59 (:REWRITE DEFAULT-PLUS-2))
     (2486 14 (:REWRITE NORMALIZE-ADDENDS))
     (2056 20 (:REWRITE FLOOR-ZERO . 3))
     (1906 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (1906 394
           (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (1895 383
           (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (1886 386 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (1886 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (1886 386
           (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
     (1875 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (1875 375
           (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (1732 20 (:REWRITE FLOOR-ZERO . 5))
     (1648 20 (:REWRITE CANCEL-FLOOR-+))
     (1586 370 (:REWRITE DEFAULT-TIMES-2))
     (1338 1338
           (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
     (1338 1338
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
     (1338 1338
           (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
     (1136 20 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (1101 43 (:REWRITE |(< (logior x y) 0)|))
     (1092 12 (:REWRITE |(< 0 (logior x y))|))
     (1012 20 (:REWRITE FLOOR-ZERO . 4))
     (992 20 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (835 370 (:REWRITE DEFAULT-TIMES-1))
     (816 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (816 8 (:DEFINITION FIX))
     (773 8
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (773 8
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (758 118 (:REWRITE INTEGERP-MINUS-X))
     (668 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (666 72 (:LINEAR LOGIOR-BOUNDS-POS . 2))
     (666 72 (:LINEAR LOGIOR-BOUNDS-POS . 1))
     (647 72 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
     (608 20 (:REWRITE FLOOR-=-X/Y . 3))
     (608 20 (:REWRITE FLOOR-=-X/Y . 2))
     (590 5 (:REWRITE CROCK-200))
     (580 40 (:REWRITE |(* (- x) y)|))
     (569 225
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (503 8 (:REWRITE |(n32p x)|))
     (497 225 (:REWRITE DEFAULT-LESS-THAN-1))
     (457 217
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (457 217
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (456 456
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (320 40 (:REWRITE DEFAULT-MINUS))
     (300 40 (:REWRITE |(- (* c x))|))
     (285 9
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (281 281
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (280 280 (:REWRITE THE-FLOOR-BELOW))
     (237 217
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (233 6 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (225 225 (:REWRITE DEFAULT-LESS-THAN-2))
     (217 217 (:REWRITE SIMPLIFY-SUMS-<))
     (217 217
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (217 217
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (217 217 (:REWRITE INTEGERP-<-CONSTANT))
     (217 217 (:REWRITE CONSTANT-<-INTEGERP))
     (217 217
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (217 217
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (217 217
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (217 217
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (217 217 (:REWRITE |(< c (- x))|))
     (217 217
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (217 217
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (217 217
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (217 217
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (217 217 (:REWRITE |(< (/ x) (/ y))|))
     (217 217 (:REWRITE |(< (- x) c)|))
     (217 217 (:REWRITE |(< (- x) (- y))|))
     (187 187
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (175 175 (:REWRITE |(< (* x y) 0)|))
     (174 6 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (167 167
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (167 167
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (167 167 (:REWRITE |(< (/ x) 0)|))
     (160 20 (:REWRITE FLOOR-ZERO . 2))
     (160 20 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (160 20 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (160 20 (:REWRITE FLOOR-CANCEL-*-CONST))
     (154 154 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (106 1 (:REWRITE O-INFP->NEQ-0))
     (105 3 (:REWRITE |(n32p (logior x y))|))
     (98 98 (:REWRITE REDUCE-INTEGERP-+))
     (98 98 (:META META-INTEGERP-CORRECT))
     (96 72 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
     (96 12 (:REWRITE RATIONALP-X))
     (90 20
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (90 20
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (90 20
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (90 20
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (66 22 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (50 50 (:TYPE-PRESCRIPTION ABS))
     (50 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (50 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (36 4 (:REWRITE ACL2-NUMBERP-X))
     (34 2 (:REWRITE |(* (if a b c) x)|))
     (30 4
         (:REWRITE |(equal (floor (+ x y) z) x)|))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (28 28
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (28 28 (:REWRITE |(< 0 (/ x))|))
     (28 28 (:REWRITE |(< 0 (* x y))|))
     (28 28
         (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (26 26 (:REWRITE DEFAULT-FLOOR-2))
     (22 22 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (22 22
         (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (22 22
         (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (20 20 (:REWRITE |(floor x (- y))| . 2))
     (20 20 (:REWRITE |(floor x (- y))| . 1))
     (20 20
         (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (20 20
         (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (20 20 (:REWRITE |(floor (- x) y)| . 2))
     (20 20 (:REWRITE |(floor (- x) y)| . 1))
     (19 19 (:TYPE-PRESCRIPTION N32P))
     (16 8 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (13 13 (:REWRITE DEFAULT-LOGAND-1))
     (12 12 (:REWRITE RATIONALP-MINUS-X))
     (11 11 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (11 11 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (8 8 (:REWRITE REDUCE-RATIONALP-+))
     (8 8
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (8 8 (:REWRITE LOGAND-CONSTANT-MASK))
     (8 8
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (8 8 (:REWRITE DEFAULT-LOGIOR-1))
     (8 8 (:REWRITE |(equal c (/ x))|))
     (8 8 (:REWRITE |(equal c (- x))|))
     (8 8 (:REWRITE |(equal (/ x) c)|))
     (8 8 (:REWRITE |(equal (/ x) (/ y))|))
     (8 8 (:REWRITE |(equal (- x) c)|))
     (8 8 (:REWRITE |(equal (- x) (- y))|))
     (8 8 (:REWRITE |(+ x (- x))|))
     (8 8 (:META META-RATIONALP-CORRECT))
     (6 6 (:TYPE-PRESCRIPTION NATP))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:LINEAR BINARY-LOGAND-<=))
     (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE |(equal (* x y) 0)|)))
(ASH-THM-101
     (2537 25 (:REWRITE THE-FLOOR-BELOW))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (606 606
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (482 482
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (385 5 (:REWRITE CANCEL-FLOOR-+))
     (353 5 (:REWRITE FLOOR-ZERO . 3))
     (325 25 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (312 1 (:REWRITE FLOOR-=-X/Y . 4))
     (292 5 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (225 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (225 25 (:REWRITE DEFAULT-LESS-THAN-2))
     (214 5 (:REWRITE FLOOR-ZERO . 5))
     (203 5 (:REWRITE FLOOR-ZERO . 4))
     (198 18 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (191 26 (:REWRITE INTEGERP-MINUS-X))
     (175 83 (:REWRITE DEFAULT-TIMES-2))
     (163 3
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (161 83 (:REWRITE DEFAULT-TIMES-1))
     (161 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (161 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (160 5 (:REWRITE FLOOR-=-X/Y . 3))
     (160 5 (:REWRITE FLOOR-=-X/Y . 2))
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
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (125 25
          (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (125 10 (:REWRITE |(* (- x) y)|))
     (123 15 (:LINEAR BINARY-LOGAND-<=))
     (107 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (101 2
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (101 2
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (94 15 (:LINEAR BINARY-LOGAND->=-0))
     (93 3 (:DEFINITION NATP))
     (76 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
     (70 10 (:REWRITE DEFAULT-MINUS))
     (65 10 (:REWRITE |(- (* c x))|))
     (64 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
     (59 25 (:REWRITE DEFAULT-LESS-THAN-1))
     (45 5 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (43 43
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (35 5 (:REWRITE FLOOR-ZERO . 2))
     (35 5 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (35 5 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (34 34 (:REWRITE LOGAND-CONSTANT-MASK))
     (34 34 (:REWRITE DEFAULT-LOGAND-1))
     (27 24
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (27 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (25 25 (:REWRITE THE-FLOOR-ABOVE))
     (24 24 (:REWRITE SIMPLIFY-SUMS-<))
     (24 24
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (24 24 (:REWRITE INTEGERP-<-CONSTANT))
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
     (23 5
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (23 5 (:REWRITE FLOOR-CANCEL-*-CONST))
     (23 5
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (21 21 (:REWRITE REDUCE-INTEGERP-+))
     (21 21 (:META META-INTEGERP-CORRECT))
     (18 18 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (18 18 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (18 6 (:REWRITE DEFAULT-FLOOR-1))
     (17 5
         (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (17 5
         (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (16 16 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (16 4 (:REWRITE DEFAULT-PLUS-2))
     (16 4 (:REWRITE DEFAULT-PLUS-1))
     (15 15 (:TYPE-PRESCRIPTION NATP))
     (15 3
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (11 1 (:REWRITE |(* (if a b c) x)|))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 3
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (7 7 (:TYPE-PRESCRIPTION ABS))
     (7 1
        (:REWRITE |(equal (floor (+ x y) z) x)|))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:REWRITE |(floor x (- y))| . 2))
     (5 5 (:REWRITE |(floor x (- y))| . 1))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (5 5
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (5 5 (:REWRITE |(floor (- x) y)| . 2))
     (5 5 (:REWRITE |(floor (- x) y)| . 1))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 1 (:REWRITE |(* a (/ a) b)|))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|)))
(ASH-THM-102
     (303 5 (:REWRITE DEFAULT-PLUS-1))
     (302 5 (:REWRITE DEFAULT-PLUS-2))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (251 251
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (234 2 (:REWRITE FLOOR-ZERO . 3))
     (203 203
          (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
     (154 2 (:REWRITE CANCEL-FLOOR-+))
     (143 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (140 2 (:REWRITE FLOOR-ZERO . 5))
     (134 2 (:REWRITE FLOOR-ZERO . 4))
     (133 10 (:REWRITE DEFAULT-LESS-THAN-1))
     (128 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (99 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (98 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (78 12 (:REWRITE INTEGERP-MINUS-X))
     (78 4 (:REWRITE DEFAULT-FLOOR-RATIO))
     (68 34 (:REWRITE DEFAULT-TIMES-2))
     (68 34 (:REWRITE DEFAULT-TIMES-1))
     (64 2 (:REWRITE FLOOR-=-X/Y . 3))
     (64 2 (:REWRITE FLOOR-=-X/Y . 2))
     (60 8 (:LINEAR LOGAND-BOUNDS-POS . 1))
     (55 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (55 11 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (55 11
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (50 4 (:REWRITE |(* (- x) y)|))
     (48 8 (:LINEAR BINARY-LOGAND->=-0))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (43 43 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (39 9
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (39 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 4 (:REWRITE DEFAULT-MINUS))
     (26 4 (:REWRITE |(- (* c x))|))
     (22 2 (:REWRITE |(* (if a b c) x)|))
     (18 18 (:REWRITE LOGAND-CONSTANT-MASK))
     (18 18 (:REWRITE DEFAULT-LOGAND-1))
     (18 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (17 17
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (16 8 (:LINEAR BINARY-LOGAND-<=))
     (14 10 (:REWRITE DEFAULT-LESS-THAN-2))
     (14 2 (:REWRITE FLOOR-ZERO . 2))
     (14 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (14 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (14 2
         (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (14 2 (:REWRITE FLOOR-CANCEL-*-CONST))
     (14 2
         (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (12 9
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (12 9
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (12 4 (:REWRITE DEFAULT-FLOOR-1))
     (11 11 (:REWRITE THE-FLOOR-BELOW))
     (10 10 (:REWRITE REDUCE-INTEGERP-+))
     (10 10 (:META META-INTEGERP-CORRECT))
     (10 2
         (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
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
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:TYPE-PRESCRIPTION NATP))
     (8 8 (:LINEAR LOGAND-BOUNDS-POS . 2))
     (8 8 (:LINEAR LOGAND-BOUNDS-NEG . 2))
     (8 8 (:LINEAR LOGAND-BOUNDS-NEG . 1))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (6 2
        (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE DEFAULT-FLOOR-2))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (2 2
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (2 2 (:REWRITE |(floor x (- y))| . 2))
     (2 2 (:REWRITE |(floor x (- y))| . 1))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (2 2
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(floor (- x) y)| . 2))
     (2 2 (:REWRITE |(floor (- x) y)| . 1))
     (2 2
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
($$$PRESUB)
($$$MODIFYSUB)
($$$PRESUB-IMPLIES-INSUB
 (44649 6 (:REWRITE FLOOR-=-X/Y . 4))
 (34472 40 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (26385 32 (:REWRITE |(n32p x)|))
 (14019 340
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (12259 12259
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (12259 12259
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5679 53 (:REWRITE FLOOR-ZERO . 3))
 (5094 530 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (4771 53 (:REWRITE CANCEL-FLOOR-+))
 (4770 530
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4770 530
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4770 530
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4236 6 (:DEFINITION NATP))
 (4182 44 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (4041 449
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (3549 53 (:REWRITE FLOOR-ZERO . 5))
 (3537 344 (:REWRITE DEFAULT-LESS-THAN-1))
 (3442 53 (:REWRITE FLOOR-ZERO . 4))
 (3315 53 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3274 44 (:LINEAR BINARY-LOGAND->=-0))
 (3193 315
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2860 44 (:LINEAR BINARY-LOGAND-<=))
 (2846 894 (:REWRITE DEFAULT-TIMES-2))
 (2842 318 (:REWRITE DEFAULT-PLUS-1))
 (2650 530 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2650 530 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2650 530
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2538 53 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2506 2 (:REWRITE CROCK-200))
 (2468 355 (:REWRITE INTEGERP-MINUS-X))
 (2138 894 (:REWRITE DEFAULT-TIMES-1))
 (2136 44 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (2136 44 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (1947 53 (:REWRITE FLOOR-=-X/Y . 3))
 (1942 15
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1927 53 (:REWRITE FLOOR-=-X/Y . 2))
 (1918 15
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1675 44 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (1606 112 (:REWRITE |(* (- x) y)|))
 (1352 606
       (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (1265 1265
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1075 1075
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1075 1075
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1075 1075
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1071 53 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1002 145 (:REWRITE DEFAULT-LOGAND-2))
 (880 20 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (872 112 (:REWRITE DEFAULT-MINUS))
 (859 131 (:REWRITE ACL2-NUMBERP-X))
 (846 112 (:REWRITE |(- (* c x))|))
 (738 20 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (538 15 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (528 344 (:REWRITE DEFAULT-LESS-THAN-2))
 (479 479
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (424 53 (:REWRITE FLOOR-ZERO . 2))
 (424 53 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (424 53 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (410 82 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (410 82
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (391 340
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (391 340
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (368 53 (:REWRITE FLOOR-CANCEL-*-CONST))
 (365 145 (:REWRITE DEFAULT-LOGAND-1))
 (364 91 (:REWRITE RATIONALP-X))
 (345 345 (:REWRITE THE-FLOOR-BELOW))
 (337 53
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (337 53
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (316 316
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (316 316 (:REWRITE INTEGERP-<-CONSTANT))
 (316 316 (:REWRITE CONSTANT-<-INTEGERP))
 (316 316
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (316 316
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (316 316
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (316 316
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (316 316 (:REWRITE |(< c (- x))|))
 (316 316
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (316 316
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (316 316
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (316 316
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (316 316 (:REWRITE |(< (/ x) (/ y))|))
 (316 316 (:REWRITE |(< (- x) c)|))
 (316 316 (:REWRITE |(< (- x) (- y))|))
 (299 299 (:REWRITE REDUCE-INTEGERP-+))
 (299 299 (:META META-INTEGERP-CORRECT))
 (234 234 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (212 53 (:REWRITE DEFAULT-FLOOR-1))
 (184 2 (:REWRITE CANCEL-MOD-+))
 (174 4 (:REWRITE |(< (if a b c) x)|))
 (169 169
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (155 12
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (153 153 (:REWRITE |(< (* x y) 0)|))
 (145 145 (:REWRITE LOGAND-CONSTANT-MASK))
 (142 142
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (142 142
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (142 142 (:REWRITE |(< (/ x) 0)|))
 (140 53
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (140 53
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (132 2 (:REWRITE MOD-X-Y-=-X . 4))
 (123 2 (:REWRITE MOD-X-Y-=-X . 3))
 (118 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (115 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (106 2 (:REWRITE MOD-ZERO . 4))
 (105 105 (:TYPE-PRESCRIPTION ABS))
 (105 1 (:REWRITE O-INFP->NEQ-0))
 (91 91 (:REWRITE REDUCE-RATIONALP-+))
 (91 91 (:REWRITE REDUCE-RATIONALP-*))
 (91 91 (:REWRITE RATIONALP-MINUS-X))
 (91 91 (:META META-RATIONALP-CORRECT))
 (84 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (82 82 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (82 82
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (82 82 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (81 81 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (81 81
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (77 77
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (75 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (74 2 (:REWRITE MOD-ZERO . 3))
 (61 1 (:REWRITE |(floor (+ x r) i)|))
 (57 57 (:REWRITE |(< 0 (* x y))|))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (56 56
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (56 56 (:REWRITE |(< 0 (/ x))|))
 (53 53 (:REWRITE DEFAULT-FLOOR-2))
 (53 53 (:REWRITE |(floor x (- y))| . 2))
 (53 53 (:REWRITE |(floor x (- y))| . 1))
 (53 53
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (53 53
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (53 53 (:REWRITE |(floor (- x) y)| . 2))
 (53 53 (:REWRITE |(floor (- x) y)| . 1))
 (48 12
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (41 5
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (40 2 (:REWRITE DEFAULT-MOD-RATIO))
 (39 39
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (38 38 (:REWRITE |(< (+ c/d x) y)|))
 (24 24
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (22 2 (:REWRITE MOD-X-Y-=-X . 2))
 (22 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (22 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (18 18 (:TYPE-PRESCRIPTION NATP))
 (18 3 (:REWRITE DISJOINT-4-ITEMS))
 (16 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (16 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (16 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 2 (:REWRITE MOD-CANCEL-*-CONST))
 (16 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (15 15
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (15 15 (:REWRITE |(equal c (/ x))|))
 (15 15 (:REWRITE |(equal c (- x))|))
 (15 15 (:REWRITE |(equal (/ x) c)|))
 (15 15 (:REWRITE |(equal (/ x) (/ y))|))
 (15 15 (:REWRITE |(equal (- x) c)|))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (12
   12
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (12
  12
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (12 2 (:REWRITE DISJOINT-7-ITEMS))
 (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 2 (:REWRITE DEFAULT-MOD-1))
 (6 2
    (:REWRITE |(n32p (r32 addr (g :mem st)))|))
 (5 5
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (5
  5
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (4 4 (:TYPE-PRESCRIPTION N32P))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (4 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (4 1 (:REWRITE |(* a (/ a) b)|))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (3 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (3 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE DEFAULT-MOD-2))
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
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1 (:REWRITE |(equal (* x y) 0)|)))
($$$NO-MAIN-CUTPOINT-IN-SUB
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 5 (:REWRITE DEFAULT-PLUS-2))
     (9 5 (:REWRITE SIMPLIFY-SUMS-<))
     (8 2 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE DEFAULT-PLUS-1))
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
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
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
     (1 1 (:REWRITE |(equal (- x) (- y))|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
($$$IN-SUB-IMPLIES-IN-MAIN
     (18 2 (:REWRITE ACL2-NUMBERP-X))
     (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (10 5
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 5 (:REWRITE SIMPLIFY-SUMS-<))
     (8 4 (:REWRITE DEFAULT-PLUS-2))
     (8 2 (:REWRITE RATIONALP-X))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
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
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE |(< y (+ (- c) x))|))
     (2 2 (:REWRITE |(< x (+ c/d y))|))
     (2 2 (:META META-RATIONALP-CORRECT))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< 0 (/ x))|))
     (1 1 (:REWRITE |(< 0 (* x y))|)))
($$$CORRECTNESS-OF-SUB)
($$$NEXT-CUTPOINT-MAIN)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-test|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-base|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-step|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)
(|$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-fn| (4 4 (:REWRITE DEFAULT-<-2))
                                           (4 4 (:REWRITE DEFAULT-<-1))
                                           (1 1 (:REWRITE ZP-OPEN))
                                           (1 1 (:REWRITE DEFAULT-+-2))
                                           (1 1 (:REWRITE DEFAULT-+-1)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1|
     (1 1
        (:TYPE-PRESCRIPTION |$$$NEXT-CUTPOINT-MAIN-arity-1-defpun-stn|)))
(|$$$NEXT-CUTPOINT-MAIN-arity-1-DEF|)
($$$NEXT-CUTPOINT-MAIN)
($$$NEXT-CUTPOINT-MAIN-DEF)
($$$NEXT-CUTPOINT-MAIN$DEF)
($$$DEFP-SYMSIM-THEOREM)
($$$PRE-IMPLIES-ASSERTION
 (37117 11 (:REWRITE FLOOR-=-X/Y . 4))
 (15753 15753
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (15753 15753
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (7709 593 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (7352 470 (:REWRITE DEFAULT-PLUS-2))
 (6822 87 (:REWRITE FLOOR-ZERO . 3))
 (5836 87 (:REWRITE CANCEL-FLOOR-+))
 (5337 593
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (5337 593
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (5085 565
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4455 470 (:REWRITE DEFAULT-PLUS-1))
 (4424 388 (:REWRITE THE-FLOOR-BELOW))
 (3928 3928
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (3425 89 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3208 435 (:REWRITE INTEGERP-MINUS-X))
 (3057 89 (:REWRITE FLOOR-ZERO . 5))
 (2965 593 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2965 593 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2965 593
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2965 593
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2965 593
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2965 593
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2965 593
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2825 565
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2810 562 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2810 562 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2810 562
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2513 1493 (:REWRITE DEFAULT-TIMES-2))
 (2283 89 (:REWRITE FLOOR-=-X/Y . 2))
 (2251 89 (:REWRITE FLOOR-=-X/Y . 3))
 (2215 26
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2215 26
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2197 2197
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2197 1493 (:REWRITE DEFAULT-TIMES-1))
 (2065 202 (:REWRITE |(* (- x) y)|))
 (1480 361
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1399 384 (:REWRITE DEFAULT-LESS-THAN-1))
 (1399 361
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1290 89 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1282 286 (:REWRITE DEFAULT-LOGAND-2))
 (1142 202 (:REWRITE DEFAULT-MINUS))
 (1125 202 (:REWRITE |(- (* c x))|))
 (952 376
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (820 820
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (790 14 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (718 23 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (639 89 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (621 10 (:REWRITE CANCEL-MOD-+))
 (605 23 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (581 384 (:REWRITE DEFAULT-LESS-THAN-2))
 (562 562
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (562 562
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (562 562 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (542 89 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (542 89 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (532 87 (:REWRITE FLOOR-ZERO . 2))
 (497 497 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (497 497
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (480 87 (:REWRITE FLOOR-CANCEL-*-CONST))
 (452 376
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (452 376
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (392 14 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (382 382
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (382 382
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (364 364 (:REWRITE INTEGERP-<-CONSTANT))
 (364 364 (:REWRITE CONSTANT-<-INTEGERP))
 (364 364
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (364 364
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (364 364
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (364 364
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (364 364 (:REWRITE |(< c (- x))|))
 (364 364
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (364 364
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (364 364
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (364 364
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (364 364 (:REWRITE |(< (/ x) (/ y))|))
 (364 364 (:REWRITE |(< (- x) c)|))
 (364 364 (:REWRITE |(< (- x) (- y))|))
 (349 87
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (349 87
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (343 14 (:REWRITE MOD-X-Y-=-X . 4))
 (334 334 (:REWRITE REDUCE-INTEGERP-+))
 (334 334 (:META META-INTEGERP-CORRECT))
 (330 330
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (328 55 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (328 55 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (322 76
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (286 286 (:REWRITE DEFAULT-LOGAND-1))
 (278 278 (:REWRITE LOGAND-CONSTANT-MASK))
 (275 14 (:REWRITE MOD-ZERO . 3))
 (270 87
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (270 87
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (220 220
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (217 14 (:REWRITE MOD-ZERO . 4))
 (198
  198
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (186 89 (:REWRITE DEFAULT-FLOOR-1))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (175 14 (:REWRITE DEFAULT-MOD-RATIO))
 (167 167 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (161 76
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (156 156 (:TYPE-PRESCRIPTION ABS))
 (89 89 (:REWRITE DEFAULT-FLOOR-2))
 (87 87 (:REWRITE |(floor x (- y))| . 2))
 (87 87 (:REWRITE |(floor x (- y))| . 1))
 (87 87
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (87 87
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (87 87 (:REWRITE |(floor (- x) y)| . 2))
 (87 87 (:REWRITE |(floor (- x) y)| . 1))
 (86 2
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (84 14 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (77 14 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (77 14 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (72 72 (:REWRITE |(< 0 (/ x))|))
 (72 72 (:REWRITE |(< 0 (* x y))|))
 (70 70
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (70 70
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (64 10 (:REWRITE MOD-X-Y-=-X . 2))
 (64 10 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (64 10
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (60 9
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (57 10
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (57 10 (:REWRITE MOD-CANCEL-*-CONST))
 (57 10
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (40 16 (:REWRITE DEFAULT-LOGIOR-2))
 (38 38 (:REWRITE |(< (+ c/d x) y)|))
 (37
   37
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (37
  37
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (37 37
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (32 2 (:LINEAR MOD-BOUNDS-3))
 (30
  30
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (30
  30
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (30 26
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (26 26
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (26 26 (:REWRITE |(equal c (/ x))|))
 (26 26 (:REWRITE |(equal c (- x))|))
 (26 26 (:REWRITE |(equal (/ x) c)|))
 (26 26 (:REWRITE |(equal (/ x) (/ y))|))
 (26 26 (:REWRITE |(equal (- x) c)|))
 (26 26 (:REWRITE |(equal (- x) (- y))|))
 (26 26 (:REWRITE |(< (+ (- c) x) y)|))
 (23 23 (:REWRITE FOLD-CONSTS-IN-+))
 (22 4 (:LINEAR MOD-BOUNDS-2))
 (21 14 (:REWRITE DEFAULT-MOD-1))
 (16 16 (:REWRITE DEFAULT-LOGIOR-1))
 (14 14 (:REWRITE DEFAULT-MOD-2))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (11 11 (:REWRITE |(equal (+ (- c) x) y)|))
 (10 10
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
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
 (10 10
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (8 4 (:REWRITE |(floor (+ x r) i)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (6 2
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (4 4
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (4 4
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
($$$ASSERTION-MAIN-IMPLIES-POST
 (43647 6 (:REWRITE FLOOR-=-X/Y . 4))
 (16417 16417
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16417 16417
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (11529 793 (:REWRITE THE-FLOOR-BELOW))
 (6591 73 (:REWRITE FLOOR-ZERO . 3))
 (6014 550 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5999 73 (:REWRITE CANCEL-FLOOR-+))
 (5964 749
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5676 5676
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (4950 550
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (4950 550
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4950 550
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4620 2147 (:REWRITE DEFAULT-PLUS-1))
 (4457 73 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (4138 73 (:REWRITE FLOOR-ZERO . 5))
 (4072 73 (:REWRITE FLOOR-ZERO . 4))
 (3468 96 (:REWRITE |(n32-to-i32 x) --- 2|))
 (3400 96 (:REWRITE |(n32-to-i32 x) --- 1|))
 (3191 566 (:REWRITE INTEGERP-MINUS-X))
 (3080 616 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3080 616 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3080 616
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (3019 1194 (:REWRITE DEFAULT-TIMES-2))
 (2750 550 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2750 550 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2750 550
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2681 1194 (:REWRITE DEFAULT-TIMES-1))
 (2603 73 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2556 284
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (2339 73 (:REWRITE FLOOR-=-X/Y . 3))
 (2235 73 (:REWRITE FLOOR-=-X/Y . 2))
 (2187 603
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2146 39
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2074 386 (:REWRITE ACL2-NUMBERP-X))
 (2051 603
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2034 39
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1966 152 (:REWRITE |(* (- x) y)|))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1679 1679
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1418 648
       (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (1279 73 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1219 4 (:DEFINITION NATP))
 (1162 29 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1153 791 (:REWRITE DEFAULT-LESS-THAN-2))
 (1090 152 (:REWRITE |(- (* c x))|))
 (1028 152 (:REWRITE DEFAULT-MINUS))
 (969 29 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (949 354 (:REWRITE DEFAULT-LOGAND-2))
 (844 211 (:REWRITE RATIONALP-X))
 (808 749
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (808 749
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (765 603 (:REWRITE SIMPLIFY-SUMS-<))
 (643 643
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (642 642
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (616 616
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (616 616 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (603 603
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (603 603 (:REWRITE INTEGERP-<-CONSTANT))
 (603 603 (:REWRITE CONSTANT-<-INTEGERP))
 (603 603
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (603 603
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (603 603
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (603 603
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (603 603 (:REWRITE |(< c (- x))|))
 (603 603
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (603 603
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (603 603
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (603 603
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (603 603 (:REWRITE |(< (/ x) (/ y))|))
 (603 603 (:REWRITE |(< (- x) c)|))
 (603 603 (:REWRITE |(< (- x) (- y))|))
 (556 73 (:REWRITE FLOOR-ZERO . 2))
 (556 73 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (556 73 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (522 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (490 490 (:REWRITE REDUCE-INTEGERP-+))
 (490 490 (:META META-INTEGERP-CORRECT))
 (486 486 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (486 486
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (459 73
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 73 (:REWRITE FLOOR-CANCEL-*-CONST))
 (459 73
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (442 442 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (436 4 (:REWRITE CROCK-200))
 (408 24
      (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- not paging|))
 (360 48
      (:REWRITE |(good-32-address-p addr st)|))
 (354 354 (:REWRITE DEFAULT-LOGAND-1))
 (350 350 (:REWRITE LOGAND-CONSTANT-MASK))
 (288 96
      (:REWRITE |(paging-p (w32 addr val st))|))
 (283 95 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (283 95 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (264 73 (:REWRITE DEFAULT-FLOOR-1))
 (252 12
      (:REWRITE |(paging-p (init_pdts-modify s))|))
 (240 144
      (:REWRITE |(paging-p (s field val st))|))
 (211 211 (:REWRITE REDUCE-RATIONALP-+))
 (211 211 (:REWRITE REDUCE-RATIONALP-*))
 (211 211 (:REWRITE RATIONALP-MINUS-X))
 (211 211 (:META META-RATIONALP-CORRECT))
 (199 22
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (192 192 (:REWRITE |(< (+ c/d x) y)|))
 (184 2 (:REWRITE CANCEL-MOD-+))
 (180 12
      (:REWRITE |(paging-p (init_pdpt-modify s))|))
 (172 172 (:REWRITE |(< (* x y) 0)|))
 (170 73
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (170 73
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (162 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (162 162
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (162 162 (:REWRITE |(< (/ x) 0)|))
 (141
   141
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (141
  141
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (141 141
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (141
     141
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (141 141
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (141 141
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (132 2 (:REWRITE MOD-X-Y-=-X . 4))
 (123 2 (:REWRITE MOD-X-Y-=-X . 3))
 (121 121 (:TYPE-PRESCRIPTION ABS))
 (118 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (115 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (109 5 (:REWRITE O-INFP->NEQ-0))
 (108 40
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (106 2 (:REWRITE MOD-ZERO . 4))
 (96 96
     (:TYPE-PRESCRIPTION GOOD-32-ADDRESS-P))
 (96 24
     (:REWRITE |(w32 addr1 val1 (w32 addr2 val2 st)) --- paging|))
 (81 81
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (81 81
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (81 81 (:REWRITE |(< 0 (/ x))|))
 (81 81 (:REWRITE |(< 0 (* x y))|))
 (75 22
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (75 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (74 2 (:REWRITE MOD-ZERO . 3))
 (73 73 (:REWRITE DEFAULT-FLOOR-2))
 (73 73 (:REWRITE |(floor x (- y))| . 2))
 (73 73 (:REWRITE |(floor x (- y))| . 1))
 (73 73
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (73 73
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (73 73 (:REWRITE |(floor (- x) y)| . 2))
 (73 73 (:REWRITE |(floor (- x) y)| . 1))
 (61 1 (:REWRITE |(floor (+ x r) i)|))
 (46 46 (:REWRITE |(< (+ (- c) x) y)|))
 (41 5
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (40 2 (:REWRITE DEFAULT-MOD-RATIO))
 (39 39
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (39 39
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (39 39 (:REWRITE |(equal c (/ x))|))
 (39 39 (:REWRITE |(equal c (- x))|))
 (39 39 (:REWRITE |(equal (/ x) c)|))
 (39 39 (:REWRITE |(equal (/ x) (/ y))|))
 (39 39 (:REWRITE |(equal (- x) c)|))
 (39 39 (:REWRITE |(equal (- x) (- y))|))
 (37 37
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (28 4 (:REWRITE DEFAULT-LOGIOR-2))
 (22 2 (:REWRITE MOD-X-Y-=-X . 2))
 (22 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (22 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (19 19 (:REWRITE |(< y (+ (- c) x))|))
 (19 19 (:REWRITE |(< x (+ c/d y))|))
 (16 16 (:REWRITE |(equal (+ (- c) x) y)|))
 (16 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (16 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (16 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 2 (:REWRITE MOD-CANCEL-*-CONST))
 (16 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (13 13 (:TYPE-PRESCRIPTION NATP))
 (12 4
     (:REWRITE |(n32p (r32 addr (g :mem st)))|))
 (11 11 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:TYPE-PRESCRIPTION N32P))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 2 (:REWRITE DEFAULT-MOD-1))
 (6 1 (:REWRITE DISJOINT-8-ITEMS))
 (4 4 (:REWRITE DEFAULT-LOGIOR-1))
 (4 1 (:REWRITE |(* a (/ a) b)|))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE DEFAULT-MOD-2))
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
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|)))
($$$ASSERTION-IMPLIES-CUTPOINT
 (43647 6 (:REWRITE FLOOR-=-X/Y . 4))
 (11154 418 (:REWRITE THE-FLOOR-BELOW))
 (9207 9207
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9207 9207
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6591 73 (:REWRITE FLOOR-ZERO . 3))
 (5999 73 (:REWRITE CANCEL-FLOOR-+))
 (4457 73 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (4138 73 (:REWRITE FLOOR-ZERO . 5))
 (4072 73 (:REWRITE FLOOR-ZERO . 4))
 (3609 365 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3285 365
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3285 365
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (3285 365
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3087 462 (:REWRITE INTEGERP-MINUS-X))
 (3019 1194 (:REWRITE DEFAULT-TIMES-2))
 (2983 2983
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (2860 387 (:REWRITE DEFAULT-PLUS-1))
 (2681 1194 (:REWRITE DEFAULT-TIMES-1))
 (2603 73 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2556 284
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (2339 73 (:REWRITE FLOOR-=-X/Y . 3))
 (2235 73 (:REWRITE FLOOR-=-X/Y . 2))
 (2082 54
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2058 54
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1966 152 (:REWRITE |(* (- x) y)|))
 (1955 391
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1825 365 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1825 365 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1825 365
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1819 391
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1594 405
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1418 648
       (:LINEAR |(n32p (r32 addr (g :mem st)))|))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1356 1356
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1279 73 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1219 4 (:DEFINITION NATP))
 (1162 29 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1090 152 (:REWRITE |(- (* c x))|))
 (1029 173 (:REWRITE ACL2-NUMBERP-X))
 (1028 152 (:REWRITE DEFAULT-MINUS))
 (969 29 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (949 354 (:REWRITE DEFAULT-LOGAND-2))
 (748 416 (:REWRITE DEFAULT-LESS-THAN-2))
 (642 642
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (556 73 (:REWRITE FLOOR-ZERO . 2))
 (556 73 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (556 73 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (555 391 (:REWRITE SIMPLIFY-SUMS-<))
 (530 106 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (530 106 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (530 106
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (522 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (464 405
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (464 405
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (459 73
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (459 73 (:REWRITE FLOOR-CANCEL-*-CONST))
 (459 73
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (436 4 (:REWRITE CROCK-200))
 (428 107 (:REWRITE RATIONALP-X))
 (391 391
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (391 391 (:REWRITE INTEGERP-<-CONSTANT))
 (391 391 (:REWRITE CONSTANT-<-INTEGERP))
 (391 391
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (391 391
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (391 391
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (391 391
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (391 391 (:REWRITE |(< c (- x))|))
 (391 391
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (391 391
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (391 391
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (391 391
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (391 391 (:REWRITE |(< (/ x) (/ y))|))
 (391 391 (:REWRITE |(< (- x) c)|))
 (391 391 (:REWRITE |(< (- x) (- y))|))
 (386 386 (:REWRITE REDUCE-INTEGERP-+))
 (386 386 (:META META-INTEGERP-CORRECT))
 (354 354 (:REWRITE DEFAULT-LOGAND-1))
 (350 350 (:REWRITE LOGAND-CONSTANT-MASK))
 (296 296 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (283 95 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (283 95 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (264 73 (:REWRITE DEFAULT-FLOOR-1))
 (249 249
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (199 22
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (184 2 (:REWRITE CANCEL-MOD-+))
 (170 73
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (170 73
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (145 145 (:REWRITE |(< (* x y) 0)|))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (135 135
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (135 135 (:REWRITE |(< (/ x) 0)|))
 (132 2 (:REWRITE MOD-X-Y-=-X . 4))
 (123 55
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (123 2 (:REWRITE MOD-X-Y-=-X . 3))
 (121 121 (:TYPE-PRESCRIPTION ABS))
 (118 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (115 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (111 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (109 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (107 107 (:REWRITE REDUCE-RATIONALP-+))
 (107 107 (:REWRITE REDUCE-RATIONALP-*))
 (107 107 (:REWRITE RATIONALP-MINUS-X))
 (107 107 (:META META-RATIONALP-CORRECT))
 (106 106
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (106 106
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (106 106 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (106 2 (:REWRITE O-INFP->NEQ-0))
 (106 2 (:REWRITE MOD-ZERO . 4))
 (102 102 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (102 102
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (82 82
     (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (75 22
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (75 1
     (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (74 2 (:REWRITE MOD-ZERO . 3))
 (73 73 (:REWRITE DEFAULT-FLOOR-2))
 (73 73 (:REWRITE |(floor x (- y))| . 2))
 (73 73 (:REWRITE |(floor x (- y))| . 1))
 (73 73
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (73 73
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (73 73 (:REWRITE |(floor (- x) y)| . 2))
 (73 73 (:REWRITE |(floor (- x) y)| . 1))
 (67 67
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (65 65
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (65 65 (:REWRITE |(< 0 (/ x))|))
 (65 65 (:REWRITE |(< 0 (* x y))|))
 (61 1 (:REWRITE |(floor (+ x r) i)|))
 (54 54
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (54 54
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (54 54 (:REWRITE |(equal c (/ x))|))
 (54 54 (:REWRITE |(equal c (- x))|))
 (54 54 (:REWRITE |(equal (/ x) c)|))
 (54 54 (:REWRITE |(equal (/ x) (/ y))|))
 (54 54 (:REWRITE |(equal (- x) c)|))
 (54 54 (:REWRITE |(equal (- x) (- y))|))
 (43 43 (:REWRITE |(equal (+ (- c) x) y)|))
 (41 5
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (40 2 (:REWRITE DEFAULT-MOD-RATIO))
 (37 37
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (28 4 (:REWRITE DEFAULT-LOGIOR-2))
 (22 2 (:REWRITE MOD-X-Y-=-X . 2))
 (22 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (22 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (21 21 (:REWRITE |(< (+ c/d x) y)|))
 (20 20 (:REWRITE |(< y (+ (- c) x))|))
 (20 20 (:REWRITE |(< x (+ c/d y))|))
 (16 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (16 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (16 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 2 (:REWRITE MOD-CANCEL-*-CONST))
 (16 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (13 13 (:TYPE-PRESCRIPTION NATP))
 (12 4
     (:REWRITE |(n32p (r32 addr (g :mem st)))|))
 (11 11 (:REWRITE FOLD-CONSTS-IN-+))
 (9
   9
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9
  9
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9 9
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION N32P))
 (8 2 (:REWRITE DEFAULT-MOD-1))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (6 1 (:REWRITE DISJOINT-8-ITEMS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4 (:REWRITE DEFAULT-LOGIOR-1))
 (4 1 (:REWRITE |(* a (/ a) b)|))
 (3 1
    (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE DEFAULT-MOD-2))
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
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1 (:REWRITE |(equal (* x y) 0)|))
 (1 1
    (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1
  1
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|)))
($$$EXISTS-NEXT-CUTPOINT)
($$$EXISTS-NEXT-CUTPOINT-SUFF)
(|(init_pdpt-pre s)|
 (2293 1988 (:REWRITE DEFAULT-PLUS-2))
 (2168 1988 (:REWRITE DEFAULT-PLUS-1))
 (1478 58
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1175 1175
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1140
  51
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (815 815
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (592 6
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (459 121 (:REWRITE DEFAULT-LOGAND-2))
 (396 396
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (396 396
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (360 3 (:REWRITE DISJOINT-3-ITEMS))
 (236
   236
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (236
  236
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (236
     236
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (236 236
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (194 194
      (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (143 62 (:REWRITE DEFAULT-LESS-THAN-1))
 (121 121 (:REWRITE DEFAULT-LOGAND-1))
 (117 117 (:REWRITE LOGAND-CONSTANT-MASK))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (96 96 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (80 17 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (80 17 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (78 34
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (73 62 (:REWRITE DEFAULT-LESS-THAN-2))
 (62 62 (:REWRITE THE-FLOOR-BELOW))
 (62 62 (:REWRITE THE-FLOOR-ABOVE))
 (60 34
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (60 34 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (58 58
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (58 58
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (56 31 (:REWRITE DEFAULT-TIMES-2))
 (55 31 (:REWRITE DEFAULT-TIMES-1))
 (46 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (39 39
     (:REWRITE |(g field (w32 addr val st))|))
 (39 39 (:REWRITE |(< (+ c/d x) y)|))
 (36 12 (:REWRITE DEFAULT-LOGIOR-2))
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
 (33 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 26 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (19 19
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE |(< (+ (- c) x) y)|))
 (13 13 (:REWRITE |(< x (+ c/d y))|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:REWRITE DEFAULT-LOGIOR-1))
 (12 12 (:META META-INTEGERP-CORRECT))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (11 1 (:REWRITE DISJOINT-8-ITEMS))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(init_pdts-pre s)|
 (11992 8991 (:REWRITE DEFAULT-PLUS-2))
 (10145 8991 (:REWRITE DEFAULT-PLUS-1))
 (6954 6
       (:REWRITE |(good-state-p (s field val) s) --- n01p|))
 (5843 5843
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3409 3409
       (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (2555 1277 (:REWRITE DEFAULT-LOGAND-2))
 (1849
  1244
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (1493 1493
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1277 1277 (:REWRITE LOGAND-CONSTANT-MASK))
 (1277 1277 (:REWRITE DEFAULT-LOGAND-1))
 (1157
   1157
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1157
  1157
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1157
      1157
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1157
     1157
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1157 1157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1157 1157
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1098 48
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (662 19
      (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (566 566
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (566 566
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (328 287 (:REWRITE DEFAULT-TIMES-2))
 (287 287
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (287 287 (:REWRITE DEFAULT-TIMES-1))
 (246 246 (:REWRITE FOLD-CONSTS-IN-+))
 (196 172 (:REWRITE DEFAULT-LOGIOR-2))
 (184 4 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (172 172 (:REWRITE DEFAULT-LOGIOR-1))
 (115 115
      (:REWRITE |(g field (w32 addr val st))|))
 (101 3 (:REWRITE |(n32-to-i32 x) --- 2|))
 (99 3 (:REWRITE |(n32-to-i32 x) --- 1|))
 (73 48 (:REWRITE DEFAULT-LESS-THAN-1))
 (73 29
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (68 13 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (68 13 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (59 48 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 29
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (55 29 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (48 48 (:REWRITE THE-FLOOR-BELOW))
 (48 48 (:REWRITE THE-FLOOR-ABOVE))
 (48 48
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (46 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (33 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (29 29 (:REWRITE INTEGERP-<-CONSTANT))
 (29 29 (:REWRITE CONSTANT-<-INTEGERP))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< c (- x))|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (29 29
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (29 29 (:REWRITE |(< (/ x) (/ y))|))
 (29 29 (:REWRITE |(< (- x) c)|))
 (29 29 (:REWRITE |(< (- x) (- y))|))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (18 16 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 4 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< 0 (/ x))|))
 (5 5 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(|(create_nested_pt-pre s)|
 (186370 141115 (:REWRITE DEFAULT-PLUS-2))
 (159959 141115 (:REWRITE DEFAULT-PLUS-1))
 (100315 100315
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (66696 48
        (:REWRITE |(good-state-p (s field val) s) --- n01p|))
 (63796 63796
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (48478 25184 (:REWRITE DEFAULT-LOGAND-2))
 (38519
  23456
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (34791 899
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (28484 512
        (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (25256 25184 (:REWRITE DEFAULT-LOGAND-1))
 (25184 25184 (:REWRITE LOGAND-CONSTANT-MASK))
 (21390 21390
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (20838
   20838
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20838
  20838
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (20838
      20838
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20838
     20838
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20838 20838
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20838 20838
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6922 6922
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6922 6922
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (4768 4768
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4768 4768 (:REWRITE FOLD-CONSTS-IN-+))
 (4768 4768 (:REWRITE DEFAULT-TIMES-2))
 (4768 4768 (:REWRITE DEFAULT-TIMES-1))
 (3892 112
       (:REWRITE |(r32 addr (w32 addr val st)) --- paging|))
 (3396 3212 (:REWRITE DEFAULT-LOGIOR-2))
 (3212 3212 (:REWRITE DEFAULT-LOGIOR-1))
 (2767 881 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (2767 881 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (2644 2644
       (:REWRITE |(g field (w32 addr val st))|))
 (1694 899 (:REWRITE DEFAULT-LESS-THAN-1))
 (1688 120 (:REWRITE |(n32-to-i32 x) --- 2|))
 (1656 120 (:REWRITE |(n32-to-i32 x) --- 1|))
 (974 899 (:REWRITE DEFAULT-LESS-THAN-2))
 (931 492
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (931 492
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (920 20 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (899 899 (:REWRITE THE-FLOOR-BELOW))
 (899 899 (:REWRITE THE-FLOOR-ABOVE))
 (899 899
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (899 899
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (599 599 (:REWRITE |(< (+ c/d x) y)|))
 (508 508 (:REWRITE INTEGERP-<-CONSTANT))
 (508 508 (:REWRITE CONSTANT-<-INTEGERP))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< c (- x))|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (508 508
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (508 508 (:REWRITE |(< (/ x) (/ y))|))
 (508 508 (:REWRITE |(< (- x) c)|))
 (508 508 (:REWRITE |(< (- x) (- y))|))
 (448 84
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (448 84
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (432 84 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (416 384 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (208 208 (:REWRITE |(< (+ (- c) x) y)|))
 (187 187 (:REWRITE |(< x (+ c/d y))|))
 (120 120 (:REWRITE |(< (* x y) 0)|))
 (84 84
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (84 84
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (84 84 (:REWRITE |(equal c (/ x))|))
 (84 84 (:REWRITE |(equal c (- x))|))
 (84 84 (:REWRITE |(equal (/ x) c)|))
 (84 84 (:REWRITE |(equal (/ x) (/ y))|))
 (84 84 (:REWRITE |(equal (- x) c)|))
 (84 84 (:REWRITE |(equal (- x) (- y))|))
 (60 20 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (40 40 (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (36 36 (:REWRITE |(< 0 (/ x))|))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (28 28
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (28 28 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< y (+ (- c) x))|))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(INIT_PDPT-PRE-FALSE)
(INIT_PDTS-PRE-FALSE)
(SEC_NOT_PRESENT-PRE-FALSE)
(WHY-0)
(SIMULATE-MAIN
 (1352719 1024099 (:REWRITE DEFAULT-PLUS-2))
 (1166645 1024099 (:REWRITE DEFAULT-PLUS-1))
 (697945 697945
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (301766 158006 (:REWRITE DEFAULT-LOGAND-2))
 (158006 158006 (:REWRITE DEFAULT-LOGAND-1))
 (138535 1986
         (:REWRITE |(r32 addr1 (w32 addr2 val st)) --- paging|))
 (135296
   135296
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (135296
  135296
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (135296
      135296
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (135296
     135296
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (135296 135296
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (135296 135296
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (115747 115747
         (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (92014 3422 (:REWRITE |(n32-to-i32 x) --- 2|))
 (90206 3422 (:REWRITE |(n32-to-i32 x) --- 1|))
 (40295 34647 (:REWRITE DEFAULT-TIMES-2))
 (34710 34647 (:REWRITE DEFAULT-TIMES-1))
 (33965 33965
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (32603 32603 (:REWRITE FOLD-CONSTS-IN-+))
 (30053 12744
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (26182 26182
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (26182 26182
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (20332 20180 (:REWRITE DEFAULT-LOGIOR-2))
 (20180 20180 (:REWRITE DEFAULT-LOGIOR-1))
 (17376 5268 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (17376 5268 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (14176 12744 (:REWRITE DEFAULT-LESS-THAN-1))
 (13975 12744 (:REWRITE DEFAULT-LESS-THAN-2))
 (12744 12744 (:REWRITE THE-FLOOR-BELOW))
 (12744 12744 (:REWRITE THE-FLOOR-ABOVE))
 (12661 12519
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11394 1327
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10208 2784 (:REWRITE ACL2-NUMBERP-X))
 (9548 6891 (:REWRITE |(< c (- x))|))
 (9171 6816 (:REWRITE CONSTANT-<-INTEGERP))
 (9096 6741 (:REWRITE INTEGERP-<-CONSTANT))
 (7857 7857 (:REWRITE |(< (+ c/d x) y)|))
 (7003 6891 (:REWRITE |(< (- x) (- y))|))
 (6891 6891
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6891 6891
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6891 6891
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6891 6891
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6891 6891
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6891 6891
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6891 6891
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6891 6891
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6891 6891 (:REWRITE |(< (/ x) (/ y))|))
 (5678 4366 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5182 77
       (:REWRITE |(< x (/ y)) with (< y 0)|))
 (3970 1327
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3712 928 (:REWRITE RATIONALP-X))
 (2231 2231 (:REWRITE |(< (+ (- c) x) y)|))
 (2130 150 (:REWRITE |(* y (* x z))|))
 (1904 40 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1888 1888 (:REWRITE |(< x (+ c/d y))|))
 (1327 1327
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1327 1327
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1327 1327
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1327 1327 (:REWRITE |(equal c (/ x))|))
 (1327 1327 (:REWRITE |(equal c (- x))|))
 (1327 1327 (:REWRITE |(equal (/ x) c)|))
 (1327 1327 (:REWRITE |(equal (/ x) (/ y))|))
 (1327 1327 (:REWRITE |(equal (- x) c)|))
 (1327 1327 (:REWRITE |(equal (- x) (- y))|))
 (1141 1141
       (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (928 928 (:REWRITE REDUCE-RATIONALP-+))
 (928 928 (:REWRITE REDUCE-RATIONALP-*))
 (928 928 (:REWRITE REDUCE-INTEGERP-+))
 (928 928 (:REWRITE RATIONALP-MINUS-X))
 (928 928 (:REWRITE INTEGERP-MINUS-X))
 (928 928 (:META META-RATIONALP-CORRECT))
 (928 928 (:META META-INTEGERP-CORRECT))
 (714 367 (:REWRITE DEFAULT-MINUS))
 (590 590 (:REWRITE |(* (- x) y)|))
 (509 509 (:TYPE-PRESCRIPTION ABS))
 (430 75 (:REWRITE |(* c (* d x))|))
 (270 270 (:REWRITE |(< y (+ (- c) x))|))
 (262 152
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (260 150 (:REWRITE |(* a (/ a) b)|))
 (242 242 (:REWRITE |(< (* x y) 0)|))
 (152 152
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (152 152
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (152 152
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (100 40 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (97 97 (:REWRITE |(< 0 (* x y))|))
 (95 95 (:REWRITE |(< 0 (/ x))|))
 (91 91
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (91 91
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (76 76 (:REWRITE |(equal (+ (- c) x) y)|))
 (23 1 (:REWRITE DEFAULT-MOD-RATIO))
 (20 10 (:REWRITE O-INFP->NEQ-0))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 4
    (:REWRITE |(r08 addr (s field val st))|))
 (8 2
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (6 2
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 1 (:REWRITE |(n32 n)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE DEFAULT-MOD-1)))
(ASSERTION-INVARIANT-DEFAULT-HINT-1)
(ASSERTION-INVARIANT-DEFAULT-HINT)
($$$ASSERTION-INVARIANT-OVER-CUTPOINTS
 (77661 4813
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (63256 63256
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (54604 49445 (:REWRITE DEFAULT-PLUS-1))
 (52368
  52235
  (:REWRITE
   |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 (42844 42844
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29734 29734
        (:REWRITE CREATE_NESTED_PT-LOADED-THM-32))
 (29528 12835 (:REWRITE DEFAULT-LOGAND-2))
 (26902 804 (:REWRITE |(n32-to-i32 x) --- 2|))
 (26370 804 (:REWRITE |(n32-to-i32 x) --- 1|))
 (12835 12835 (:REWRITE LOGAND-CONSTANT-MASK))
 (12835 12835 (:REWRITE DEFAULT-LOGAND-1))
 (7543
  7543
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|))
 (7543
  7543
  (:REWRITE
   |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 (7016 1078 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (7016 1078 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (6697 2990
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6517 2990
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5895
   5895
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (5895
  5895
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5895
      5895
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5895
     5895
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5895 5895
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5895 5895
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5603 4830 (:REWRITE DEFAULT-LESS-THAN-2))
 (4846 4846 (:REWRITE THE-FLOOR-BELOW))
 (4846 4846 (:REWRITE THE-FLOOR-ABOVE))
 (4813 4813
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4813 4813
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3857 601 (:REWRITE ACL2-NUMBERP-X))
 (3489 599
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3433 599
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3429 599 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3326 36 (:DEFINITION NATP))
 (2991 2991 (:REWRITE INTEGERP-<-CONSTANT))
 (2991 2991 (:REWRITE CONSTANT-<-INTEGERP))
 (2991 2991
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2991 2991
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2991 2991
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2991 2991
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2991 2991 (:REWRITE |(< c (- x))|))
 (2991 2991
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2991 2991
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2991 2991
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2991 2991
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2991 2991 (:REWRITE |(< (/ x) (/ y))|))
 (2991 2991 (:REWRITE |(< (- x) c)|))
 (2991 2991 (:REWRITE |(< (- x) (- y))|))
 (2210 2210 (:REWRITE |(< (+ c/d x) y)|))
 (2160 1890 (:REWRITE DEFAULT-TIMES-2))
 (1890 1890
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1890 1890 (:REWRITE DEFAULT-TIMES-1))
 (1832 1649
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1628 407 (:REWRITE RATIONALP-X))
 (1620 1620 (:REWRITE FOLD-CONSTS-IN-+))
 (1416 16 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (1416 16 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (1400 16 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1352 1352
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1352 1352
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1352 1352
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1320 16 (:REWRITE |(< (logior x y) 0)|))
 (1208 1080 (:REWRITE DEFAULT-LOGIOR-2))
 (1080 1080 (:REWRITE DEFAULT-LOGIOR-1))
 (730 366 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (599 599
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (599 599
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (599 599
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (599 599 (:REWRITE |(equal c (/ x))|))
 (599 599 (:REWRITE |(equal c (- x))|))
 (599 599 (:REWRITE |(equal (/ x) c)|))
 (599 599 (:REWRITE |(equal (/ x) (/ y))|))
 (599 599 (:REWRITE |(equal (- x) c)|))
 (599 599 (:REWRITE |(equal (- x) (- y))|))
 (534 78
      (:REWRITE |(memoryp (g :mem (sec_not_present-modify s)))|))
 (486 12 (:REWRITE |(< (if a b c) x)|))
 (413 413 (:REWRITE REDUCE-INTEGERP-+))
 (413 413 (:REWRITE INTEGERP-MINUS-X))
 (413 413 (:META META-INTEGERP-CORRECT))
 (407 407 (:REWRITE REDUCE-RATIONALP-+))
 (407 407 (:REWRITE REDUCE-RATIONALP-*))
 (407 407 (:REWRITE RATIONALP-MINUS-X))
 (407 407 (:META META-RATIONALP-CORRECT))
 (393 102
      (:REWRITE |(create_nested_pt-pre s)|))
 (388 388 (:REWRITE |(< (+ (- c) x) y)|))
 (339 339 (:REWRITE |(< (* x y) 0)|))
 (268 268
      (:TYPE-PRESCRIPTION N32-TO-I32-TYPE))
 (220 220
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (220 220
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (220 220 (:REWRITE |(< (/ x) 0)|))
 (204 204
      (:TYPE-PRESCRIPTION SEC_NOT_PRESENT-PRE))
 (187 187 (:REWRITE |(< x (+ c/d y))|))
 (186 186 (:REWRITE |(< y (+ (- c) x))|))
 (179 71
      (:REWRITE |(r32 addr (sec_not_present-modify s))|))
 (161 161
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (161 161
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (161 161 (:REWRITE |(< 0 (/ x))|))
 (161 161 (:REWRITE |(< 0 (* x y))|))
 (112 16 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (97 97 (:REWRITE |(equal (+ (- c) x) y)|))
 (36 36 (:TYPE-PRESCRIPTION NATP))
 (34 7
     (:REWRITE |(good-state-p (s field val) s) --- n01p|))
 (32 5
     (:REWRITE |(y86-p (sec_not_present-modify s))|))
 (19 7
     (:REWRITE |(good-state-p (s field val) s) --- n32p|))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (8 2
    (:REWRITE |(good-state-p (sec_not_present-modify s))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:TYPE-PRESCRIPTION N32-TO-I32)))
(CREATE_NESTED_PT-EXITSTEPS-TAIL)
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-defpun-test|)
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-defpun-base|)
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-step|)
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-defpun-stn|)
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-defpun-fn|
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1|
 (1
  1
  (:TYPE-PRESCRIPTION |CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-defpun-stn|)))
(|CREATE_NESTED_PT-EXITSTEPS-TAIL-arity-1-DEF|)
(CREATE_NESTED_PT-EXITSTEPS-TAIL)
(CREATE_NESTED_PT-EXITSTEPS-TAIL-DEF
     (6 6 (:REWRITE DEFAULT-CAR))
     (4 2 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-CDR))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 2 (:REWRITE DEFAULT-+-1)))
(CREATE_NESTED_PT-EXITSTEPS-TAIL$DEF)
(CREATE_NESTED_PT-EXITSTEPS)
(CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT)
(CREATE_NESTED_PT-EXISTS-NEXT-EXITPOINT-SUFF)
(CREATE_NESTED_PT-NEXT-EXITPOINT)
(CREATE_NESTED_PT-CORRECT)
