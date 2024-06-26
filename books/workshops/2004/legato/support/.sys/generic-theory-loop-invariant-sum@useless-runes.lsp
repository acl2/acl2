(DEC)
(WP-LOOP
 (8 8 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (8 8 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (8 8 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (8 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (8 8 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (8 8 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (6 6 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
 )
(WP-1)
(WP-SUM-INVARIANT
 (23 23 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (23 23 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 )
(WP-SUM-LOOP-INVARIANT
 (12157 218 (:REWRITE CANCEL-FLOOR-+))
 (12024 87 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (8929 218 (:REWRITE FLOOR-ZERO . 4))
 (8020 478 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6738 903 (:REWRITE DEFAULT-+-2))
 (3886 16 (:REWRITE |(< (+ c x y) d)|))
 (3392 81 (:REWRITE CANCEL-MOD-+))
 (3107 56 (:REWRITE MOD-ZERO . 2))
 (3039 506 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2939 2911 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2939 2911 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2939 2911 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2819 70 (:LINEAR FLOOR-BOUNDS-3))
 (2819 70 (:LINEAR FLOOR-BOUNDS-2))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2648 2648 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (2573 2573 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (2548 1269 (:REWRITE DEFAULT-*-2))
 (2208 81 (:REWRITE MOD-X-Y-=-X . 4))
 (1988 420 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1819 751 (:META META-INTEGERP-CORRECT))
 (1318 748 (:REWRITE INTEGERP-MINUS-X))
 (1277 56 (:REWRITE MOD-ZERO . 3))
 (1269 1269 (:REWRITE DEFAULT-*-1))
 (1196 718 (:REWRITE REDUCE-INTEGERP-+))
 (1120 407 (:REWRITE DEFAULT-<-1))
 (1047 1047 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1047 1047 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (903 903 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (762 117 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (740 24 (:REWRITE |(* (if a b c) x)|))
 (704 41 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (677 407 (:REWRITE DEFAULT-<-2))
 (662 554 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (641 218 (:REWRITE FLOOR-CANCEL-*-WEAK))
 (640 217 (:REWRITE FLOOR-ZERO . 2))
 (640 217 (:REWRITE FLOOR-COMPLETION))
 (635 218 (:REWRITE FLOOR-MINUS-WEAK))
 (623 41 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (587 587 (:REWRITE |(integerp (* c x))|))
 (584 38 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (520 22 (:LINEAR MOD-BOUNDS-3))
 (507 67 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (506 506 (:REWRITE |(< (- x) (- y))|))
 (487 218 (:REWRITE FLOOR-MINUS-2))
 (477 477 (:REWRITE DEFAULT-CAR))
 (437 437 (:REWRITE DEFAULT-CDR))
 (420 420 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (420 420 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (420 420 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (405 405 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (350 281 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (302 302 (:REWRITE |(expt x (- n))|))
 (302 302 (:REWRITE |(expt 2^i n)|))
 (302 302 (:REWRITE |(expt 1/c n)|))
 (302 302 (:REWRITE |(expt (- x) n)|))
 (274 274 (:REWRITE DEFAULT-EXPT-2))
 (274 274 (:REWRITE DEFAULT-EXPT-1))
 (252 252 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (252 252 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (248 54 (:LINEAR EXPT-X->-X))
 (197 57 (:LINEAR EXPT-<-1-TWO))
 (196 28 (:REWRITE |(* (/ x) (expt x n))|))
 (184 112 (:REWRITE MOD-COMPLETION))
 (174 6 (:REWRITE |(* x (if a b c))|))
 (153 81 (:REWRITE MOD-NEG))
 (153 81 (:REWRITE MOD-CANCEL-*))
 (152 44 (:REWRITE DEFAULT-UNARY-MINUS))
 (147 57 (:LINEAR EXPT->-1-TWO))
 (147 57 (:LINEAR EXPT-<-1-ONE))
 (143 143 (:REWRITE |(< 0 (- x))|))
 (142 142 (:REWRITE FOLD-CONSTS-IN-+))
 (128 128 (:REWRITE |(- (- x))|))
 (114 114 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (114 114 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (114 114 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (114 114 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (108 108 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (87 87 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (87 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (81 81 (:REWRITE MOD-MINUS-2))
 (80 44 (:REWRITE |(* c (* d x))|))
 (56 56 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (56 56 (:REWRITE MOD-X-Y-=-X . 2))
 (56 56 (:REWRITE DEFAULT-UNARY-/))
 (44 44 (:LINEAR MOD-BOUNDS-2))
 (41 41 (:REWRITE |(equal (- x) (- y))|))
 (29 29 (:REWRITE EXPT-X->-X))
 (28 28 (:REWRITE |(expt x 1)|))
 (28 28 (:REWRITE |(* a (/ a))|))
 (24 24 (:REWRITE |(< (- x) 0)|))
 (19 19 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (12 12 (:REWRITE |(< d (+ c x y))|))
 (12 3 (:REWRITE |(+ x x)|))
 (11 11 (:REWRITE |(equal (- x) 0)|))
 (8 8 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE EXPT-X->=-X))
 (4 4 (:REWRITE |(equal (+ c x y) d)|))
 (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
 )
(WP-LOOP-IS-CORRECT
 (532 8 (:REWRITE CANCEL-FLOOR-+))
 (186 32 (:REWRITE DEFAULT-+-2))
 (171 8 (:REWRITE FLOOR-ZERO . 3))
 (146 2 (:LINEAR FLOOR-BOUNDS-3))
 (146 2 (:LINEAR FLOOR-BOUNDS-2))
 (108 22 (:REWRITE REDUCE-INTEGERP-+))
 (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (98 98 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (94 40 (:REWRITE DEFAULT-*-2))
 (80 32 (:REWRITE DEFAULT-+-1))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (59 59 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (57 57 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (53 11 (:REWRITE SIMPLIFY-SUMS-<))
 (53 11 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (53 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (53 11 (:REWRITE DEFAULT-<-1))
 (44 8 (:REWRITE FLOOR-ZERO . 4))
 (40 40 (:REWRITE DEFAULT-*-1))
 (32 32 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (32 32 (:REWRITE NORMALIZE-ADDENDS))
 (26 8 (:REWRITE FLOOR-ZERO . 2))
 (26 8 (:REWRITE FLOOR-COMPLETION))
 (26 8 (:REWRITE FLOOR-CANCEL-*-WEAK))
 (22 22 (:REWRITE INTEGERP-MINUS-X))
 (22 22 (:META META-INTEGERP-CORRECT))
 (20 8 (:REWRITE FLOOR-MINUS-WEAK))
 (20 8 (:REWRITE FLOOR-MINUS-2))
 (19 19 (:REWRITE DEFAULT-EXPT-2))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt x (- n))|))
 (19 19 (:REWRITE |(expt 2^i n)|))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE |(integerp (* c x))|))
 (11 11 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE |(< (- x) (- y))|))
 (10 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (8 1 (:LINEAR EXPT-X->-X))
 (8 1 (:LINEAR EXPT->-1-ONE))
 (8 1 (:LINEAR EXPT-<-1-TWO))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (4 4 (:REWRITE |(< (+ c x) d)|))
 (4 4 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE))
 )
