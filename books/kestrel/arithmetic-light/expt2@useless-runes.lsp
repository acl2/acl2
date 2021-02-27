(INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2
     (101 101 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (101 101
          (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (26 2 (:REWRITE DEFAULT-UNARY-/))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (8 8 (:REWRITE DEFAULT-EXPT-2))
     (8 8 (:REWRITE DEFAULT-EXPT-1))
     (8 8 (:REWRITE |(expt x (- n))|))
     (8 8 (:REWRITE |(expt 2^i n)|))
     (8 8 (:REWRITE |(expt 1/c n)|))
     (8 8 (:REWRITE |(expt (- x) n)|))
     (7 7 (:REWRITE REDUCE-INTEGERP-+))
     (7 7 (:REWRITE INTEGERP-MINUS-X))
     (7 7 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE |(< (- x) 0)|))
     (4 4 (:REWRITE |(< (+ c x) d)|))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX)))
(INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2-TYPE
     (44 44 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (44 44
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (13 1 (:REWRITE DEFAULT-UNARY-/))
     (3 3 (:REWRITE DEFAULT-EXPT-2))
     (3 3 (:REWRITE DEFAULT-EXPT-1))
     (3 3 (:REWRITE |(expt x (- n))|))
     (3 3 (:REWRITE |(expt 2^i n)|))
     (3 3 (:REWRITE |(expt 1/c n)|))
     (3 3 (:REWRITE |(expt (- x) n)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(INTEGERP-OF-*-OF-/-OF-EXPT2-AND-EXPT2
     (66 66 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (66 66
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (66 66
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (26 2 (:REWRITE DEFAULT-UNARY-/))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (6 6
        (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2-TYPE))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (6 6
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (6 6 (:REWRITE DEFAULT-EXPT-2))
     (6 6 (:REWRITE DEFAULT-EXPT-1))
     (6 6 (:REWRITE |(expt x (- n))|))
     (6 6 (:REWRITE |(expt 2^i n)|))
     (6 6 (:REWRITE |(expt 1/c n)|))
     (6 6 (:REWRITE |(expt (- x) n)|))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:META META-INTEGERP-CORRECT))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE DEFAULT-+-2))
     (2 2 (:REWRITE DEFAULT-+-1))
     (2 2 (:REWRITE |(< (- x) 0)|))
     (2 2 (:REWRITE |(< (+ c x) d)|))
     (2 2 (:REWRITE |(+ c (+ d x))|)))
(INTEGERP-OF-*-OF-/-OF-EXPT2-AND-EXPT2-TYPE
     (44 44 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (44 44
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (13 1 (:REWRITE DEFAULT-UNARY-/))
     (3 3 (:REWRITE DEFAULT-EXPT-2))
     (3 3 (:REWRITE DEFAULT-EXPT-1))
     (3 3 (:REWRITE |(expt x (- n))|))
     (3 3 (:REWRITE |(expt 2^i n)|))
     (3 3 (:REWRITE |(expt 1/c n)|))
     (3 3 (:REWRITE |(expt (- x) n)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1 1
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(< (- x) (- y))|)))
(EXPT-BOUND-LINEAR-WEAK
     (61 61 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (61 61
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (61 61
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (10 1 (:LINEAR EXPT->-1-ONE))
     (10 1 (:LINEAR EXPT-<-1-TWO))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE DEFAULT-EXPT-2))
     (2 2 (:REWRITE DEFAULT-EXPT-1))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1))
     (2 2 (:REWRITE |(expt x (- n))|))
     (2 2 (:REWRITE |(expt 2^i n)|))
     (2 2 (:REWRITE |(expt 1/c n)|))
     (2 2 (:REWRITE |(expt (- x) n)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|))
     (1 1 (:LINEAR EXPT->-1-TWO))
     (1 1 (:LINEAR EXPT-<-1-ONE)))
(*-OF-/-OF-EXPT-AND-*-OF-EXPT-OF-+
     (91 91 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (91 91
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (91 91
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (48 6 (:REWRITE DEFAULT-*-2))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (18 6 (:REWRITE DEFAULT-*-1))
     (13 1 (:REWRITE DEFAULT-UNARY-/))
     (5 5 (:REWRITE DEFAULT-EXPT-2))
     (5 5 (:REWRITE DEFAULT-EXPT-1))
     (5 5 (:REWRITE |(expt x (- n))|))
     (5 5 (:REWRITE |(expt 2^i n)|))
     (5 5 (:REWRITE |(expt 1/c n)|))
     (5 5 (:REWRITE |(expt (- x) n)|))
     (4 4 (:REWRITE |(* c (* d x))|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(EXPT-COMBINE-HACK-2
     (85 85 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (85 85
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (85 85
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (13 1 (:REWRITE DEFAULT-UNARY-/))
     (10 1 (:LINEAR EXPT->-1-ONE))
     (10 1 (:LINEAR EXPT-<-1-TWO))
     (8 1 (:LINEAR EXPT-X->=-X))
     (8 1 (:LINEAR EXPT-X->-X))
     (7 1 (:REWRITE DEFAULT-*-2))
     (7 1 (:REWRITE DEFAULT-*-1))
     (6 6 (:REWRITE |(expt 2^i n)|))
     (6 6 (:REWRITE |(expt 1/c n)|))
     (6 6 (:REWRITE |(expt (- x) n)|))
     (5 5 (:REWRITE DEFAULT-EXPT-2))
     (5 5 (:REWRITE DEFAULT-EXPT-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (2 2
        (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE NORMALIZE-ADDENDS))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|))
     (1 1 (:REWRITE |(* c (* d x))|))
     (1 1 (:LINEAR EXPT->-1-TWO))
     (1 1 (:LINEAR EXPT-<-1-ONE)))
(EXPT-COMBINE-HACK
     (88 88 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (88 88
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (88 88
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (13 1 (:REWRITE DEFAULT-UNARY-/))
     (11 1 (:LINEAR EXPT->-1-ONE))
     (11 1 (:LINEAR EXPT-<-1-TWO))
     (9 1 (:LINEAR EXPT-X->=-X))
     (9 1 (:LINEAR EXPT-X->-X))
     (5 5
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (5 5 (:REWRITE DEFAULT-+-2))
     (5 5 (:REWRITE DEFAULT-+-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE DEFAULT-EXPT-2))
     (4 4 (:REWRITE DEFAULT-EXPT-1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE |(expt x (- n))|))
     (4 4 (:REWRITE |(expt 2^i n)|))
     (4 4 (:REWRITE |(expt 1/c n)|))
     (4 4 (:REWRITE |(expt (- x) n)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< d (+ c x))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE |(+ c (+ d x))|))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (2 2
        (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (1 1
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|))
     (1 1 (:REWRITE |(< (+ c x) d)|))
     (1 1 (:LINEAR EXPT->-1-TWO))
     (1 1 (:LINEAR EXPT-<-1-ONE)))
(EXPT-HACK (49 49 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
           (49 49
               (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
           (30 3 (:LINEAR EXPT->-1-ONE))
           (30 3 (:LINEAR EXPT-<-1-TWO))
           (28 3 (:LINEAR EXPT-X->=-X))
           (28 3 (:LINEAR EXPT-X->-X))
           (26 26
               (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
           (26 2 (:LINEAR EXPT-HALF-LINEAR))
           (22 2 (:DEFINITION NATP))
           (21 21 (:REWRITE DEFAULT-EXPT-2))
           (21 21 (:REWRITE DEFAULT-EXPT-1))
           (17 17 (:REWRITE SIMPLIFY-SUMS-<))
           (17 17
               (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
           (17 17 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
           (17 17 (:REWRITE DEFAULT-<-2))
           (17 17 (:REWRITE DEFAULT-<-1))
           (17 17 (:REWRITE |(< (- x) (- y))|))
           (16 2 (:REWRITE |(< (+ c x) d)|))
           (15 15
               (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
           (15 15 (:REWRITE NORMALIZE-ADDENDS))
           (15 15 (:REWRITE DEFAULT-+-2))
           (15 15 (:REWRITE DEFAULT-+-1))
           (6 6
              (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
           (6 6 (:REWRITE |(expt x (- n))|))
           (6 6 (:REWRITE |(expt 2^i n)|))
           (6 6 (:REWRITE |(expt 1/c n)|))
           (6 6 (:REWRITE |(expt (- x) n)|))
           (6 6
              (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
           (6 6
              (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
           (6 6
              (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
           (6 6
              (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
           (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
           (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
           (6 3
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
           (6 3
              (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
           (3 3
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
           (3 3
              (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
           (3 3 (:REWRITE |(equal (- x) (- y))|))
           (3 3 (:REWRITE |(< 0 (- x))|))
           (3 3 (:REWRITE |(< (- x) 0)|))
           (3 3 (:LINEAR EXPT->-1-TWO))
           (3 3 (:LINEAR EXPT-<-1-ONE))
           (2 2 (:TYPE-PRESCRIPTION NATP))
           (1 1 (:REWRITE REDUCE-INTEGERP-+))
           (1 1 (:REWRITE INTEGERP-MINUS-X))
           (1 1 (:META META-INTEGERP-CORRECT)))
(EXPT-BOUND-WHEN-NEGATIVE
     (27 27 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (27 27
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (27 27
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(EQUAL-OF-1-AND-EXPT (157 157 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
                     (157 157
                          (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
                     (46 7 (:REWRITE DEFAULT-*-2))
                     (42 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                     (42 11
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                     (42 11
                         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                     (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                     (11 11 (:REWRITE |(equal (- x) (- y))|))
                     (11 1 (:LINEAR EXPT-<-1-TWO))
                     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
                     (10 10
                         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                     (10 10
                         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                     (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                     (10 10 (:REWRITE DEFAULT-EXPT-1))
                     (10 10 (:REWRITE DEFAULT-<-2))
                     (10 10 (:REWRITE DEFAULT-<-1))
                     (10 10 (:REWRITE |(< (- x) (- y))|))
                     (8 8
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                     (8 8
                        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                     (8 8 (:REWRITE |(expt x (- n))|))
                     (8 8 (:REWRITE |(expt 2^i n)|))
                     (8 8 (:REWRITE |(expt 1/c n)|))
                     (8 8 (:REWRITE |(expt (- x) n)|))
                     (8 8 (:REWRITE |(< 0 (- x))|))
                     (7 7
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                     (7 7 (:REWRITE NORMALIZE-ADDENDS))
                     (7 7 (:REWRITE DEFAULT-+-2))
                     (7 7 (:REWRITE DEFAULT-+-1))
                     (7 7 (:REWRITE DEFAULT-*-1))
                     (4 4 (:REWRITE REDUCE-INTEGERP-+))
                     (4 4 (:REWRITE INTEGERP-MINUS-X))
                     (4 4 (:META META-INTEGERP-CORRECT))
                     (3 3
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                     (3 3 (:REWRITE |(equal (- x) 0)|))
                     (2 2
                        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                     (2 2 (:REWRITE |(< (- x) 0)|))
                     (2 2 (:REWRITE |(< (+ c x) d)|))
                     (2 2
                        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
                     (2 2
                        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
                     (2 2
                        (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
                     (2 2
                        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
                     (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
                     (1 1 (:REWRITE ZIP-OPEN))
                     (1 1 (:LINEAR EXPT-X->=-X))
                     (1 1 (:LINEAR EXPT-X->-X))
                     (1 1 (:LINEAR EXPT->-1-TWO))
                     (1 1 (:LINEAR EXPT->-1-ONE))
                     (1 1 (:LINEAR EXPT-<-1-ONE)))
(EVEN-NOT-EQUAL-ODD-HACK (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                         (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                         (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                         (24 24 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                         (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
                         (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                         (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                         (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                         (2 2
                            (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
                         (2 2 (:REWRITE DEFAULT-*-2))
                         (2 2 (:REWRITE DEFAULT-*-1))
                         (1 1 (:REWRITE REDUCE-INTEGERP-+))
                         (1 1 (:REWRITE INTEGERP-MINUS-X))
                         (1 1 (:REWRITE |(integerp (* c x))|))
                         (1 1 (:META META-INTEGERP-CORRECT)))
(EVEN-ODD-EXPT-HACK
     (72 1 (:REWRITE ZIP-OPEN))
     (42 1
         (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
     (28 1 (:REWRITE EVEN-AND-ODD-ALTERNATE))
     (25 11 (:REWRITE DEFAULT-+-2))
     (11 11
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (11 11 (:REWRITE NORMALIZE-ADDENDS))
     (11 11 (:REWRITE DEFAULT-+-1))
     (9 1 (:REWRITE |(< d (+ c x))|))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (7 7 (:REWRITE DEFAULT-EXPT-2))
     (7 7 (:REWRITE DEFAULT-EXPT-1))
     (7 1 (:REWRITE |(equal (+ c x) d)|))
     (6 6 (:META META-INTEGERP-CORRECT))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (4 4
        (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (4 4 (:REWRITE REDUCE-INTEGERP-+))
     (4 4 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (3 3
        (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (3 3 (:REWRITE SIMPLIFY-SUMS-<))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 3 (:REWRITE DEFAULT-*-2))
     (3 3 (:REWRITE DEFAULT-*-1))
     (3 3 (:REWRITE |(expt x (- n))|))
     (3 3 (:REWRITE |(expt 2^i n)|))
     (3 3 (:REWRITE |(expt 1/c n)|))
     (3 3 (:REWRITE |(expt (- x) n)|))
     (3 3 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (2 2 (:REWRITE |(integerp (* c x))|))
     (2 2 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1 1
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1 1 (:REWRITE |(equal (- x) (- y))|)))
(EXPT-BOUND-LINEAR (145 145 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
                   (145 145
                        (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
                   (82 82 (:REWRITE DEFAULT-EXPT-2))
                   (82 82 (:REWRITE DEFAULT-EXPT-1))
                   (48 33 (:REWRITE SIMPLIFY-SUMS-<))
                   (48 33
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (48 33 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (46 22
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (42 33 (:REWRITE DEFAULT-<-2))
                   (39 33 (:REWRITE DEFAULT-<-1))
                   (37 37
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (35 35
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (35 35 (:REWRITE NORMALIZE-ADDENDS))
                   (35 35 (:REWRITE DEFAULT-+-2))
                   (35 35 (:REWRITE DEFAULT-+-1))
                   (33 33 (:REWRITE |(< (- x) (- y))|))
                   (32 4 (:LINEAR EXPT-X->=-X))
                   (32 4 (:LINEAR EXPT-X->-X))
                   (26 26 (:REWRITE |(expt x (- n))|))
                   (26 26 (:REWRITE |(expt 2^i n)|))
                   (26 26 (:REWRITE |(expt 1/c n)|))
                   (26 26 (:REWRITE |(expt (- x) n)|))
                   (21 21 (:REWRITE ZIP-OPEN))
                   (17 17
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (17 17 (:REWRITE |(< 0 (- x))|))
                   (12 12 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
                   (8 8
                      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
                   (8 8
                      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
                   (8 8
                      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
                   (8 1
                      (:REWRITE EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
                   (5 5 (:LINEAR EXPT->-1-TWO))
                   (5 5 (:LINEAR EXPT-<-1-ONE))
                   (4 4 (:REWRITE REDUCE-INTEGERP-+))
                   (4 4 (:REWRITE INTEGERP-MINUS-X))
                   (4 4 (:META META-INTEGERP-CORRECT))
                   (3 3
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (3 3 (:REWRITE |(< (- x) 0)|))
                   (1 1
                      (:REWRITE EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
                   (1 1
                      (:REWRITE EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1)))
(EXPT-INTEGER-HACK (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
                   (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
                   (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
                   (9 1 (:REWRITE |(< d (+ c x))|))
                   (7 7
                      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (7 7 (:REWRITE NORMALIZE-ADDENDS))
                   (7 7 (:REWRITE DEFAULT-EXPT-2))
                   (7 7 (:REWRITE DEFAULT-EXPT-1))
                   (7 7 (:REWRITE DEFAULT-+-2))
                   (7 7 (:REWRITE DEFAULT-+-1))
                   (6 1 (:REWRITE ZIP-OPEN))
                   (5 1 (:REWRITE |(equal (+ c x) d)|))
                   (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
                   (4 4
                      (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
                   (4 4
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (4 4
                      (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (3 3 (:REWRITE SIMPLIFY-SUMS-<))
                   (3 3
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (3 3 (:REWRITE DEFAULT-<-2))
                   (3 3 (:REWRITE DEFAULT-<-1))
                   (3 3 (:REWRITE |(expt x (- n))|))
                   (3 3 (:REWRITE |(expt 2^i n)|))
                   (3 3 (:REWRITE |(expt 1/c n)|))
                   (3 3 (:REWRITE |(expt (- x) n)|))
                   (3 3 (:REWRITE |(< (- x) (- y))|))
                   (2 2
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (2 2 (:REWRITE |(< 0 (- x))|))
                   (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (1 1
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (1 1 (:REWRITE REDUCE-INTEGERP-+))
                   (1 1
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (1 1 (:REWRITE INTEGERP-MINUS-X))
                   (1 1 (:REWRITE |(equal (- x) (- y))|))
                   (1 1 (:META META-INTEGERP-CORRECT)))
(EXPT-DIFF-COLLECT
     (88 88 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
     (88 88
         (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
     (88 88
         (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
     (84 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (28 1 (:LINEAR EXPT-X->=-X))
     (28 1 (:LINEAR EXPT-X->-X))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (27 27
         (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-/-OF-EXPT2-AND-EXPT2-TYPE))
     (26 2 (:REWRITE DEFAULT-UNARY-/))
     (25 1 (:LINEAR EXPT->-1-ONE))
     (25 1 (:LINEAR EXPT-<-1-TWO))
     (24 4 (:REWRITE |(+ y (+ x z))|))
     (22 8 (:REWRITE |(+ y x)|))
     (15 7 (:REWRITE NORMALIZE-ADDENDS))
     (14 2 (:REWRITE DEFAULT-*-2))
     (14 2 (:REWRITE DEFAULT-*-1))
     (8 8
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (8 8
        (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (8 8 (:REWRITE |(< (- x) (- y))|))
     (8 4 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
     (6 6 (:REWRITE |(expt 2^i n)|))
     (6 6 (:REWRITE |(expt 1/c n)|))
     (6 6 (:REWRITE |(expt (- x) n)|))
     (6 6 (:REWRITE |(+ 0 x)|))
     (5 5 (:REWRITE DEFAULT-EXPT-2))
     (5 5 (:REWRITE DEFAULT-EXPT-1))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE |(+ x (- x))|))
     (4 4 (:REWRITE |(+ c (+ d x))|))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE DEFAULT-+-2))
     (3 3 (:REWRITE DEFAULT-+-1))
     (3 3 (:REWRITE |(< d (+ c x))|))
     (3 3 (:REWRITE |(< (+ c x) d)|))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:META META-INTEGERP-CORRECT))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
     (2 2
        (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
     (2 2
        (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
     (2 2 (:LINEAR EXPT-BOUND-LINEAR))
     (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
     (1 1 (:REWRITE |(< 0 (- x))|))
     (1 1 (:REWRITE |(< (- x) 0)|))
     (1 1 (:LINEAR EXPT->-1-TWO))
     (1 1 (:LINEAR EXPT-<-1-ONE)))
