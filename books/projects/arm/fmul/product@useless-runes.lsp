(RTL::MULTIPLIER)
(RTL::PPROD)
(RTL::IA)
(RTL::IB)
(RTL::PPA)
(RTL::PPB)
(RTL::PROD*)
(RTL::COMPUTEPRODUCT-LEMMA)
(RTL::SLC)
(RTL::ENC)
(RTL::MUX)
(RTL::UPDATE-PP)
(RTL::LOOP-SIMPLE (32 27 (:REWRITE DEFAULT-PLUS-1))
                  (27 27 (:REWRITE DEFAULT-PLUS-2))
                  (9 9 (:REWRITE THE-FLOOR-BELOW))
                  (9 9 (:REWRITE THE-FLOOR-ABOVE))
                  (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
                  (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
                  (8 8
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                  (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
                  (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
                  (8 8
                     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
                  (8 8
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
                  (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
                  (5 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
                  (4 4 (:REWRITE SIMPLIFY-SUMS-<))
                  (4 4
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (4 2 (:REWRITE GL::NFIX-NATP))
                  (3 3 (:REWRITE |(< (+ c/d x) y)|))
                  (3 3 (:REWRITE |(< (+ (- c) x) y)|))
                  (2 2 (:TYPE-PRESCRIPTION NATP))
                  (2 2 (:REWRITE DEFAULT-MINUS))
                  (2 2 (:REWRITE |(< y (+ (- c) x))|))
                  (2 2 (:REWRITE |(< x (+ c/d y))|))
                  (2 2 (:REWRITE |(< (/ x) 0)|))
                  (2 2 (:REWRITE |(< (* x y) 0)|))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1 (:REWRITE |(< 0 (/ x))|))
                  (1 1 (:REWRITE |(< 0 (* x y))|))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::LOOP-REWRITE
 (133834 2395 (:REWRITE RTL::BITS-TAIL-GEN))
 (101700 8528 (:REWRITE RTL::NEG-BITN-0))
 (63258 1685 (:REWRITE |(< (if a b c) x)|))
 (61399 8528 (:REWRITE RTL::BVECP-BITN-0))
 (42410 29647 (:REWRITE DEFAULT-PLUS-1))
 (40855 29647 (:REWRITE DEFAULT-PLUS-2))
 (40182 4892 (:REWRITE RTL::BITS-NEG-INDICES))
 (35930 3963 (:REWRITE SIMPLIFY-SUMS-<))
 (29199 2809 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (25711 2809 (:REWRITE RTL::BITS-BVECP))
 (24948 8528 (:REWRITE RTL::NEG-BITN-1))
 (18845 5841 (:REWRITE DEFAULT-LESS-THAN-1))
 (17797 2897 (:REWRITE RTL::BITN-BVECP-1))
 (14607 12349 (:REWRITE DEFAULT-TIMES-2))
 (12349 12349 (:REWRITE DEFAULT-TIMES-1))
 (11696 1462 (:REWRITE |(* x (+ y z))|))
 (11331 1091
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11297 4156
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (11220 1020 (:REWRITE |(- (+ x y))|))
 (9863
   9863
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (9863
  9863
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (9863
      9863
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (9863
     9863
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (9863 9863
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (9863 9863
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (9164 872 (:REWRITE |(* -1 x)|))
 (6766 6766
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6567 6567 (:TYPE-PRESCRIPTION LOGNOT))
 (6252 6252
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6083 2395 (:REWRITE RTL::BITS-TAIL))
 (5841 5841 (:REWRITE THE-FLOOR-BELOW))
 (5841 5841 (:REWRITE THE-FLOOR-ABOVE))
 (5841 5841 (:REWRITE DEFAULT-LESS-THAN-2))
 (5801 5801 (:REWRITE RTL::BITN-NEG))
 (5602 4580 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (5254 3963
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5156 3963
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4753 1907
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3963 3963
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3963 3963
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3963 3963 (:REWRITE INTEGERP-<-CONSTANT))
 (3963 3963 (:REWRITE CONSTANT-<-INTEGERP))
 (3963 3963
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3963 3963
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3963 3963
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3963 3963
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3963 3963 (:REWRITE |(< c (- x))|))
 (3963 3963
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3963 3963
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3963 3963
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3963 3963
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3963 3963 (:REWRITE |(< (/ x) (/ y))|))
 (3963 3963 (:REWRITE |(< (- x) c)|))
 (3963 3963 (:REWRITE |(< (- x) (- y))|))
 (3856 3856
       (:TYPE-PRESCRIPTION RTL::MULTIPLIER))
 (3551 871 (:REWRITE |(+ c (+ d x))|))
 (3248 3018 (:REWRITE DEFAULT-MINUS))
 (3152 2440 (:REWRITE RTL::AG-DIFF-AS))
 (2922 2920
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2920 2920
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2920 2920
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2920 2920 (:REWRITE |(equal c (/ x))|))
 (2920 2920 (:REWRITE |(equal c (- x))|))
 (2920 2920 (:REWRITE |(equal (/ x) c)|))
 (2920 2920 (:REWRITE |(equal (/ x) (/ y))|))
 (2920 2920 (:REWRITE |(equal (- x) c)|))
 (2920 2920 (:REWRITE |(equal (- x) (- y))|))
 (2864 2864 (:REWRITE |(* (- x) y)|))
 (2123 193 (:REWRITE |(* y (* x z))|))
 (2112 2112 (:REWRITE |(< (+ c/d x) y)|))
 (2112 2112 (:REWRITE |(< (+ (- c) x) y)|))
 (2083 2083 (:REWRITE |(equal (+ (- c) x) y)|))
 (1697 1697 (:REWRITE REDUCE-INTEGERP-+))
 (1697 1697 (:REWRITE INTEGERP-MINUS-X))
 (1697 1697 (:META META-INTEGERP-CORRECT))
 (1645 1645 (:REWRITE RTL::BITN-BVECP))
 (1602 890 (:REWRITE RTL::AS-DIFF-AS))
 (1230 1230 (:REWRITE SUBSETP-MEMBER . 4))
 (1230 1230 (:REWRITE SUBSETP-MEMBER . 3))
 (1230 1230 (:REWRITE SUBSETP-MEMBER . 2))
 (1230 1230 (:REWRITE SUBSETP-MEMBER . 1))
 (1230 1230 (:REWRITE INTERSECTP-MEMBER . 3))
 (1230 1230 (:REWRITE INTERSECTP-MEMBER . 2))
 (1091 1091 (:REWRITE |(< (/ x) 0)|))
 (1091 1091 (:REWRITE |(< (* x y) 0)|))
 (1010 202 (:REWRITE ACL2-NUMBERP-X))
 (835 835
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (753 753
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (603 603 (:REWRITE |(< y (+ (- c) x))|))
 (603 603 (:REWRITE |(< x (+ c/d y))|))
 (424 424
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (424 424
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (424 424
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (404 101 (:REWRITE RATIONALP-X))
 (295 295 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (202 202 (:TYPE-PRESCRIPTION BOOLEANP))
 (201 201 (:REWRITE FOLD-CONSTS-IN-+))
 (195 195 (:TYPE-PRESCRIPTION ABS))
 (193 193 (:REWRITE |(* a (/ a) b)|))
 (101 101 (:REWRITE REDUCE-RATIONALP-+))
 (101 101 (:REWRITE REDUCE-RATIONALP-*))
 (101 101 (:REWRITE RATIONALP-MINUS-X))
 (101 101 (:META META-RATIONALP-CORRECT)))
(RTL::UPDATE-NOOP
 (652 55 (:REWRITE RTL::NEG-BITN-0))
 (157 55 (:REWRITE RTL::NEG-BITN-1))
 (140 55 (:REWRITE RTL::BVECP-BITN-0))
 (121 17 (:REWRITE ACL2-NUMBERP-X))
 (103 16
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (59
   59
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (59
  59
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (59 59
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (52 13 (:REWRITE RATIONALP-X))
 (45 15 (:REWRITE RTL::BITS-TAIL-GEN))
 (39 39 (:REWRITE RTL::BITN-NEG))
 (36 16 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (35 15 (:REWRITE RTL::BITS-TAIL))
 (32 18 (:REWRITE RTL::BITN-BVECP-1))
 (25 25 (:REWRITE RTL::BITS-NEG-INDICES))
 (24 24
     (:TYPE-PRESCRIPTION RTL::BITS-NONNEGATIVE-INTEGERP-TYPE))
 (23 23 (:REWRITE REDUCE-INTEGERP-+))
 (23 23 (:REWRITE INTEGERP-MINUS-X))
 (23 23 (:META META-INTEGERP-CORRECT))
 (20 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (13 13 (:REWRITE REDUCE-RATIONALP-+))
 (13 13 (:REWRITE REDUCE-RATIONALP-*))
 (13 13 (:REWRITE RATIONALP-MINUS-X))
 (13 13 (:META META-RATIONALP-CORRECT))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (11 11 (:REWRITE RTL::BITN-BVECP))
 (6 6 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (6 6 (:REWRITE RTL::BITS-BVECP))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|)))
(RTL::AG-UPDATE-NIL
 (1184 100 (:REWRITE RTL::NEG-BITN-0))
 (284 100 (:REWRITE RTL::NEG-BITN-1))
 (232 100 (:REWRITE RTL::BVECP-BITN-0))
 (104
   104
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (104
  104
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (104
     104
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (104 104
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (90 30 (:REWRITE RTL::BITS-TAIL-GEN))
 (70 30 (:REWRITE RTL::BITS-TAIL))
 (68 68 (:REWRITE RTL::BITN-NEG))
 (60 36 (:REWRITE RTL::BITN-BVECP-1))
 (40 40 (:REWRITE RTL::BITS-NEG-INDICES))
 (32 15
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (28 28 (:REWRITE RTL::AG-DIFF-AS))
 (25 15 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 24
     (:TYPE-PRESCRIPTION RTL::BITS-NONNEGATIVE-INTEGERP-TYPE))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (22 22 (:REWRITE RTL::BITN-BVECP))
 (16 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
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
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (10 2 (:REWRITE ACL2-NUMBERP-X))
 (6 6 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (6 6 (:REWRITE RTL::BITS-BVECP))
 (4 1 (:REWRITE RATIONALP-X))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::PROD-LOOP-1
     (30 6 (:REWRITE ACL2-NUMBERP-X))
     (30 3
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (18 18 (:REWRITE THE-FLOOR-BELOW))
     (18 18 (:REWRITE THE-FLOOR-ABOVE))
     (18 18 (:REWRITE SIMPLIFY-SUMS-<))
     (18 18
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (18 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (18 18
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (18 18
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 18
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (18 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (18 18 (:REWRITE INTEGERP-<-CONSTANT))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
     (18 18 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (12 3 (:REWRITE RATIONALP-X))
     (11 11 (:REWRITE REDUCE-INTEGERP-+))
     (11 11 (:REWRITE INTEGERP-MINUS-X))
     (11 11 (:META META-INTEGERP-CORRECT))
     (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (8 8
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (8 8 (:REWRITE |(< (/ x) 0)|))
     (8 8 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3 (:REWRITE REDUCE-RATIONALP-+))
     (3 3 (:REWRITE REDUCE-RATIONALP-*))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3 (:REWRITE RATIONALP-MINUS-X))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:META META-RATIONALP-CORRECT))
     (2 2
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (2 2 (:REWRITE NORMALIZE-ADDENDS))
     (2 2 (:REWRITE DEFAULT-PLUS-2))
     (2 2 (:REWRITE DEFAULT-PLUS-1)))
(RTL::PROD-LOOP-2
     (180 27
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (161 25 (:REWRITE ACL2-NUMBERP-X))
     (77 65 (:REWRITE DEFAULT-PLUS-1))
     (68 17 (:REWRITE RATIONALP-X))
     (65 65 (:REWRITE DEFAULT-PLUS-2))
     (61 61 (:REWRITE THE-FLOOR-BELOW))
     (61 61 (:REWRITE THE-FLOOR-ABOVE))
     (61 61 (:REWRITE DEFAULT-LESS-THAN-2))
     (61 61 (:REWRITE DEFAULT-LESS-THAN-1))
     (61 27 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (58 58
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (58 58
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (58 58
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (58 58 (:REWRITE INTEGERP-<-CONSTANT))
     (58 58 (:REWRITE CONSTANT-<-INTEGERP))
     (58 58
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (58 58
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (58 58
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (58 58
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (58 58 (:REWRITE |(< c (- x))|))
     (58 58
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (58 58
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (58 58
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (58 58
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (58 58 (:REWRITE |(< (/ x) (/ y))|))
     (58 58 (:REWRITE |(< (- x) c)|))
     (58 58 (:REWRITE |(< (- x) (- y))|))
     (57 57 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (54 54 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (35 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (34 34 (:TYPE-PRESCRIPTION BOOLEANP))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (30 30 (:REWRITE REDUCE-INTEGERP-+))
     (30 30 (:REWRITE INTEGERP-MINUS-X))
     (30 30 (:META META-INTEGERP-CORRECT))
     (30 6 (:REWRITE |(+ c (+ d x))|))
     (29 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (29 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (27 27
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (27 27 (:REWRITE |(equal c (- x))|))
     (27 27 (:REWRITE |(equal (- x) c)|))
     (26 26 (:REWRITE RTL::AG-UPDATE-NIL))
     (21 21
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (17 17 (:REWRITE REDUCE-RATIONALP-+))
     (17 17 (:REWRITE REDUCE-RATIONALP-*))
     (17 17 (:REWRITE RATIONALP-MINUS-X))
     (17 17 (:META META-RATIONALP-CORRECT))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (12 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (11 11
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (11 11 (:REWRITE |(< (/ x) 0)|))
     (11 11 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:REWRITE DEFAULT-TIMES-2))
     (6 6 (:REWRITE DEFAULT-TIMES-1))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|))
     (5 5 (:REWRITE DEFAULT-DIVIDE))
     (5 5 (:REWRITE |(not (equal x (/ y)))|))
     (5 5 (:REWRITE |(equal x (/ y))|))
     (4 4 (:REWRITE |(< y (+ (- c) x))|))
     (4 4 (:REWRITE |(< x (+ c/d y))|))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(RTL::AG-PPROD-UPDATE
     (2 2 (:REWRITE RTL::UPDATE-NOOP))
     (2 2 (:REWRITE THE-FLOOR-BELOW))
     (2 2 (:REWRITE THE-FLOOR-ABOVE))
     (2 2 (:REWRITE SIMPLIFY-SUMS-<))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2 2
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (2 2 (:REWRITE INTEGERP-<-CONSTANT))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-2))
     (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
     (2 2 (:REWRITE CONSTANT-<-INTEGERP))
     (2 2 (:REWRITE RTL::AG-UPDATE-NIL))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< c (- x))|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2 2
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2 2 (:REWRITE |(< (/ x) (/ y))|))
     (2 2 (:REWRITE |(< (- x) c)|))
     (2 2 (:REWRITE |(< (- x) (- y))|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::BVECP-MANA
 (585 58
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (527 71 (:REWRITE ACL2-NUMBERP-X))
 (228 57 (:REWRITE RATIONALP-X))
 (172 5 (:REWRITE RTL::BITS-TAIL-GEN))
 (158 58 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (86 86 (:TYPE-PRESCRIPTION BOOLEANP))
 (86 58 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (58 58
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (58 58 (:REWRITE REDUCE-INTEGERP-+))
 (58 58
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (58 58 (:REWRITE INTEGERP-MINUS-X))
 (58 58
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (58 58 (:REWRITE |(equal c (/ x))|))
 (58 58 (:REWRITE |(equal c (- x))|))
 (58 58 (:REWRITE |(equal (/ x) c)|))
 (58 58 (:REWRITE |(equal (/ x) (/ y))|))
 (58 58 (:REWRITE |(equal (- x) c)|))
 (58 58 (:REWRITE |(equal (- x) (- y))|))
 (58 58 (:META META-INTEGERP-CORRECT))
 (57 57 (:REWRITE REDUCE-RATIONALP-+))
 (57 57 (:REWRITE REDUCE-RATIONALP-*))
 (57 57 (:REWRITE RATIONALP-MINUS-X))
 (57 57 (:META META-RATIONALP-CORRECT))
 (32 32
     (:TYPE-PRESCRIPTION RTL::INTEGERP-OPA))
 (15 5 (:REWRITE RTL::BITS-TAIL))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE SUBSETP-MEMBER . 4))
 (10 10 (:REWRITE SUBSETP-MEMBER . 3))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (10 10 (:REWRITE INTERSECTP-MEMBER . 3))
 (10 10 (:REWRITE INTERSECTP-MEMBER . 2))
 (8 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (5 5 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|)))
(RTL::BVECP-MANB
 (625 62
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (563 75 (:REWRITE ACL2-NUMBERP-X))
 (244 61 (:REWRITE RATIONALP-X))
 (172 5 (:REWRITE RTL::BITS-TAIL-GEN))
 (170 62 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (94 94 (:TYPE-PRESCRIPTION BOOLEANP))
 (90 62 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (62 62
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (62 62 (:REWRITE REDUCE-INTEGERP-+))
 (62 62
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (62 62 (:REWRITE INTEGERP-MINUS-X))
 (62 62
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (62 62 (:REWRITE |(equal c (/ x))|))
 (62 62 (:REWRITE |(equal c (- x))|))
 (62 62 (:REWRITE |(equal (/ x) c)|))
 (62 62 (:REWRITE |(equal (/ x) (/ y))|))
 (62 62 (:REWRITE |(equal (- x) c)|))
 (62 62 (:REWRITE |(equal (- x) (- y))|))
 (62 62 (:META META-INTEGERP-CORRECT))
 (61 61 (:REWRITE REDUCE-RATIONALP-+))
 (61 61 (:REWRITE REDUCE-RATIONALP-*))
 (61 61 (:REWRITE RATIONALP-MINUS-X))
 (61 61 (:META META-RATIONALP-CORRECT))
 (32 32
     (:TYPE-PRESCRIPTION RTL::INTEGERP-OPB))
 (15 15 (:REWRITE SUBSETP-MEMBER . 4))
 (15 15 (:REWRITE SUBSETP-MEMBER . 3))
 (15 15 (:REWRITE SUBSETP-MEMBER . 2))
 (15 15 (:REWRITE SUBSETP-MEMBER . 1))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (15 15 (:REWRITE INTERSECTP-MEMBER . 3))
 (15 15 (:REWRITE INTERSECTP-MEMBER . 2))
 (15 5 (:REWRITE RTL::BITS-TAIL))
 (8 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (5 5 (:REWRITE RTL::BITS-NEG-INDICES))
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
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|)))
(RTL::INTEGERP-MANA (67 3 (:REWRITE RTL::OPAZ-OPA))
                    (53 6
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (47 7 (:REWRITE ACL2-NUMBERP-X))
                    (20 5 (:REWRITE RATIONALP-X))
                    (14 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                    (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
                    (6 6
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE REDUCE-INTEGERP-+))
                    (6 6
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (6 6 (:REWRITE INTEGERP-MINUS-X))
                    (6 6
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (6 6 (:REWRITE |(equal c (/ x))|))
                    (6 6 (:REWRITE |(equal c (- x))|))
                    (6 6 (:REWRITE |(equal (/ x) c)|))
                    (6 6 (:REWRITE |(equal (/ x) (/ y))|))
                    (6 6 (:REWRITE |(equal (- x) c)|))
                    (6 6 (:REWRITE |(equal (- x) (- y))|))
                    (6 6 (:META META-INTEGERP-CORRECT))
                    (5 5 (:REWRITE REDUCE-RATIONALP-+))
                    (5 5 (:REWRITE REDUCE-RATIONALP-*))
                    (5 5 (:REWRITE RATIONALP-MINUS-X))
                    (5 5 (:META META-RATIONALP-CORRECT))
                    (4 4
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (4 1 (:REWRITE RTL::BITS-TAIL-GEN))
                    (3 1 (:REWRITE RTL::BITS-TAIL))
                    (2 1
                       (:TYPE-PRESCRIPTION RTL::INTEGERP-MANA))
                    (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
                    (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::INTEGERP-MANB (93 10
                        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                    (83 11 (:REWRITE ACL2-NUMBERP-X))
                    (67 3 (:REWRITE RTL::OPBZ-OPB))
                    (36 9 (:REWRITE RATIONALP-X))
                    (26 10 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                    (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
                    (14 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                    (10 10
                        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                    (10 10 (:REWRITE REDUCE-INTEGERP-+))
                    (10 10
                        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                    (10 10 (:REWRITE INTEGERP-MINUS-X))
                    (10 10
                        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                    (10 10 (:REWRITE |(equal c (/ x))|))
                    (10 10 (:REWRITE |(equal c (- x))|))
                    (10 10 (:REWRITE |(equal (/ x) c)|))
                    (10 10 (:REWRITE |(equal (/ x) (/ y))|))
                    (10 10 (:REWRITE |(equal (- x) c)|))
                    (10 10 (:REWRITE |(equal (- x) (- y))|))
                    (10 10 (:META META-INTEGERP-CORRECT))
                    (9 9 (:REWRITE REDUCE-RATIONALP-+))
                    (9 9 (:REWRITE REDUCE-RATIONALP-*))
                    (9 9 (:REWRITE RATIONALP-MINUS-X))
                    (9 9 (:META META-RATIONALP-CORRECT))
                    (5 5 (:REWRITE SUBSETP-MEMBER . 4))
                    (5 5 (:REWRITE SUBSETP-MEMBER . 3))
                    (5 5 (:REWRITE SUBSETP-MEMBER . 2))
                    (5 5 (:REWRITE SUBSETP-MEMBER . 1))
                    (5 5
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                    (5 5 (:REWRITE INTERSECTP-MEMBER . 3))
                    (5 5 (:REWRITE INTERSECTP-MEMBER . 2))
                    (4 1 (:REWRITE RTL::BITS-TAIL-GEN))
                    (3 1 (:REWRITE RTL::BITS-TAIL))
                    (2 1
                       (:TYPE-PRESCRIPTION RTL::INTEGERP-MANB))
                    (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
                    (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BITN-MULTIPLIER
 (1534 4 (:REWRITE RTL::NEG-BITN-0))
 (900 35
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (206 54
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (204 8 (:REWRITE |(< (+ (- c) x) y)|))
 (202 8 (:REWRITE |(< y (+ (- c) x))|))
 (202 4 (:REWRITE RTL::NEG-BITN-1))
 (156 2 (:REWRITE |(* x (- y))|))
 (130 4 (:LINEAR EXPT-<=-1-TWO))
 (126 4 (:LINEAR EXPT->-1-ONE))
 (119 9
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (118 27 (:REWRITE DEFAULT-TIMES-2))
 (116 4 (:LINEAR EXPT-X->=-X))
 (116 4 (:LINEAR EXPT-X->-X))
 (102 4 (:LINEAR EXPT->=-1-ONE))
 (90 54 (:REWRITE DEFAULT-LESS-THAN-2))
 (70 5 (:REWRITE |(* y (* x z))|))
 (70 4 (:REWRITE RTL::BITN-NEG))
 (70 4 (:LINEAR EXPT-<-1-TWO))
 (69 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (68 8
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (66 54 (:REWRITE DEFAULT-LESS-THAN-1))
 (66 2 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (64 2 (:REWRITE |(* (/ c) (expt d n))|))
 (57
   57
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (57
  57
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (56 33 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (54 54 (:REWRITE THE-FLOOR-BELOW))
 (54 54 (:REWRITE THE-FLOOR-ABOVE))
 (54 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (53 33 (:REWRITE SIMPLIFY-SUMS-<))
 (51 51
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (40 4 (:REWRITE DEFAULT-MINUS))
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
 (34 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (31 27 (:REWRITE DEFAULT-TIMES-1))
 (28 28 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (20 2 (:DEFINITION FIX))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE DEFAULT-PLUS-2))
 (12 12 (:REWRITE DEFAULT-PLUS-1))
 (12 4 (:REWRITE RTL::BVECP-BITN-0))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (10 5 (:REWRITE |(* a (/ a) b)|))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:REWRITE |(* 1 x)|))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::MUX-BMUX4P
 (3756 8 (:REWRITE RTL::BVECP-BITN-0))
 (2040 8 (:REWRITE RTL::NEG-BITN-0))
 (1520 35 (:REWRITE |(< y (+ (- c) x))|))
 (1206 26 (:REWRITE |(< (+ (- c) x) y)|))
 (770 14 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (641 15 (:REWRITE |(< (if a b c) x)|))
 (606 154 (:REWRITE INTEGERP-<-CONSTANT))
 (576 14 (:LINEAR EXPT->-1-ONE))
 (538 14 (:LINEAR EXPT->=-1-ONE))
 (456 14 (:LINEAR EXPT-<=-1-TWO))
 (450 160 (:REWRITE CONSTANT-<-INTEGERP))
 (420 14 (:LINEAR EXPT-X->=-X))
 (420 14 (:LINEAR EXPT-X->-X))
 (381 3 (:REWRITE RTL::BITS-TAIL-GEN))
 (358 220 (:REWRITE DEFAULT-LESS-THAN-1))
 (346 220 (:REWRITE DEFAULT-LESS-THAN-2))
 (332 6 (:REWRITE ODD-EXPT-THM))
 (305 225 (:REWRITE DEFAULT-PLUS-1))
 (296 146
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (296 14 (:LINEAR EXPT-<-1-TWO))
 (292 146
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (290 8 (:REWRITE RTL::BITN-NEG))
 (286 195 (:REWRITE DEFAULT-TIMES-2))
 (285 225 (:REWRITE DEFAULT-PLUS-2))
 (264 8 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (220 220 (:REWRITE THE-FLOOR-BELOW))
 (220 220 (:REWRITE THE-FLOOR-ABOVE))
 (209 195 (:REWRITE DEFAULT-TIMES-1))
 (207 185
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (188 8 (:REWRITE RTL::NEG-BITN-1))
 (182
  182
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (182 182
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (182
     182
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (182 182
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (182 182
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (180 6 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (164 164 (:TYPE-PRESCRIPTION LOGNOT))
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
 (146 146
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (136 4
      (:REWRITE |(<= x (/ y)) with (< 0 y)|))
 (126 28
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (124 4
      (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (112 14 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (100 100
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (95 95
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (88 28
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (74 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (68 13 (:REWRITE DEFAULT-MINUS))
 (57 57
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (54 54 (:REWRITE DEFAULT-EXPT-2))
 (54 54 (:REWRITE DEFAULT-EXPT-1))
 (54 54 (:REWRITE |(expt 1/c n)|))
 (54 54 (:REWRITE |(expt (- x) n)|))
 (50 50 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (49 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (44 18 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (42 37 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (39 11 (:REWRITE DEFAULT-LOGNOT))
 (35 35 (:REWRITE |(< x (+ c/d y))|))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (28 28
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (28 4 (:REWRITE |(expt c (* d n))|))
 (27 27 (:REWRITE |(< (* x y) 0)|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (26 26 (:REWRITE |(< 0 (/ x))|))
 (23 23
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (23 23
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (23 23
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (23 23 (:REWRITE |(equal c (/ x))|))
 (23 23 (:REWRITE |(equal c (- x))|))
 (23 23 (:REWRITE |(equal (/ x) c)|))
 (23 23 (:REWRITE |(equal (/ x) (/ y))|))
 (23 23 (:REWRITE |(equal (- x) c)|))
 (23 23 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (19 19 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE SUBSETP-MEMBER . 4))
 (18 18 (:REWRITE SUBSETP-MEMBER . 3))
 (18 18 (:REWRITE SUBSETP-MEMBER . 2))
 (18 18 (:REWRITE SUBSETP-MEMBER . 1))
 (18 18 (:REWRITE INTERSECTP-MEMBER . 3))
 (18 18 (:REWRITE INTERSECTP-MEMBER . 2))
 (14 14 (:REWRITE RTL::BITS-NEG-INDICES))
 (14 14 (:LINEAR EXPT-LINEAR-UPPER-<))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (14 14 (:LINEAR EXPT->=-1-TWO))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT-<=-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (8 8 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (7 7 (:REWRITE |(* (- x) y)|))
 (6 6 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4
    (:REWRITE |(<= x (/ y)) with (< y 0)|))
 (4 4
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE |(lognot (* 2 x))| . 3))
 (2 2 (:REWRITE |(lognot (* 2 x))| . 2))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::PP-0-REWRITE
 (304 29 (:REWRITE RTL::NEG-BITN-0))
 (137 81 (:REWRITE DEFAULT-LESS-THAN-1))
 (130 3 (:REWRITE |(< (if a b c) x)|))
 (127 78 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (124 78
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (103 103 (:TYPE-PRESCRIPTION RTL::BMUX4P))
 (82 78
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (81 81 (:REWRITE THE-FLOOR-BELOW))
 (81 81 (:REWRITE THE-FLOOR-ABOVE))
 (81 81 (:REWRITE DEFAULT-LESS-THAN-2))
 (80 78
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (78 78 (:REWRITE SIMPLIFY-SUMS-<))
 (78 78
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (78 78
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (78 78
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (78 78 (:REWRITE |(< (/ x) (/ y))|))
 (78 78 (:REWRITE |(< (- x) c)|))
 (78 78 (:REWRITE |(< (- x) (- y))|))
 (62 31 (:REWRITE DEFAULT-PLUS-2))
 (62 20 (:REWRITE RTL::BITS-BITS-SUM-ALT))
 (57
   57
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (57
  57
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (57 57
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (51 51 (:TYPE-PRESCRIPTION RTL::MULTIPLIER))
 (43 43 (:REWRITE RTL::BITS-NEG-INDICES))
 (43 29 (:REWRITE RTL::NEG-BITN-1))
 (39 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (34 31 (:REWRITE DEFAULT-PLUS-1))
 (28 28 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:REWRITE INTEGERP-MINUS-X))
 (28 28 (:META META-INTEGERP-CORRECT))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (22 22 (:REWRITE |(< (/ x) 0)|))
 (22 22 (:REWRITE |(< (+ c/d x) y)|))
 (22 22 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22 (:REWRITE |(< (* x y) 0)|))
 (21 5
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20 20 (:REWRITE RTL::BITN-NEG))
 (14 14
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE NORMALIZE-ADDENDS))
 (12 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (10 2 (:REWRITE ACL2-NUMBERP-X))
 (9 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 5 (:REWRITE DEFAULT-TIMES-2))
 (7 7 (:REWRITE RTL::AG-DIFF-AS))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITN-BVECP))
 (4 1 (:REWRITE RATIONALP-X))
 (1 1 (:REWRITE REDUCE-RATIONALP-+))
 (1 1 (:REWRITE REDUCE-RATIONALP-*))
 (1 1 (:REWRITE RATIONALP-MINUS-X))
 (1 1 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (1 1 (:META META-RATIONALP-CORRECT)))
(RTL::PP-I-REWRITE
 (21280 2108 (:REWRITE RTL::NEG-BITN-0))
 (12508 11266 (:REWRITE DEFAULT-LESS-THAN-1))
 (11388 10146
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11388 10146
        (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11266 11266 (:REWRITE THE-FLOOR-BELOW))
 (11266 11266 (:REWRITE THE-FLOOR-ABOVE))
 (11266 11266 (:REWRITE DEFAULT-LESS-THAN-2))
 (10466 10266
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10266 10266
        (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10266 10266 (:REWRITE INTEGERP-<-CONSTANT))
 (10266 10266 (:REWRITE CONSTANT-<-INTEGERP))
 (10266 10266
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10266 10266
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10266 10266
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10266 10266
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10266 10266 (:REWRITE |(< c (- x))|))
 (10266 10266
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10266 10266
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10266 10266
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10266 10266
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10266 10266 (:REWRITE |(< (/ x) (/ y))|))
 (10266 10266 (:REWRITE |(< (- x) c)|))
 (10266 10266 (:REWRITE |(< (- x) (- y))|))
 (10146 10146 (:REWRITE SIMPLIFY-SUMS-<))
 (8294 4774 (:REWRITE DEFAULT-TIMES-2))
 (5189
  5189
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5189
      5189
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5189
     5189
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5189 5189
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5189 5189
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4942 4192 (:REWRITE DEFAULT-PLUS-2))
 (4774 4774 (:REWRITE DEFAULT-TIMES-1))
 (4192 4192 (:REWRITE DEFAULT-PLUS-1))
 (3920 3920 (:REWRITE RTL::BITS-NEG-INDICES))
 (2723 1339
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2523 1339
       (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (2392 2392 (:REWRITE |(< (+ c/d x) y)|))
 (2392 2392 (:REWRITE |(< (+ (- c) x) y)|))
 (2390 2390
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2308 2108 (:REWRITE RTL::NEG-BITN-1))
 (2192 2192
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2192 2192 (:REWRITE NORMALIZE-ADDENDS))
 (1908 1908 (:REWRITE RTL::BITN-NEG))
 (1689 1339 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1563 1563 (:REWRITE |(< (/ x) 0)|))
 (1563 1563 (:REWRITE |(< (* x y) 0)|))
 (1531 1339
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1443 1443
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1443 1443
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1339 1339
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1339 1339
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1339 1339 (:REWRITE |(equal c (/ x))|))
 (1339 1339 (:REWRITE |(equal c (- x))|))
 (1339 1339 (:REWRITE |(equal (/ x) c)|))
 (1339 1339 (:REWRITE |(equal (/ x) (/ y))|))
 (1339 1339 (:REWRITE |(equal (- x) c)|))
 (1339 1339 (:REWRITE |(equal (- x) (- y))|))
 (830 830
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (830 830
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (830 830
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (830 830
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (600 600 (:REWRITE RTL::AG-DIFF-AS))
 (558 558
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (400 400 (:REWRITE REDUCE-INTEGERP-+))
 (400 400 (:REWRITE INTEGERP-MINUS-X))
 (400 400 (:META META-INTEGERP-CORRECT))
 (400 350 (:REWRITE RTL::BITS-BITS-SUM-ALT))
 (200 200 (:REWRITE |(equal (+ (- c) x) y)|))
 (200 200
      (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (100 100 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (33 33 (:REWRITE SUBSETP-MEMBER . 4))
 (33 33 (:REWRITE SUBSETP-MEMBER . 3))
 (33 33 (:REWRITE SUBSETP-MEMBER . 2))
 (33 33 (:REWRITE SUBSETP-MEMBER . 1))
 (33 33 (:REWRITE INTERSECTP-MEMBER . 3))
 (33 33 (:REWRITE INTERSECTP-MEMBER . 2)))
(RTL::PP-26-REWRITE
 (951 34 (:REWRITE RTL::BITS-TAIL-GEN))
 (182 18 (:REWRITE RTL::NEG-BITN-0))
 (110 98 (:REWRITE DEFAULT-LESS-THAN-1))
 (102 90
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (102 90 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (98 98 (:REWRITE THE-FLOOR-BELOW))
 (98 98 (:REWRITE THE-FLOOR-ABOVE))
 (98 98 (:REWRITE DEFAULT-LESS-THAN-2))
 (90 90 (:REWRITE SIMPLIFY-SUMS-<))
 (90 90
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (90 90
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (90 90 (:REWRITE INTEGERP-<-CONSTANT))
 (90 90 (:REWRITE CONSTANT-<-INTEGERP))
 (90 90
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (90 90
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (90 90
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (90 90
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (90 90 (:REWRITE |(< c (- x))|))
 (90 90
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (90 90
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (90 90
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (90 90
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (90 90 (:REWRITE |(< (/ x) (/ y))|))
 (90 90 (:REWRITE |(< (- x) c)|))
 (90 90 (:REWRITE |(< (- x) (- y))|))
 (77
   77
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (77
  77
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (68 42 (:REWRITE DEFAULT-TIMES-2))
 (63 52 (:REWRITE DEFAULT-PLUS-2))
 (52 52 (:REWRITE DEFAULT-PLUS-1))
 (42 42 (:REWRITE DEFAULT-TIMES-1))
 (38 38 (:REWRITE RTL::BITS-NEG-INDICES))
 (34 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (24 24 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 18 (:REWRITE RTL::NEG-BITN-1))
 (13 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (10 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8 (:REWRITE RTL::BITN-NEG))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (6 6 (:REWRITE RTL::AG-DIFF-AS))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5 (:REWRITE RTL::BITS-BITS-SUM-ALT))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE RTL::BITS-BVECP-SIMPLE)))
(RTL::SUM-PPROD
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(RTL::INTEGERP-PPROD
 (4230 165 (:REWRITE RTL::BITS-TAIL-GEN))
 (2124 177 (:REWRITE RTL::NEG-BITN-0))
 (1542 36 (:REWRITE |(< (if a b c) x)|))
 (1072 352 (:REWRITE SIMPLIFY-SUMS-<))
 (877 352
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (853 352
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (790 388 (:REWRITE DEFAULT-LESS-THAN-1))
 (765 765
      (:TYPE-PRESCRIPTION RTL::MULTIPLIER))
 (603 405 (:REWRITE DEFAULT-PLUS-2))
 (577 388 (:REWRITE DEFAULT-LESS-THAN-2))
 (566 333
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MANA))
 (564 405 (:REWRITE DEFAULT-PLUS-1))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (543
   543
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (543
  543
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (543
     543
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (543 543
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (537 21 (:LINEAR EXPT-X->-X))
 (531 177 (:REWRITE RTL::NEG-BITN-1))
 (495 21 (:LINEAR EXPT->-1-ONE))
 (417 21 (:LINEAR EXPT-X->=-X))
 (388 388 (:REWRITE THE-FLOOR-BELOW))
 (388 388 (:REWRITE THE-FLOOR-ABOVE))
 (356 178
      (:TYPE-PRESCRIPTION RTL::INTEGERP-MANB))
 (352 352
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (352 352
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (352 352
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (352 352 (:REWRITE INTEGERP-<-CONSTANT))
 (352 352 (:REWRITE CONSTANT-<-INTEGERP))
 (352 352
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (352 352
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (352 352
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (352 352
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (352 352 (:REWRITE |(< c (- x))|))
 (352 352
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (352 352
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (352 352
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (352 352
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (352 352 (:REWRITE |(< (/ x) (/ y))|))
 (352 352 (:REWRITE |(< (- x) c)|))
 (352 352 (:REWRITE |(< (- x) (- y))|))
 (336 21 (:LINEAR EXPT->=-1-ONE))
 (306 228 (:REWRITE DEFAULT-TIMES-2))
 (258 42
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (240 240
      (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (237 21 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (234 234 (:REWRITE RTL::BITS-NEG-INDICES))
 (228 228 (:REWRITE DEFAULT-TIMES-1))
 (216 21 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (177 42
      (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (171 171
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (162 162 (:REWRITE |(< (+ c/d x) y)|))
 (162 162 (:REWRITE |(< (+ (- c) x) y)|))
 (141 141
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (129 129 (:REWRITE DEFAULT-EXPT-2))
 (129 129 (:REWRITE DEFAULT-EXPT-1))
 (129 129 (:REWRITE |(expt 1/c n)|))
 (129 129 (:REWRITE |(expt (- x) n)|))
 (126 108 (:REWRITE RTL::BITN-MULTIPLIER))
 (120 120 (:REWRITE RTL::BITN-NEG))
 (108 21 (:LINEAR EXPT-<=-1-TWO))
 (80 80 (:REWRITE REDUCE-INTEGERP-+))
 (80 80 (:REWRITE INTEGERP-MINUS-X))
 (80 80 (:META META-INTEGERP-CORRECT))
 (76 76 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (63 9 (:REWRITE |(expt c (* d n))|))
 (57 15 (:REWRITE RTL::BITS-BITS-SUM))
 (48 30
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (48 30 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (45 45 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (44 44
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (44 44 (:REWRITE |(< (/ x) 0)|))
 (44 44 (:REWRITE |(< (* x y) 0)|))
 (42 42 (:REWRITE RTL::AG-DIFF-AS))
 (42 42
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (42 42
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 24 (:REWRITE RTL::MUX-BMUX4P))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (30 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (30 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (30 30
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (30 30
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (30 30 (:REWRITE |(equal c (/ x))|))
 (30 30 (:REWRITE |(equal c (- x))|))
 (30 30 (:REWRITE |(equal (/ x) c)|))
 (30 30 (:REWRITE |(equal (/ x) (/ y))|))
 (30 30 (:REWRITE |(equal (- x) c)|))
 (30 30 (:REWRITE |(equal (- x) (- y))|))
 (24 12 (:REWRITE ODD-EXPT-THM))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-TWO))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (19 9 (:REWRITE RTL::INTEGERP-MANA))
 (15 15 (:REWRITE DEFAULT-MINUS))
 (15 15 (:REWRITE |(* (- x) y)|))
 (15 5 (:REWRITE RTL::INTEGERP-MANB))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE |(+ c (+ d x))|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (3 3 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-PPROD))
 (1 1 (:TYPE-PRESCRIPTION NATP)))
(RTL::INTEGERP-SUM-PPROD
 (50 4 (:REWRITE ACL2-NUMBERP-X))
 (43 14 (:REWRITE DEFAULT-PLUS-1))
 (27 8 (:REWRITE DEFAULT-TIMES-1))
 (24 4 (:REWRITE RATIONALP-X))
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
 (10 10
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
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
 (4 4 (:REWRITE REDUCE-RATIONALP-+))
 (4 4 (:REWRITE REDUCE-RATIONALP-*))
 (4 4 (:REWRITE RATIONALP-MINUS-X))
 (4 4 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (4 4 (:META META-RATIONALP-CORRECT))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE RTL::INTEGERP-PPROD))
 (2 2 (:REWRITE DEFAULT-EXPT-2))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 1
    (:TYPE-PRESCRIPTION RTL::INTEGERP-SUM-PPROD))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(RTL::SUM-PP-PPROD
 (428 198 (:REWRITE DEFAULT-PLUS-1))
 (304 22 (:REWRITE ACL2-NUMBERP-X))
 (231 65 (:REWRITE DEFAULT-TIMES-1))
 (176 22 (:REWRITE RATIONALP-X))
 (150
  150
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (150 150
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (150
     150
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (150 150
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (150 150
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (146 36
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (129 129
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (60 3 (:REWRITE |(+ (+ x y) z)|))
 (54 54
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (51 35 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (50 2 (:REWRITE |(< (+ (- c) x) y)|))
 (48 48 (:REWRITE THE-FLOOR-BELOW))
 (48 48 (:REWRITE THE-FLOOR-ABOVE))
 (48 48
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (48 48
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (48 48 (:REWRITE DEFAULT-LESS-THAN-2))
 (48 48 (:REWRITE DEFAULT-LESS-THAN-1))
 (38 38 (:REWRITE SIMPLIFY-SUMS-<))
 (38 38
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 38
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (38 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (38 38 (:REWRITE INTEGERP-<-CONSTANT))
 (38 38 (:REWRITE CONSTANT-<-INTEGERP))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< c (- x))|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (38 38
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (38 38 (:REWRITE |(< (/ x) (/ y))|))
 (38 38 (:REWRITE |(< (- x) c)|))
 (38 38 (:REWRITE |(< (- x) (- y))|))
 (37 37
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (36 36
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (36 36 (:REWRITE |(equal c (/ x))|))
 (36 36 (:REWRITE |(equal c (- x))|))
 (36 36 (:REWRITE |(equal (/ x) c)|))
 (36 36 (:REWRITE |(equal (/ x) (/ y))|))
 (36 36 (:REWRITE |(equal (- x) c)|))
 (36 36 (:REWRITE |(equal (- x) (- y))|))
 (31 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (28 12 (:REWRITE RTL::INTEGERP-PPROD))
 (26 26 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (26 10 (:REWRITE RTL::INTEGERP-SUM-PPROD))
 (15 15 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (13 13 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE DEFAULT-EXPT-1))
 (13 13 (:REWRITE |(expt 1/c n)|))
 (13 13 (:REWRITE |(expt (- x) n)|))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:META META-RATIONALP-CORRECT))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE |(< (+ c/d x) y)|)))
(RTL::SUM-PP-PPROD-27
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::SUM-PPROD-REWRITE
 (32 2 (:DEFINITION RTL::SUM-PPROD))
 (17 10 (:REWRITE DEFAULT-PLUS-2))
 (16 10 (:REWRITE DEFAULT-PLUS-1))
 (10 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (6 6
    (:TYPE-PRESCRIPTION RTL::INTEGERP-PPROD))
 (6 4 (:REWRITE DEFAULT-TIMES-2))
 (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
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
 (5 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
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
 (2 2 (:TYPE-PRESCRIPTION RTL::PP4P)))
(RTL::SA
 (18 9
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MANA))
 (9 9 (:TYPE-PRESCRIPTION RTL::SPECIALP))
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::SB
 (18 9
     (:TYPE-PRESCRIPTION RTL::INTEGERP-MANB))
 (9 9 (:TYPE-PRESCRIPTION RTL::SPECIALP))
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
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(RTL::SUM-PPROD-IA-IB
 (130 20
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (120 3 (:REWRITE |(< (if a b c) x)|))
 (108 12 (:REWRITE ACL2-NUMBERP-X))
 (90 73 (:REWRITE DEFAULT-PLUS-2))
 (73 73 (:REWRITE DEFAULT-PLUS-1))
 (52 45 (:REWRITE DEFAULT-TIMES-2))
 (48 12 (:REWRITE RATIONALP-X))
 (46 20 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (45 45 (:REWRITE DEFAULT-TIMES-1))
 (41 41
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (41 41 (:REWRITE NORMALIZE-ADDENDS))
 (34 28 (:REWRITE DEFAULT-LESS-THAN-1))
 (30 30
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (30 24
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (30 24 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (28 28 (:REWRITE THE-FLOOR-BELOW))
 (28 28 (:REWRITE THE-FLOOR-ABOVE))
 (28 28 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25 (:REWRITE CONSTANT-<-INTEGERP))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) c)|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (24 24 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 24 (:REWRITE SIMPLIFY-SUMS-<))
 (22 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (22 2 (:REWRITE RTL::BVECP-BITN-0))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (20 2 (:REWRITE RTL::NEG-BITN-0))
 (19 19
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (19 19 (:REWRITE FOLD-CONSTS-IN-+))
 (16
   16
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (16
  16
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (16 16
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-RATIONALP-CORRECT))
 (12 12 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE RTL::NEG-BITN-1)))
(RTL::T2PP0S)
(RTL::T1PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP1S)
(RTL::T1PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP2S)
(RTL::T1PP2C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP3S)
(RTL::T1PP3C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP4S)
(RTL::T1PP4C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP5S)
(RTL::T1PP5C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP6S)
(RTL::T1PP6C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP7S)
(RTL::T1PP7C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T2PP8S)
(RTL::T1PP8C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T3PP0S)
(RTL::T2PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T3PP1S)
(RTL::T2PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T3PP2S)
(RTL::T2PP2C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T4PP0S)
(RTL::T3PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T4PP1S)
(RTL::T3PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T4PP2S)
(RTL::T3PP2C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T4PP3S)
(RTL::T3PP3C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T5PP0S)
(RTL::T4PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T5PP1S)
(RTL::T4PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T4PP4S)
(RTL::T4PP2C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T6PP0S)
(RTL::T5PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
             (4 4
                (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2)))
(RTL::T6PP1S)
(RTL::T5PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T7PP0S)
(RTL::T6PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T6PP2S)
(RTL::T6PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T8PP0S)
(RTL::T7PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T9PP0S)
(RTL::T7PP1C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::T9PP1S)
(RTL::T9PP0C (14 14
                 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
             (9 9
                (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::PPA*)
(RTL::PPB* (8 8
              (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
           (3 3
              (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
           (3 3
              (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
           (3 3
              (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1)))
(RTL::COMPRESS-LEMMA)
(RTL::COMP-1
 (14676 1244 (:REWRITE DEFAULT-PLUS-2))
 (2835 1244 (:REWRITE DEFAULT-PLUS-1))
 (665 665
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (665 665 (:REWRITE NORMALIZE-ADDENDS))
 (621 621 (:REWRITE FOLD-CONSTS-IN-+))
 (621 621 (:REWRITE |(+ c (+ d x))|))
 (114 114
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (83
   83
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (83
  83
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (83 83
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (54 6 (:REWRITE ACL2-NUMBERP-X))
 (30 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (30 1
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (30 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 6 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE REDUCE-RATIONALP-+))
 (6 6 (:REWRITE REDUCE-RATIONALP-*))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE RATIONALP-MINUS-X))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-RATIONALP-CORRECT))
 (6 6 (:META META-INTEGERP-CORRECT))
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
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::BVECP-PPROD
 (580 49 (:REWRITE RTL::NEG-BITN-0))
 (139 49 (:REWRITE RTL::NEG-BITN-1))
 (110 49 (:REWRITE RTL::BVECP-BITN-0))
 (53
   53
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (53
  53
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (53 53
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (53 53
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (53 53
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (53 53
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (45 15 (:REWRITE RTL::BITS-TAIL-GEN))
 (35 15 (:REWRITE RTL::BITS-TAIL))
 (33 33 (:REWRITE RTL::BITN-NEG))
 (32 18 (:REWRITE RTL::BITN-BVECP-1))
 (18 6 (:REWRITE RTL::MUX-BMUX4P))
 (16 10
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (16 10 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (15 15 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (15 15 (:REWRITE RTL::BITS-NEG-INDICES))
 (14 14 (:REWRITE RTL::AG-DIFF-AS))
 (13 13 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:REWRITE INTEGERP-MINUS-X))
 (13 13 (:META META-INTEGERP-CORRECT))
 (12 12 (:TYPE-PRESCRIPTION RTL::SPECIALP))
 (11 11 (:REWRITE RTL::BITN-BVECP))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
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
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|)))
(RTL::BVECP-PPROD-26
 (216 18 (:REWRITE RTL::NEG-BITN-0))
 (54 18 (:REWRITE RTL::NEG-BITN-1))
 (50 18 (:REWRITE RTL::BVECP-BITN-0))
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
 (17 9 (:REWRITE RTL::BITN-BVECP-1))
 (15 15 (:REWRITE RTL::BITN-NEG))
 (12 12
     (:TYPE-PRESCRIPTION RTL::BITS-NONNEGATIVE-INTEGERP-TYPE))
 (12 12 (:REWRITE RTL::BITS-NEG-INDICES))
 (9 3 (:REWRITE RTL::MUX-BMUX4P))
 (8 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (7 7 (:REWRITE RTL::AG-DIFF-AS))
 (6 6 (:TYPE-PRESCRIPTION RTL::SPECIALP))
 (6 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
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
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE RTL::BITS-BVECP-SIMPLE))
 (3 3 (:REWRITE RTL::BITS-BVECP))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|)))
(RTL::INTEGERP-SA (10 1
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (9 1 (:REWRITE ACL2-NUMBERP-X))
                  (4 1 (:REWRITE RATIONALP-X))
                  (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                  (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
                  (2 1 (:TYPE-PRESCRIPTION RTL::INTEGERP-SA))
                  (2 1 (:REWRITE DEFAULT-PLUS-2))
                  (1 1
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (1 1 (:REWRITE NORMALIZE-ADDENDS))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE DEFAULT-PLUS-1))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|))
                  (1 1 (:META META-RATIONALP-CORRECT))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::INTEGERP-SB (10 1
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                  (9 1 (:REWRITE ACL2-NUMBERP-X))
                  (4 1 (:REWRITE RATIONALP-X))
                  (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
                  (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
                  (2 1 (:TYPE-PRESCRIPTION RTL::INTEGERP-SB))
                  (2 1 (:REWRITE DEFAULT-PLUS-2))
                  (1 1
                     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
                  (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                  (1 1 (:REWRITE REDUCE-RATIONALP-+))
                  (1 1 (:REWRITE REDUCE-RATIONALP-*))
                  (1 1
                     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE REDUCE-INTEGERP-+))
                  (1 1
                     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                  (1 1 (:REWRITE RATIONALP-MINUS-X))
                  (1 1
                     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                  (1 1 (:REWRITE NORMALIZE-ADDENDS))
                  (1 1 (:REWRITE INTEGERP-MINUS-X))
                  (1 1
                     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                  (1 1 (:REWRITE DEFAULT-PLUS-1))
                  (1 1 (:REWRITE |(equal c (/ x))|))
                  (1 1 (:REWRITE |(equal c (- x))|))
                  (1 1 (:REWRITE |(equal (/ x) c)|))
                  (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                  (1 1 (:REWRITE |(equal (- x) c)|))
                  (1 1 (:REWRITE |(equal (- x) (- y))|))
                  (1 1 (:META META-RATIONALP-CORRECT))
                  (1 1 (:META META-INTEGERP-CORRECT)))
(RTL::BVECP-T2PP0S
 (54 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (23 11 (:REWRITE DEFAULT-TIMES-2))
 (17 14 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 14 (:REWRITE THE-FLOOR-BELOW))
 (14 14 (:REWRITE THE-FLOOR-ABOVE))
 (14 14 (:REWRITE DEFAULT-LESS-THAN-2))
 (14 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (14 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (11 11
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 11 (:REWRITE INTEGERP-<-CONSTANT))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
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
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES)))
(RTL::BVECP-T1PP0C
 (55 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (25 13 (:REWRITE DEFAULT-TIMES-2))
 (18 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (15 12
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 13 (:REWRITE DEFAULT-TIMES-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 12 (:REWRITE SIMPLIFY-SUMS-<))
 (12 12
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (12 12
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP1S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP1C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP2S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP2C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP3S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP3C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP4S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP4C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP5S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP5C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP6S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP6C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP7S
 (39 19 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 19 (:REWRITE DEFAULT-TIMES-1))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (16 13 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 13
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 13 (:REWRITE SIMPLIFY-SUMS-<))
 (13 13
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T1PP7C
 (50 26 (:REWRITE DEFAULT-TIMES-2))
 (26 26 (:REWRITE DEFAULT-TIMES-1))
 (25 22 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 22 (:REWRITE THE-FLOOR-BELOW))
 (22 22 (:REWRITE THE-FLOOR-ABOVE))
 (22 22 (:REWRITE DEFAULT-LESS-THAN-2))
 (19 16
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 16 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16 (:REWRITE SIMPLIFY-SUMS-<))
 (16 16
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (16 16 (:REWRITE INTEGERP-<-CONSTANT))
 (16 16 (:REWRITE CONSTANT-<-INTEGERP))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) c)|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T2PP8S
 (18 10 (:REWRITE DEFAULT-TIMES-2))
 (16 13 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 11
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (14 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 13 (:REWRITE THE-FLOOR-BELOW))
 (13 13 (:REWRITE THE-FLOOR-ABOVE))
 (13 13 (:REWRITE DEFAULT-LESS-THAN-2))
 (13 11
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 11 (:REWRITE SIMPLIFY-SUMS-<))
 (11 11
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR)))
(RTL::BVECP-T1PP8C
 (29 17 (:REWRITE DEFAULT-TIMES-2))
 (21 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (19 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (18 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (17 17 (:REWRITE DEFAULT-TIMES-1))
 (15 15 (:REWRITE SIMPLIFY-SUMS-<))
 (15 15
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< c (- x))|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:REWRITE |(< (- x) c)|))
 (15 15 (:REWRITE |(< (- x) (- y))|))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T3PP0S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T2PP0C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T3PP1S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T2PP1C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T3PP2S
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 8
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR)))
(RTL::BVECP-T2PP2C
 (16 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T4PP0S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T3PP0C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T4PP1S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T3PP1C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T4PP2S
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 8
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR)))
(RTL::BVECP-T3PP2C
 (16 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T4PP3S
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 8
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR)))
(RTL::BVECP-T3PP3C
 (16 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T5PP0S
 (41 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 1 (:REWRITE |(* c (* d x))|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* 1 x)|)))
(RTL::BVECP-T4PP0C
 (43 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 1 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* 1 x)|)))
(RTL::BVECP-T5PP1S
 (41 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (6 6 (:REWRITE DEFAULT-TIMES-2))
 (6 6 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 1 (:REWRITE |(* c (* d x))|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* 1 x)|)))
(RTL::BVECP-T4PP1C
 (43 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 1 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* 1 x)|)))
(RTL::BVECP-IA (26 2 (:REWRITE RTL::BITS-TAIL-GEN))
               (21 3
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (18 2 (:REWRITE ACL2-NUMBERP-X))
               (12 6
                   (:TYPE-PRESCRIPTION RTL::INTEGERP-MANB))
               (8 2 (:REWRITE RATIONALP-X))
               (7 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
               (6 2 (:REWRITE RTL::INTEGERP-MANB))
               (6 2 (:REWRITE RTL::BITS-TAIL))
               (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
               (4 4 (:REWRITE REDUCE-INTEGERP-+))
               (4 4 (:REWRITE INTEGERP-MINUS-X))
               (4 4 (:META META-INTEGERP-CORRECT))
               (3 3
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
               (2 2 (:REWRITE REDUCE-RATIONALP-+))
               (2 2 (:REWRITE REDUCE-RATIONALP-*))
               (2 2 (:REWRITE RATIONALP-MINUS-X))
               (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
               (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
               (2 2 (:META META-RATIONALP-CORRECT)))
(RTL::BVECP-IB
 (95 14
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (81 9 (:REWRITE ACL2-NUMBERP-X))
 (36 9 (:REWRITE RATIONALP-X))
 (32 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (32 3 (:REWRITE RTL::NEG-BITN-0))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (15 3 (:REWRITE RTL::BITS-TAIL-GEN))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
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
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE REDUCE-RATIONALP-+))
 (9 9 (:REWRITE REDUCE-RATIONALP-*))
 (9 9 (:REWRITE RATIONALP-MINUS-X))
 (9 9 (:META META-RATIONALP-CORRECT))
 (8 3 (:REWRITE RTL::BVECP-BITN-0))
 (7 3 (:REWRITE RTL::BITS-TAIL))
 (6 3
    (:TYPE-PRESCRIPTION RTL::INTEGERP-MANA))
 (5 3 (:REWRITE RTL::NEG-BITN-1))
 (4 4
    (:TYPE-PRESCRIPTION RTL::BITN-NONNEGATIVE-INTEGER))
 (4 2 (:REWRITE RTL::BITN-BVECP-1))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (3 3 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 1 (:REWRITE RTL::INTEGERP-MANA))
 (2 2 (:REWRITE RTL::BITN-NEG))
 (1 1 (:REWRITE RTL::BITN-BVECP)))
(RTL::BVECP-T4PP4S
 (15 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (15 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 8
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (9 5 (:REWRITE DEFAULT-LOGXOR-2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
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
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (8 8
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (8 8 (:REWRITE |(< (/ x) (/ y))|))
 (8 8 (:REWRITE |(< (- x) c)|))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (8 5 (:REWRITE DEFAULT-LOGXOR-1))
 (6 4 (:REWRITE DEFAULT-TIMES-2))
 (6 4 (:REWRITE DEFAULT-TIMES-1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T4PP2C
 (38 5 (:REWRITE DEFAULT-LOGIOR-2))
 (28 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (22 5 (:REWRITE DEFAULT-LOGIOR-1))
 (19 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (17 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 2
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (14 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (12 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (12 8 (:REWRITE DEFAULT-TIMES-2))
 (12 8 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
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
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 5 (:REWRITE DEFAULT-LOGAND-2))
 (8 5 (:REWRITE DEFAULT-LOGAND-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE LOGAND-CONSTANT-MASK))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (2 2
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2 2 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T6PP0S
 (54 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 5 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 6 (:REWRITE DEFAULT-LOGXOR-2))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE DEFAULT-LOGXOR-1))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T5PP0C
 (55 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 6 (:REWRITE DEFAULT-LOGIOR-2))
 (18 6 (:REWRITE DEFAULT-LOGIOR-1))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 2
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE LOGAND-CONSTANT-MASK))
 (6 6 (:REWRITE DEFAULT-LOGAND-2))
 (6 6 (:REWRITE DEFAULT-LOGAND-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (2 2
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE |(logior c d x)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T6PP1S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (6 4 (:REWRITE DEFAULT-LOGXOR-2))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE DEFAULT-LOGXOR-1))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T5PP1C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 3 (:REWRITE DEFAULT-LOGIOR-2))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
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
 (9 3 (:REWRITE DEFAULT-LOGIOR-1))
 (7 7
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (7 7
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE LOGAND-CONSTANT-MASK))
 (4 4 (:REWRITE DEFAULT-LOGAND-2))
 (4 4 (:REWRITE DEFAULT-LOGAND-1))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T7PP0S
 (54 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 5 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (3 2 (:REWRITE DEFAULT-LOGXOR-2))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-LOGXOR-1))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T6PP0C
 (55 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 2 (:REWRITE DEFAULT-LOGIOR-2))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 2 (:REWRITE DEFAULT-LOGIOR-1))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (5 5
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE LOGAND-CONSTANT-MASK))
 (3 3 (:REWRITE DEFAULT-LOGAND-2))
 (3 3 (:REWRITE DEFAULT-LOGAND-1))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T6PP2S
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 8
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (8 6 (:REWRITE DEFAULT-LOGXOR-2))
 (6 6 (:REWRITE DEFAULT-LOGXOR-1))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
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
 (4 4 (:TYPE-PRESCRIPTION ABS))
 (4 4 (:REWRITE DEFAULT-TIMES-2))
 (4 4 (:REWRITE DEFAULT-TIMES-1))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(RTL::BVECP-T6PP1C
 (32 6 (:REWRITE DEFAULT-LOGIOR-2))
 (18 6 (:REWRITE DEFAULT-LOGIOR-1))
 (16 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (14 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (14 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
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
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (10 2
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (8
   8
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (8
  8
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (8 8
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE DEFAULT-TIMES-1))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE LOGAND-CONSTANT-MASK))
 (6 6 (:REWRITE DEFAULT-LOGAND-2))
 (6 6 (:REWRITE DEFAULT-LOGAND-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 4
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (2 2
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2 2 (:REWRITE |(logior c d x)|)))
(RTL::BVECP-T8PP0S
 (108 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (86 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (22 2 (:REWRITE |(* y (* x z))|))
 (18 10 (:REWRITE DEFAULT-TIMES-2))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (7 5 (:REWRITE DEFAULT-LOGXOR-2))
 (5 5 (:REWRITE DEFAULT-LOGXOR-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T7PP0C
 (110 4 (:REWRITE RTL::BITS-TAIL-GEN))
 (86 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (29 5 (:REWRITE DEFAULT-LOGIOR-2))
 (22 14 (:REWRITE DEFAULT-TIMES-2))
 (22 2 (:REWRITE |(* y (* x z))|))
 (15 5 (:REWRITE DEFAULT-LOGIOR-1))
 (14 14 (:REWRITE DEFAULT-TIMES-1))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 2
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE LOGAND-CONSTANT-MASK))
 (5 5 (:REWRITE DEFAULT-LOGAND-2))
 (5 5 (:REWRITE DEFAULT-LOGAND-1))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2
   2
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2 2 (:REWRITE |(logior c d x)|))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T9PP0S
 (54 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 5 (:REWRITE DEFAULT-TIMES-2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 4 (:REWRITE DEFAULT-LOGXOR-2))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4 (:REWRITE DEFAULT-LOGXOR-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T7PP1C
 (55 2 (:REWRITE RTL::BITS-TAIL-GEN))
 (46 8
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 3 (:REWRITE DEFAULT-LOGIOR-2))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 7
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (10 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (9 3 (:REWRITE DEFAULT-LOGIOR-1))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (7 7
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (7 7
    (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE INTEGERP-<-CONSTANT))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (7 7 (:REWRITE CONSTANT-<-INTEGERP))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< c (- x))|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (7 7
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (7 7 (:REWRITE |(< (/ x) (/ y))|))
 (7 7 (:REWRITE |(< (- x) c)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (5 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
 (4 4 (:REWRITE LOGAND-CONSTANT-MASK))
 (4 4 (:REWRITE DEFAULT-LOGAND-2))
 (4 4 (:REWRITE DEFAULT-LOGAND-1))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1 1
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1 1 (:REWRITE |(logior c d x)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T9PP1S
 (48 9
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (13 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 9 (:REWRITE DEFAULT-LESS-THAN-1))
 (11 8
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 7 (:REWRITE DEFAULT-TIMES-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE THE-FLOOR-BELOW))
 (9 9 (:REWRITE THE-FLOOR-ABOVE))
 (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
 (9 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (8 8 (:REWRITE INTEGERP-<-CONSTANT))
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
 (8 6 (:REWRITE DEFAULT-LOGXOR-2))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (6 6 (:REWRITE DEFAULT-LOGXOR-1))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3
   3
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3
  3
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGXOR))
 (2 2 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (2 2 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::BVECP-T9PP0C
 (50 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 6 (:REWRITE DEFAULT-LOGIOR-2))
 (18 6 (:REWRITE DEFAULT-LOGIOR-1))
 (15 11 (:REWRITE DEFAULT-TIMES-2))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 3))
 (14 14
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (14 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (12 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 11 (:REWRITE DEFAULT-TIMES-1))
 (11 9
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 2
     (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 2))
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
 (6 6 (:REWRITE LOGAND-CONSTANT-MASK))
 (6 6 (:REWRITE DEFAULT-LOGAND-2))
 (6 6 (:REWRITE DEFAULT-LOGAND-1))
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
 (5 5 (:TYPE-PRESCRIPTION ABS))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (4 4 (:REWRITE RTL::BITS-NEG-INDICES))
 (2 2 (:TYPE-PRESCRIPTION BINARY-LOGIOR))
 (2 2
    (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2 2
    (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (2 2 (:REWRITE |(logior c d x)|))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T0
 (19383 19383
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (17510 396 (:REWRITE DEFAULT-PLUS-2))
 (11836 11836
        (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (11836 11836
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (11836 11836
        (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (4266 54 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1700 396 (:REWRITE DEFAULT-PLUS-1))
 (1450 602 (:REWRITE DEFAULT-TIMES-2))
 (1053 153 (:REWRITE DEFAULT-LOGIOR-2))
 (646 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (646 22
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (621 54 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (621 54 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (606 602 (:REWRITE DEFAULT-TIMES-1))
 (540 54 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (495 153 (:REWRITE DEFAULT-LOGIOR-1))
 (441 306 (:REWRITE DEFAULT-LESS-THAN-2))
 (435 246
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (435 246
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (431 431
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (360 306 (:REWRITE DEFAULT-LESS-THAN-1))
 (315 315 (:REWRITE THE-FLOOR-BELOW))
 (315 315 (:REWRITE THE-FLOOR-ABOVE))
 (274 274
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (274 274 (:REWRITE NORMALIZE-ADDENDS))
 (270 246
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (270 216 (:REWRITE DEFAULT-LOGAND-2))
 (246 246 (:REWRITE SIMPLIFY-SUMS-<))
 (246 246
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (246 246 (:REWRITE INTEGERP-<-CONSTANT))
 (246 246 (:REWRITE CONSTANT-<-INTEGERP))
 (246 246
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (246 246
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (246 246
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (246 246
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (246 246 (:REWRITE |(< c (- x))|))
 (246 246
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (246 246
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (246 246
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (246 246
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (246 246 (:REWRITE |(< (/ x) (/ y))|))
 (246 246 (:REWRITE |(< (- x) c)|))
 (246 246 (:REWRITE |(< (- x) (- y))|))
 (223 223 (:REWRITE FOLD-CONSTS-IN-+))
 (223 223 (:REWRITE |(+ c (+ d x))|))
 (216 216 (:REWRITE LOGAND-CONSTANT-MASK))
 (216 216 (:REWRITE DEFAULT-LOGAND-1))
 (186 132 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (156
   156
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (156
  156
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (156 156
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (156
     156
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (156 156
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (156 156
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (108 72 (:REWRITE DEFAULT-LOGXOR-2))
 (81 54 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (81 54 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (78 78
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (78 78 (:REWRITE |(< (/ x) 0)|))
 (78 78 (:REWRITE |(< (* x y) 0)|))
 (72 72 (:REWRITE DEFAULT-LOGXOR-1))
 (72 72 (:REWRITE |(logior c d x)|))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (60 60 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (54 54
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (54 54 (:REWRITE |(< 0 (/ x))|))
 (54 54 (:REWRITE |(< 0 (* x y))|))
 (51 51 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (51 51 (:REWRITE RTL::BITS-NEG-INDICES))
 (26 22 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 24
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
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
 (22 22 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::COMP-T1
 (5350 185 (:REWRITE DEFAULT-PLUS-2))
 (3497 3497
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1877 1877
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1877 1877
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1877 1877
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (1870 23 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (923 185 (:REWRITE DEFAULT-PLUS-1))
 (334 48 (:REWRITE DEFAULT-LOGIOR-2))
 (282 23 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (270 23 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (247 114 (:REWRITE DEFAULT-TIMES-2))
 (240 23 (:LINEAR LOGAND-BOUNDS-POS . 1))
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
 (165 48 (:REWRITE DEFAULT-LOGIOR-1))
 (145 57
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (131 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (131 5
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (124 55
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (124 55 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (117 57 (:REWRITE DEFAULT-LESS-THAN-2))
 (116 116
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (116 116 (:REWRITE NORMALIZE-ADDENDS))
 (116 114 (:REWRITE DEFAULT-TIMES-1))
 (101 101 (:REWRITE FOLD-CONSTS-IN-+))
 (101 101 (:REWRITE |(+ c (+ d x))|))
 (92 92
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (92 64 (:REWRITE DEFAULT-LOGAND-2))
 (67 55
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (66 57 (:REWRITE DEFAULT-LESS-THAN-1))
 (64 64 (:REWRITE LOGAND-CONSTANT-MASK))
 (64 64 (:REWRITE DEFAULT-LOGAND-1))
 (61 61 (:REWRITE THE-FLOOR-BELOW))
 (61 61 (:REWRITE THE-FLOOR-ABOVE))
 (55 55 (:REWRITE SIMPLIFY-SUMS-<))
 (55 55
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (- x))|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (/ x) (/ y))|))
 (55 55 (:REWRITE |(< (- x) c)|))
 (55 55 (:REWRITE |(< (- x) (- y))|))
 (48 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (37 23 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (37 23 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (26 26 (:TYPE-PRESCRIPTION ABS))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (22 2 (:REWRITE |(* y (* x z))|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (20 20 (:REWRITE |(logior c d x)|))
 (18 18 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (18 18 (:REWRITE RTL::BITS-NEG-INDICES))
 (18 12 (:REWRITE DEFAULT-LOGXOR-2))
 (12 12 (:REWRITE DEFAULT-LOGXOR-1))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (7 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T2
 (4406 4406
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (2648 135 (:REWRITE DEFAULT-PLUS-2))
 (2432 30 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (2343 2343
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (2343 2343
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (2343 2343
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (467 135 (:REWRITE DEFAULT-PLUS-1))
 (435 63 (:REWRITE DEFAULT-LOGIOR-2))
 (366 30 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (350 30 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (312 30 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (285 130 (:REWRITE DEFAULT-TIMES-2))
 (258
   258
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (258
  258
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (258 258
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (258
     258
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (258 258
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (258 258
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (216 63 (:REWRITE DEFAULT-LOGIOR-1))
 (170 76
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (164 74
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (164 74 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (154 76 (:REWRITE DEFAULT-LESS-THAN-2))
 (154 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (154 6
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (132 130 (:REWRITE DEFAULT-TIMES-1))
 (120 84 (:REWRITE DEFAULT-LOGAND-2))
 (102 102
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (92 74
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (89 89
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (89 89 (:REWRITE NORMALIZE-ADDENDS))
 (88 76 (:REWRITE DEFAULT-LESS-THAN-1))
 (84 84 (:REWRITE LOGAND-CONSTANT-MASK))
 (84 84 (:REWRITE DEFAULT-LOGAND-1))
 (81 81 (:REWRITE THE-FLOOR-BELOW))
 (81 81 (:REWRITE THE-FLOOR-ABOVE))
 (74 74 (:REWRITE SIMPLIFY-SUMS-<))
 (74 74
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (74 74 (:REWRITE INTEGERP-<-CONSTANT))
 (74 74 (:REWRITE CONSTANT-<-INTEGERP))
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
 (72 72 (:REWRITE FOLD-CONSTS-IN-+))
 (72 72 (:REWRITE |(+ c (+ d x))|))
 (66 42 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (48 30 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (48 30 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (38 38 (:TYPE-PRESCRIPTION ABS))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (30 30
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (30 30 (:REWRITE |(< 0 (/ x))|))
 (30 30 (:REWRITE |(< 0 (* x y))|))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (30 30 (:REWRITE |(< (* x y) 0)|))
 (26 26 (:REWRITE |(logior c d x)|))
 (24 24 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (24 24 (:REWRITE RTL::BITS-NEG-INDICES))
 (24 16 (:REWRITE DEFAULT-LOGXOR-2))
 (22 2 (:REWRITE |(* y (* x z))|))
 (18 18
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (16 16 (:REWRITE DEFAULT-LOGXOR-1))
 (8 6 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
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
 (6 6 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T3
 (2930 2930
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (2552 130 (:REWRITE DEFAULT-PLUS-2))
 (2161 21 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1519 1519
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (1519 1519
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (1519 1519
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (451 61 (:REWRITE DEFAULT-LOGIOR-2))
 (438 130 (:REWRITE DEFAULT-PLUS-1))
 (412 31 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (408 31 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (259 21 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (238 61 (:REWRITE DEFAULT-LOGIOR-1))
 (232 97 (:REWRITE DEFAULT-TIMES-2))
 (197
   197
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (197
  197
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (197 197
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (197
     197
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (197 197
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (197 197
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (160 104 (:REWRITE DEFAULT-LOGAND-2))
 (134 104 (:REWRITE DEFAULT-LOGAND-1))
 (129 55
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (129 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (129 5
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (125 53 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (123 53
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (114 55 (:REWRITE DEFAULT-LESS-THAN-2))
 (105 97 (:REWRITE DEFAULT-TIMES-1))
 (104 104 (:REWRITE LOGAND-CONSTANT-MASK))
 (81 81
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (81 81 (:REWRITE NORMALIZE-ADDENDS))
 (75 75
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (72 55 (:REWRITE DEFAULT-LESS-THAN-1))
 (70 31 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (70 31 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (67 67 (:REWRITE FOLD-CONSTS-IN-+))
 (67 67 (:REWRITE |(+ c (+ d x))|))
 (65 53
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (58 58 (:REWRITE THE-FLOOR-BELOW))
 (58 58 (:REWRITE THE-FLOOR-ABOVE))
 (57 53
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (55 53
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (53 53 (:REWRITE SIMPLIFY-SUMS-<))
 (53 53 (:REWRITE INTEGERP-<-CONSTANT))
 (53 53 (:REWRITE CONSTANT-<-INTEGERP))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< c (- x))|))
 (53 53
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (53 53
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (53 53 (:REWRITE |(< (/ x) (/ y))|))
 (53 53 (:REWRITE |(< (- x) c)|))
 (53 53 (:REWRITE |(< (- x) (- y))|))
 (46 30 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (30 18 (:REWRITE DEFAULT-LOGXOR-2))
 (26 26 (:TYPE-PRESCRIPTION ABS))
 (26 26 (:REWRITE |(logior c d x)|))
 (24 18 (:REWRITE DEFAULT-LOGXOR-1))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (21 21 (:REWRITE |(< 0 (/ x))|))
 (21 21 (:REWRITE |(< 0 (* x y))|))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (18 18 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (18 18 (:REWRITE RTL::BITS-NEG-INDICES))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (9 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 2 (:REWRITE |(* c (* d x))|))
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
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(* 1 x)|)))
(RTL::COMP-T4
 (2352 24 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (2069 2069
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (813 813
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (813 813
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (813 813
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (691 93 (:REWRITE DEFAULT-PLUS-2))
 (484 84 (:REWRITE DEFAULT-LOGIOR-2))
 (434 34 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (429 34 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (302 84 (:REWRITE DEFAULT-LOGIOR-1))
 (273 24 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (263 93 (:REWRITE DEFAULT-PLUS-1))
 (152 108 (:REWRITE DEFAULT-LOGAND-2))
 (142 59 (:REWRITE DEFAULT-TIMES-2))
 (130 108 (:REWRITE DEFAULT-LOGAND-1))
 (122 43
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (114 41
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (114 41 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (110
   110
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (110
  110
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (110
     110
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (110 110
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (110 43 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 108 (:REWRITE LOGAND-CONSTANT-MASK))
 (71 34 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (71 34 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (65 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (65 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (61 59 (:REWRITE DEFAULT-TIMES-1))
 (55 55
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (55 55 (:REWRITE NORMALIZE-ADDENDS))
 (51 51 (:REWRITE THE-FLOOR-BELOW))
 (51 51 (:REWRITE THE-FLOOR-ABOVE))
 (49 43 (:REWRITE DEFAULT-LESS-THAN-1))
 (46 46
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (44 41
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (41 41 (:REWRITE SIMPLIFY-SUMS-<))
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
 (38 38 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:REWRITE |(+ c (+ d x))|))
 (28 20 (:REWRITE DEFAULT-LOGXOR-2))
 (27 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (24 24 (:REWRITE |(< 0 (/ x))|))
 (24 24 (:REWRITE |(< 0 (* x y))|))
 (22 22 (:REWRITE |(logior c d x)|))
 (22 2 (:REWRITE |(* y (* x z))|))
 (20 20 (:REWRITE DEFAULT-LOGXOR-1))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (9 9 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (9 9 (:REWRITE RTL::BITS-NEG-INDICES))
 (9 9 (:REWRITE |(< (/ x) 0)|))
 (9 9 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (6 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T5
 (2480 22 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1987 1987
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (806 806
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (806 806
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (806 806
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (532 59 (:REWRITE DEFAULT-PLUS-2))
 (532 38 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (524 82 (:REWRITE DEFAULT-LOGIOR-2))
 (518 38 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (310 82 (:REWRITE DEFAULT-LOGIOR-1))
 (258 22 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (194 126 (:REWRITE DEFAULT-LOGAND-2))
 (166 126 (:REWRITE DEFAULT-LOGAND-1))
 (148 59 (:REWRITE DEFAULT-PLUS-1))
 (126 126 (:REWRITE LOGAND-CONSTANT-MASK))
 (126 52 (:REWRITE DEFAULT-TIMES-2))
 (109 41
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (109 41 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (105
   105
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (105
  105
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (105
     105
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (105 105
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (104 42 (:REWRITE DEFAULT-LESS-THAN-2))
 (92 38 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (92 38 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (86 42
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (78 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (78 4
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (54 52 (:REWRITE DEFAULT-TIMES-1))
 (48 48 (:REWRITE THE-FLOOR-BELOW))
 (48 48 (:REWRITE THE-FLOOR-ABOVE))
 (48 42 (:REWRITE DEFAULT-LESS-THAN-1))
 (47 41
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (41 41 (:REWRITE SIMPLIFY-SUMS-<))
 (41 41
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (41 41
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
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
 (38 38
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (38 38 (:REWRITE NORMALIZE-ADDENDS))
 (30 18 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (27 27 (:REWRITE |(+ c (+ d x))|))
 (26 26 (:REWRITE |(logior c d x)|))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (22 22
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (22 22 (:REWRITE |(< 0 (/ x))|))
 (22 22 (:REWRITE |(< 0 (* x y))|))
 (22 16 (:REWRITE DEFAULT-LOGXOR-2))
 (16 16 (:REWRITE DEFAULT-LOGXOR-1))
 (13 13 (:TYPE-PRESCRIPTION ABS))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< (/ x) 0)|))
 (12 12 (:REWRITE |(< (* x y) 0)|))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (9 9 (:REWRITE RTL::BITS-NEG-INDICES))
 (6 6
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (6 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T6
 (1248 10 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (778 778
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (272 16 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (267 267
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (267 267
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (267 267
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (262 16 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (222 38 (:REWRITE DEFAULT-LOGIOR-2))
 (163 45 (:REWRITE DEFAULT-PLUS-2))
 (150 38 (:REWRITE DEFAULT-LOGIOR-1))
 (130 10 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (112 6 (:REWRITE RTL::BITS-TAIL-GEN))
 (96 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (94 54 (:REWRITE DEFAULT-LOGAND-2))
 (88 40 (:REWRITE DEFAULT-TIMES-2))
 (82 54 (:REWRITE DEFAULT-LOGAND-1))
 (80 45 (:REWRITE DEFAULT-PLUS-1))
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
 (55 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (55 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (54 54 (:REWRITE LOGAND-CONSTANT-MASK))
 (54 20 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 16 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (50 16 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (42 40 (:REWRITE DEFAULT-TIMES-1))
 (30 30
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (28 28
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (24 24 (:REWRITE THE-FLOOR-BELOW))
 (24 24 (:REWRITE THE-FLOOR-ABOVE))
 (24 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (23 20 (:REWRITE DEFAULT-LESS-THAN-1))
 (22 2 (:REWRITE |(* y (* x z))|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE FOLD-CONSTS-IN-+))
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
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (14 10 (:REWRITE DEFAULT-LOGXOR-2))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE DEFAULT-LOGXOR-1))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(logior c d x)|))
 (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:TYPE-PRESCRIPTION ABS))
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
 (2 2 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T7
 (1090 13 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (930 930
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (318 318
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (318 318
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (318 318
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (205 39 (:REWRITE DEFAULT-LOGIOR-2))
 (180 15 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (156 15 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (144 25 (:REWRITE DEFAULT-PLUS-2))
 (141 39 (:REWRITE DEFAULT-LOGIOR-1))
 (140 13 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (65 24 (:REWRITE DEFAULT-TIMES-2))
 (59 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (58 42 (:REWRITE DEFAULT-LOGAND-2))
 (57 20
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (57 20 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (56 3 (:REWRITE RTL::BITS-TAIL-GEN))
 (55 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (50 25 (:REWRITE DEFAULT-PLUS-1))
 (43 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (43 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (42
   42
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (42
  42
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (42 42
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (42 42 (:REWRITE LOGAND-CONSTANT-MASK))
 (42 42 (:REWRITE DEFAULT-LOGAND-1))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 24 (:REWRITE DEFAULT-TIMES-1))
 (24 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 15 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (23 15 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (20 20 (:REWRITE SIMPLIFY-SUMS-<))
 (20 20
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (20 20
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
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
 (18 18
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (18 18 (:REWRITE NORMALIZE-ADDENDS))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (13 13 (:REWRITE |(< 0 (/ x))|))
 (13 13 (:REWRITE |(< 0 (* x y))|))
 (12 8 (:REWRITE DEFAULT-LOGXOR-2))
 (12 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 1 (:REWRITE |(* y (* x z))|))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (8 8 (:REWRITE DEFAULT-LOGXOR-1))
 (8 8 (:REWRITE |(logior c d x)|))
 (5 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (3 3 (:REWRITE RTL::BITS-NEG-INDICES))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION ABS))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T8
 (2076 16 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1070 1070
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (484 32 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (470 32 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (440 68 (:REWRITE DEFAULT-LOGIOR-2))
 (320 320
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (320 320
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (320 320
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (268 68 (:REWRITE DEFAULT-LOGIOR-1))
 (202 16 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (176 108 (:REWRITE DEFAULT-LOGAND-2))
 (148 108 (:REWRITE DEFAULT-LOGAND-1))
 (108 108 (:REWRITE LOGAND-CONSTANT-MASK))
 (92 20 (:REWRITE DEFAULT-PLUS-2))
 (86 32 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (86 32 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (79 26
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (79 26 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (77 27 (:REWRITE DEFAULT-LESS-THAN-2))
 (73 33 (:REWRITE DEFAULT-TIMES-2))
 (68 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
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
 (43 20 (:REWRITE DEFAULT-PLUS-1))
 (35 33 (:REWRITE DEFAULT-TIMES-1))
 (31 31 (:REWRITE THE-FLOOR-BELOW))
 (31 31 (:REWRITE THE-FLOOR-ABOVE))
 (30 27 (:REWRITE DEFAULT-LESS-THAN-1))
 (29 26
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (26 26 (:REWRITE SIMPLIFY-SUMS-<))
 (26 26
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (26 26 (:REWRITE INTEGERP-<-CONSTANT))
 (26 26 (:REWRITE CONSTANT-<-INTEGERP))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< c (- x))|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (26 26
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (26 26 (:REWRITE |(< (/ x) (/ y))|))
 (26 26 (:REWRITE |(< (- x) c)|))
 (26 26 (:REWRITE |(< (- x) (- y))|))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (22 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (22 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (20 20 (:REWRITE |(logior c d x)|))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 16 (:REWRITE |(< 0 (* x y))|))
 (16 12 (:REWRITE DEFAULT-LOGXOR-2))
 (15 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (13 13 (:REWRITE NORMALIZE-ADDENDS))
 (12 12 (:REWRITE DEFAULT-LOGXOR-1))
 (11 1 (:REWRITE |(* y (* x z))|))
 (7 7 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(+ c (+ d x))|))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
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
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-T9
 (200 200
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (120 120
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (120 120
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (120 120
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (76 34 (:REWRITE DEFAULT-TIMES-2))
 (58 10 (:REWRITE DEFAULT-LOGIOR-2))
 (54
   54
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (54
  54
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (54 54
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (52 34 (:REWRITE DEFAULT-TIMES-1))
 (52 11
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (51 13 (:REWRITE DEFAULT-PLUS-2))
 (34 4 (:LINEAR RTL::FL-DEF))
 (30 10 (:REWRITE DEFAULT-LOGIOR-1))
 (25 25
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (21 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (21 2
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (18 18 (:TYPE-PRESCRIPTION IFIX))
 (15 13 (:REWRITE DEFAULT-PLUS-1))
 (15 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (14 11 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 10 (:REWRITE DEFAULT-LOGXOR-2))
 (13 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (13 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (13 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 12 (:REWRITE LOGAND-CONSTANT-MASK))
 (12 12 (:REWRITE DEFAULT-LOGAND-2))
 (12 12 (:REWRITE DEFAULT-LOGAND-1))
 (11 11 (:REWRITE THE-FLOOR-BELOW))
 (11 11 (:REWRITE THE-FLOOR-ABOVE))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (11 11 (:REWRITE DEFAULT-LESS-THAN-2))
 (11 1 (:REWRITE |(* y (* x z))|))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LOGXOR-1))
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
 (7 7 (:TYPE-PRESCRIPTION ABS))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (6 6 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (6 6 (:REWRITE RTL::BITS-NEG-INDICES))
 (6 6 (:REWRITE |(< (/ x) 0)|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:REWRITE |(logior c d x)|))
 (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 3
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2 2
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2 2
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 5))
 (2 2
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 4))
 (2 2
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 3))
 (2 2 (:REWRITE |(equal c (/ x))|))
 (2 2 (:REWRITE |(equal c (- x))|))
 (2 2 (:REWRITE |(equal (/ x) c)|))
 (2 2 (:REWRITE |(equal (/ x) (/ y))|))
 (2 2 (:REWRITE |(equal (- x) c)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(equal (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:LINEAR RTL::N<=FL-LINEAR))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE |(* a (/ a) b)|)))
(RTL::COMP-29
 (1696 16 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1637 1637
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (1014 113
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (763 151 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (763 151 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (763 151
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (763 151
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (692 692
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (692 692
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (692 692
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (642 642
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (642 642
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (642 642
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (450 223 (:REWRITE DEFAULT-TIMES-2))
 (430 4 (:REWRITE MOD-ZERO . 3))
 (406 103 (:REWRITE DEFAULT-PLUS-2))
 (333 223 (:REWRITE DEFAULT-TIMES-1))
 (332 4 (:LINEAR RTL::MOD-BND-2))
 (294 294
      (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (260 4 (:LINEAR MOD-BOUNDS-3))
 (228 4 (:REWRITE DEFAULT-MOD-RATIO))
 (216 4 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (196 4 (:REWRITE MOD-X-Y-=-X . 3))
 (192 48 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (192 48 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (191 13 (:REWRITE |(* y (* x z))|))
 (190 11
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (180 4 (:REWRITE RTL::MOD-DOES-NOTHING))
 (168 16 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (165 103 (:REWRITE DEFAULT-PLUS-1))
 (162 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (161 113 (:REWRITE DEFAULT-LESS-THAN-2))
 (160 100
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (160 100
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (151 151 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (151 151
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (151 151
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (151 151
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (147 147 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (145 25 (:REWRITE DEFAULT-LOGIOR-2))
 (141 113 (:REWRITE DEFAULT-LESS-THAN-1))
 (123 123
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (117 117 (:REWRITE THE-FLOOR-BELOW))
 (117 117 (:REWRITE THE-FLOOR-ABOVE))
 (115 100
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (100 100 (:REWRITE SIMPLIFY-SUMS-<))
 (100 100
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (100 100 (:REWRITE INTEGERP-<-CONSTANT))
 (100 100 (:REWRITE CONSTANT-<-INTEGERP))
 (100 100
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (100 100
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (100 100
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (100 100
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (100 100 (:REWRITE |(< c (- x))|))
 (100 100
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (100 100
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (100 100
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (100 100
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (100 100 (:REWRITE |(< (/ x) (/ y))|))
 (100 100 (:REWRITE |(< (- x) c)|))
 (100 100 (:REWRITE |(< (- x) (- y))|))
 (91 67 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (85 85 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (84 16 (:LINEAR RTL::FL-DEF))
 (75 25 (:REWRITE DEFAULT-LOGIOR-1))
 (66 66
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (66 66 (:REWRITE NORMALIZE-ADDENDS))
 (56 8 (:LINEAR MOD-BOUNDS-2))
 (50 3
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (48 48 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (48 48 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (43 43 (:TYPE-PRESCRIPTION ABS))
 (43 13 (:META META-INTEGERP-CORRECT))
 (40 40 (:TYPE-PRESCRIPTION IFIX))
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
 (40 40 (:REWRITE |arith (* c (* d x))|))
 (40 16 (:REWRITE |(* c (* d x))|))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (39 39
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (39 39 (:REWRITE |(< (/ x) 0)|))
 (39 39 (:REWRITE |(< (* x y) 0)|))
 (35 25 (:REWRITE DEFAULT-LOGXOR-2))
 (32 32 (:REWRITE |arith (+ c (+ d x))|))
 (32 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (30 30 (:REWRITE LOGAND-CONSTANT-MASK))
 (30 30 (:REWRITE DEFAULT-LOGAND-2))
 (30 30 (:REWRITE DEFAULT-LOGAND-1))
 (30 30 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (30 30 (:REWRITE RTL::BITS-NEG-INDICES))
 (29 13 (:REWRITE |(* a (/ a) b)|))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (25 25 (:REWRITE DEFAULT-LOGXOR-1))
 (24 24 (:REWRITE |(< 0 (* x y))|))
 (24 24 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (20 4 (:REWRITE MOD-ZERO . 4))
 (20 4 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (20 4 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (20 4 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (20 4 (:REWRITE MOD-X-Y-=-X . 4))
 (20 4 (:REWRITE MOD-X-Y-=-X . 2))
 (20 4
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (20 4
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (20 4
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (19 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (16 16
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (16 16
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 16 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (15 15
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (13 13 (:REWRITE REDUCE-INTEGERP-+))
 (13 13 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:REWRITE |(logior c d x)|))
 (8 8 (:REWRITE |arith (- (* c x))|))
 (8 8 (:REWRITE |arith (* (- x) y)|))
 (8 8
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (8 8 (:LINEAR RTL::N<=FL-LINEAR))
 (8 2 (:REWRITE RATIONALP-X))
 (7 7 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 5))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 4))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 3))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4
    (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (4 4
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4 4 (:REWRITE DEFAULT-MOD-2))
 (4 4 (:REWRITE DEFAULT-MOD-1))
 (4 4 (:REWRITE |(mod x (- y))| . 3))
 (4 4 (:REWRITE |(mod x (- y))| . 2))
 (4 4 (:REWRITE |(mod x (- y))| . 1))
 (4 4
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (4 4
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (4 4
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (4 4 (:LINEAR RTL::MOD-BND-3))
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
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(RTL::COMP-30
 (53364 3 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (26740 31 (:REWRITE |(equal (+ (- c) x) y)|))
 (26606 3 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (15671 200 (:REWRITE RTL::MOD-DOES-NOTHING))
 (15311 215 (:REWRITE MOD-ZERO . 4))
 (12343 215 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (10879 215 (:REWRITE MOD-X-Y-=-X . 4))
 (10231 215 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (9425 9425
       (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (7652 215 (:REWRITE MOD-ZERO . 3))
 (7272 215 (:REWRITE DEFAULT-MOD-RATIO))
 (6530 66 (:REWRITE |(* x (+ y z))|))
 (6413 1060 (:REWRITE DEFAULT-TIMES-2))
 (5428 5428
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5428 5428
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5428 5428
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5291 64 (:LINEAR RTL::MOD-BND-2))
 (5033 110 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (4815 726
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4663 4663
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (4663 4663
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (4663 4663
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (4473 87 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (4248 110 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (3467 67 (:REWRITE |(* y (* x z))|))
 (3439 679 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3439 679 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3439 679
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3439 679
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2966 389
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2482 389
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2429 409 (:REWRITE DEFAULT-LESS-THAN-1))
 (2408 1060 (:REWRITE DEFAULT-TIMES-1))
 (2228 200 (:REWRITE MOD-X-Y-=-X . 2))
 (2083 64 (:LINEAR MOD-BOUNDS-3))
 (1791 139 (:REWRITE DEFAULT-PLUS-2))
 (1689 215 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1689 215 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1557 409
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1428 200
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1428 200
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1155 110 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (1121 139 (:REWRITE DEFAULT-PLUS-1))
 (1108 69 (:REWRITE |(* c (* d x))|))
 (1086 1
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (997 409 (:REWRITE DEFAULT-LESS-THAN-2))
 (964 128 (:LINEAR MOD-BOUNDS-2))
 (839 66
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (829 215 (:REWRITE DEFAULT-MOD-1))
 (748 88 (:LINEAR RTL::FL-DEF))
 (726 726
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (726 726
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (726 726
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (704 66 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (700 3 (:REWRITE |(+ (+ x y) z)|))
 (679 679 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (679 679
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (679 679
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (679 679
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (662 139 (:REWRITE DEFAULT-LOGIOR-2))
 (657 657 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (569 394 (:REWRITE |(< c (- x))|))
 (557 557
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (480 60 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (480 60 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (478 28
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (478 28
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (424 139 (:REWRITE DEFAULT-LOGIOR-1))
 (413 394
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (412 412 (:REWRITE THE-FLOOR-BELOW))
 (412 412 (:REWRITE THE-FLOOR-ABOVE))
 (396 396 (:TYPE-PRESCRIPTION IFIX))
 (395 3 (:REWRITE |(+ y (+ x z))|))
 (394 394
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (394 394
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (394 394
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (394 394
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (394 394
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (394 394
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (394 394
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (394 394
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (394 394 (:REWRITE |(< (/ x) (/ y))|))
 (394 394 (:REWRITE |(< (- x) (- y))|))
 (389 389 (:REWRITE SIMPLIFY-SUMS-<))
 (389 389
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (389 389 (:REWRITE INTEGERP-<-CONSTANT))
 (389 389 (:REWRITE CONSTANT-<-INTEGERP))
 (389 389 (:REWRITE |(< (- x) c)|))
 (386 200
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (386 200
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (364 66 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (289 17 (:REWRITE |(* (* x y) z)|))
 (244 28
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (215 215 (:REWRITE DEFAULT-MOD-2))
 (212 212 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (209 124 (:REWRITE NORMALIZE-ADDENDS))
 (200 200
      (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (200 200 (:REWRITE |(mod x (- y))| . 3))
 (200 200 (:REWRITE |(mod x (- y))| . 2))
 (200 200 (:REWRITE |(mod x (- y))| . 1))
 (200 200
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (200 200
      (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (150 150 (:REWRITE LOGAND-CONSTANT-MASK))
 (150 150 (:REWRITE DEFAULT-LOGAND-2))
 (150 150 (:REWRITE DEFAULT-LOGAND-1))
 (146 146
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (146 146
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (146 146 (:REWRITE |(< (/ x) 0)|))
 (146 146 (:REWRITE |(< (* x y) 0)|))
 (123 123
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (120 120 (:REWRITE |(< (+ c/d x) y)|))
 (120 120 (:REWRITE |(< (+ (- c) x) y)|))
 (112 112 (:REWRITE |(< 0 (* x y))|))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (99 99
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (99 99 (:REWRITE |(< 0 (/ x))|))
 (88 88
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (88 88
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (88 88 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (84 1 (:REWRITE |(- (+ x y))|))
 (83 83 (:REWRITE REDUCE-INTEGERP-+))
 (83 83 (:REWRITE INTEGERP-MINUS-X))
 (83 83 (:META META-INTEGERP-CORRECT))
 (82 3
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (73 13 (:REWRITE DEFAULT-MINUS))
 (69 67
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (67 67
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (66 66
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (66 66 (:REWRITE |(equal c (/ x))|))
 (66 66 (:REWRITE |(equal c (- x))|))
 (66 66 (:REWRITE |(equal (/ x) c)|))
 (66 66 (:REWRITE |(equal (/ x) (/ y))|))
 (66 66 (:REWRITE |(equal (- x) c)|))
 (66 66 (:REWRITE |(equal (- x) (- y))|))
 (64 64 (:LINEAR RTL::MOD-BND-3))
 (63 63
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (60 60 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (60 60 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (55 55 (:TYPE-PRESCRIPTION ABS))
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
 (44 44 (:LINEAR RTL::N<=FL-LINEAR))
 (41 15 (:REWRITE |(* a (/ a) b)|))
 (39 3 (:REWRITE |(< (logior x y) 0)|))
 (37 37
     (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (37 37
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (36 26 (:REWRITE DEFAULT-LOGXOR-2))
 (35 35 (:REWRITE |(logior c d x)|))
 (31 31 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (31 31 (:REWRITE RTL::BITS-NEG-INDICES))
 (28 28 (:REWRITE |(< y (+ (- c) x))|))
 (28 28 (:REWRITE |(< x (+ c/d y))|))
 (27 26 (:REWRITE DEFAULT-LOGXOR-1))
 (27 2 (:REWRITE |(- (* c x))|))
 (25 16 (:REWRITE RTL::BITS-TAIL))
 (21 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 1 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (21 1 (:DEFINITION FIX))
 (20 1 (:REWRITE |(+ (* c x) (* d x))|))
 (15 15
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (15 15
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (12 12
     (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 2))
 (10 5 (:REWRITE |(- (- x))|))
 (6 1 (:REWRITE |(+ 0 x)|))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 5))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 4))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 3))
 (3 1 (:REWRITE RTL::LOGXOR-BVECP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(equal (* x y) 0)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE |(* 0 x)|)))
(RTL::PPB*-REWRITE
 (5776 11 (:REWRITE RTL::BITS-TAIL-GEN))
 (3309 56
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2548 12 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (1916 12 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (1672 4 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (606 606
      (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (468 12 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (456 12 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (456 12 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (432 44 (:REWRITE DEFAULT-TIMES-2))
 (388 8 (:REWRITE |(* y (* x z))|))
 (252 26 (:REWRITE DEFAULT-LOGIOR-2))
 (252 12 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (220 12 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (204 204
      (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (204 204
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (204 204
      (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (198 52 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (197 52
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (192 56 (:REWRITE DEFAULT-LESS-THAN-1))
 (154 26 (:REWRITE DEFAULT-LOGIOR-1))
 (116 56 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (108 8 (:REWRITE |(* a (/ a) b)|))
 (102 52
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (100 44 (:REWRITE DEFAULT-TIMES-1))
 (56 56 (:REWRITE THE-FLOOR-BELOW))
 (56 56 (:REWRITE THE-FLOOR-ABOVE))
 (52 52 (:REWRITE SIMPLIFY-SUMS-<))
 (52 52
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (52 52
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (52 52 (:REWRITE INTEGERP-<-CONSTANT))
 (52 52 (:REWRITE CONSTANT-<-INTEGERP))
 (52 52
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (52 52
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (52 52
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (52 52
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (52 52 (:REWRITE |(< c (- x))|))
 (52 52
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (52 52
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (52 52
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (52 52 (:REWRITE |(< (/ x) (/ y))|))
 (52 52 (:REWRITE |(< (- x) c)|))
 (52 52 (:REWRITE |(< (- x) (- y))|))
 (44 22 (:REWRITE DEFAULT-LOGAND-2))
 (44 22 (:REWRITE DEFAULT-LOGAND-1))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< (/ x) 0)|))
 (36 36 (:REWRITE |(< (* x y) 0)|))
 (22 22 (:REWRITE LOGAND-CONSTANT-MASK))
 (19 11 (:REWRITE RTL::BITS-TAIL))
 (18 18
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12 (:REWRITE |(logior c d x)|))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (11 11 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (11 11 (:REWRITE RTL::BITS-NEG-INDICES))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
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
 (4 4 (:TYPE-PRESCRIPTION ABS)))
(RTL::COMP-31
 (28434 68 (:REWRITE RTL::MOD-DOES-NOTHING))
 (14170 80 (:REWRITE MOD-X-Y-=-X . 4))
 (14084 80 (:REWRITE MOD-ZERO . 4))
 (13140 80 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (12051 12051
        (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (8476 80 (:REWRITE DEFAULT-MOD-RATIO))
 (8176 220
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6878 130 (:LINEAR LOGIOR-BOUNDS-NEG . 1))
 (6718 130 (:LINEAR LOGIOR-BOUNDS-POS . 2))
 (6356 702 (:REWRITE DEFAULT-TIMES-2))
 (6166 6166
       (:TYPE-PRESCRIPTION |(< 0 (logior x y))| . 1))
 (6166 6166
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (6166 6166
       (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (5811 441
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (5718 84 (:LINEAR LOGIOR-BOUNDS-POS . 1))
 (5550 78 (:REWRITE |(* (* x y) z)|))
 (4782 80 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4508 80 (:REWRITE MOD-ZERO . 3))
 (3478 702 (:REWRITE DEFAULT-TIMES-1))
 (3109 2
       (:REWRITE |(equal (mod a n) (mod b n))|))
 (2954 2954
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (2954 2954
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (2954 2954
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2514 494 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2514 494 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2514 494
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2514 494
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2412 68 (:REWRITE MOD-X-Y-=-X . 2))
 (1859 55 (:REWRITE DEFAULT-PLUS-2))
 (1815 185
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1752 30 (:REWRITE |(* x (+ y z))|))
 (1524 80 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1524 80 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1498 220 (:REWRITE DEFAULT-LESS-THAN-1))
 (1498 130 (:LINEAR LOGIOR-BOUNDS-NEG . 2))
 (1488 84 (:REWRITE |(* c (* d x))|))
 (1475 2 (:REWRITE |(+ (+ x y) z)|))
 (1410 185
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1333 41 (:REWRITE |(* y (* x z))|))
 (1204 80 (:REWRITE DEFAULT-MOD-1))
 (1163 4 (:REWRITE |(+ y (+ x z))|))
 (1108 68
       (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1108 68
       (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (792 20 (:LINEAR MOD-BOUNDS-3))
 (784 40 (:LINEAR MOD-BOUNDS-2))
 (764 220 (:REWRITE DEFAULT-LESS-THAN-2))
 (759 120 (:REWRITE DEFAULT-LOGIOR-2))
 (752 94 (:LINEAR LOGAND-BOUNDS-POS . 2))
 (752 94 (:LINEAR LOGAND-BOUNDS-POS . 1))
 (508 44 (:REWRITE NORMALIZE-ADDENDS))
 (505 55 (:REWRITE DEFAULT-PLUS-1))
 (494 494 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (494 494
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (494 494
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (494 494
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (472 472 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (441 441
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (441 441
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (441 441
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (380 24
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (380 24 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (367 120 (:REWRITE DEFAULT-LOGIOR-1))
 (336 68
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (336 68
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (325 325
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (290 2 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (252 2 (:REWRITE |(- (+ x y))|))
 (248 12
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (235 185
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (227 35 (:REWRITE |(* a (/ a) b)|))
 (222 222 (:REWRITE THE-FLOOR-BELOW))
 (222 222 (:REWRITE THE-FLOOR-ABOVE))
 (218 218 (:REWRITE LOGAND-CONSTANT-MASK))
 (218 218 (:REWRITE DEFAULT-LOGAND-2))
 (218 218 (:REWRITE DEFAULT-LOGAND-1))
 (185 185 (:REWRITE SIMPLIFY-SUMS-<))
 (185 185
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (185 185 (:REWRITE INTEGERP-<-CONSTANT))
 (185 185 (:REWRITE CONSTANT-<-INTEGERP))
 (185 185
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (185 185
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (185 185
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (185 185
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (185 185 (:REWRITE |(< c (- x))|))
 (185 185
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (185 185
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (185 185
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (185 185
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (185 185 (:REWRITE |(< (/ x) (/ y))|))
 (185 185 (:REWRITE |(< (- x) c)|))
 (185 185 (:REWRITE |(< (- x) (- y))|))
 (162 6 (:REWRITE DEFAULT-MINUS))
 (145 145 (:TYPE-PRESCRIPTION ABS))
 (138 2 (:REWRITE |(+ 0 x)|))
 (118 118 (:REWRITE |(< 0 (* x y))|))
 (114 2 (:REWRITE MOD-ZERO . 1))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (94 94
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (94 94 (:REWRITE |(< 0 (/ x))|))
 (94 94 (:LINEAR LOGAND-BOUNDS-NEG . 2))
 (94 94 (:LINEAR LOGAND-BOUNDS-NEG . 1))
 (88 88
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (88 88
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (82 4 (:REWRITE |(- (* c x))|))
 (82 2 (:REWRITE MOD-POSITIVE . 3))
 (80 80 (:REWRITE DEFAULT-MOD-2))
 (74 2 (:REWRITE MOD-ZERO . 2))
 (73 1 (:REWRITE |(+ y x)|))
 (70 70 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (68 68
     (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (68 68 (:REWRITE |(mod x (- y))| . 3))
 (68 68 (:REWRITE |(mod x (- y))| . 2))
 (68 68 (:REWRITE |(mod x (- y))| . 1))
 (68 68
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (68 68
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (57 57 (:REWRITE |(logior c d x)|))
 (42 42
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (42 2 (:REWRITE MOD-NONPOSITIVE))
 (39
   39
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (39
  39
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (39 39
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (38 38 (:REWRITE |(< (+ c/d x) y)|))
 (38 38 (:REWRITE |(< (+ (- c) x) y)|))
 (34 34
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (34 24
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (34 2
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< (/ x) 0)|))
 (32 32 (:REWRITE |(< (* x y) 0)|))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:META META-INTEGERP-CORRECT))
 (28 28
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (26 2 (:REWRITE |(< (logior x y) 0)|))
 (24 24
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (24 24
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (24 24
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (24 24 (:REWRITE |(equal c (/ x))|))
 (24 24 (:REWRITE |(equal c (- x))|))
 (24 24 (:REWRITE |(equal (/ x) c)|))
 (24 24 (:REWRITE |(equal (/ x) (/ y))|))
 (24 24 (:REWRITE |(equal (- x) c)|))
 (24 24 (:REWRITE |(equal (- x) (- y))|))
 (21 21 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (21 21 (:REWRITE RTL::BITS-NEG-INDICES))
 (18 18 (:LINEAR RTL::MOD-BND-3))
 (17 11 (:REWRITE RTL::BITS-TAIL))
 (16 16
     (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (16 16
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (12 12
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (12 12 (:REWRITE |(equal (+ (- c) x) y)|))
 (12 12 (:REWRITE |(< y (+ (- c) x))|))
 (12 12 (:REWRITE |(< x (+ c/d y))|))
 (12 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (12 2 (:DEFINITION FIX))
 (10 10 (:REWRITE |(equal (* x y) 0)|))
 (10 2 (:REWRITE |(+ (* c x) (* d x))|))
 (6 6 (:REWRITE |(+ c (+ d x))|))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 5))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 4))
 (5 5
    (:REWRITE |(logand (* 2 x) (* 2 y))| . 3))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE |(* (- x) y)|))
 (2 2 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (2 2 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (2 2 (:REWRITE MOD-POSITIVE . 2))
 (2 2 (:REWRITE MOD-POSITIVE . 1))
 (2 2 (:REWRITE |(* 0 x)|)))
(RTL::PROD-REWRITE
 (88 2 (:REWRITE DEFAULT-MOD-RATIO))
 (87 3 (:REWRITE |(* y x)|))
 (69 3 (:REWRITE |(* x (+ y z))|))
 (66 2 (:REWRITE MOD-ZERO . 3))
 (59 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (54 2 (:REWRITE MOD-X-Y-=-X . 4))
 (51 2 (:REWRITE MOD-X-Y-=-X . 3))
 (51 1 (:REWRITE RTL::BITS-TAIL-GEN))
 (49 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (41 2 (:REWRITE RTL::MOD-DOES-NOTHING))
 (37 2 (:REWRITE MOD-ZERO . 4))
 (28 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (24 12 (:REWRITE DEFAULT-TIMES-2))
 (22 5 (:REWRITE DEFAULT-PLUS-2))
 (22 5 (:REWRITE DEFAULT-PLUS-1))
 (22 2
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (21 21 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (18 12 (:REWRITE DEFAULT-TIMES-1))
 (18 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (18 2 (:REWRITE MOD-X-Y-=-X . 2))
 (15 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (14 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (14 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (14 2
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (14 2
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (13 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (9 9
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 2 (:REWRITE DEFAULT-MOD-1))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE SIMPLIFY-SUMS-<))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE NORMALIZE-ADDENDS))
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
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (3 1 (:REWRITE RTL::BITS-TAIL))
 (2 2
    (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE |(mod x (- y))| . 3))
 (2 2 (:REWRITE |(mod x (- y))| . 2))
 (2 2 (:REWRITE |(mod x (- y))| . 1))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2 2
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2 2
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (2 2
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (1
   1
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1
  1
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1 1
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE RTL::BITS-REVERSE-INDICES))
 (1 1 (:REWRITE RTL::BITS-NEG-INDICES))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:META META-INTEGERP-CORRECT)))
