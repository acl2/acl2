(STR::HEX-DIGIT-CHAR-VALUE-OF-HEX-DIGIT-TO-CHAR
     (4 2
        (:LINEAR STR::HEX-DIGIT-CHAR-VALUE-UPPER-BOUND))
     (2 2
        (:REWRITE STR::HEX-DIGIT-CHAR-VALUE-OF-DIGIT-TO-CHAR))
     (2 2 (:REWRITE DEFAULT-<-2))
     (2 2 (:REWRITE DEFAULT-<-1)))
(STR::HEX-DIGIT-TO-CHAR-OF-HEX-DIGIT-CHAR-VALUE
   (158 158
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
   (137 137 (:REWRITE SIMPLIFY-SUMS-EQUAL))
   (137 137
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
   (137 137
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
   (137 137
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
   (137 137 (:REWRITE |(equal c (/ x))|))
   (137 137 (:REWRITE |(equal c (- x))|))
   (137 137 (:REWRITE |(equal (/ x) c)|))
   (137 137 (:REWRITE |(equal (/ x) (/ y))|))
   (137 137 (:REWRITE |(equal (- x) c)|))
   (137 137 (:REWRITE |(equal (- x) (- y))|))
   (118 118 (:REWRITE DEFAULT-CHAR-CODE))
   (82 82 (:REWRITE THE-FLOOR-BELOW))
   (82 82 (:REWRITE THE-FLOOR-ABOVE))
   (82 82
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
   (82 82
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
   (82 82
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
   (82 82 (:REWRITE INTEGERP-<-CONSTANT))
   (82 82 (:REWRITE DEFAULT-LESS-THAN-2))
   (82 82 (:REWRITE DEFAULT-LESS-THAN-1))
   (82 82 (:REWRITE CONSTANT-<-INTEGERP))
   (82 82
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
   (82 82
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
   (82 82
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
   (82 82
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
   (82 82 (:REWRITE |(< c (- x))|))
   (82 82
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
   (82 82
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
   (82 82
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
   (82 82
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
   (82 82 (:REWRITE |(< (/ x) (/ y))|))
   (82 82 (:REWRITE |(< (- x) c)|))
   (82 82 (:REWRITE |(< (- x) (- y))|))
   (69 69 (:REWRITE DEFAULT-PLUS-2))
   (69 69 (:REWRITE DEFAULT-PLUS-1))
   (45 45 (:REWRITE |(equal (+ (- c) x) y)|))
   (24 24
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
   (24 24 (:REWRITE NORMALIZE-ADDENDS))
   (19 19 (:REWRITE SIMPLIFY-SUMS-<))
   (19 19
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
   (19 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
   (18 3
       (:REWRITE STR::UPCASE-CHAR-DOES-NOTHING-UNLESS-DOWN-ALPHA-P))
   (9 3
      (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
   (9 3
      (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
   (6 6
      (:TYPE-PRESCRIPTION STR::UP-ALPHA-P$INLINE))
   (6 6
      (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
   (6 6
      (:TYPE-PRESCRIPTION STR::DOWN-ALPHA-P$INLINE))
   (6 6
      (:REWRITE
           STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LISTP)))
