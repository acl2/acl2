(DENOMINATOR-POSITIVE-INTEGER-TYPE-PRESCRIPTION)
(DENOMINATOR-POSITIVE)
(DENOMINATOR-INTEGERP)
(DENOMINATOR-ONE-MEANS-INTEGER
 (11 7 (:REWRITE DEFAULT-*-2))
 (11 7 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (3 3 (:REWRITE EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 1 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 )
(DENOMINATOR-OF-INTEGER-IS-ONE)
(DENOMINATOR-LOWER-BOUND
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:LINEAR /-WEAKLY-MONOTONIC))
 (2 2 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE DENOMINATOR-OF-INTEGER-IS-ONE))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
