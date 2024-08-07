(RTL::FL)
(RTL::NATP-COMPOUND-RECOGNIZER
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(RTL::NATP+)
(RTL::NATP*)
(RTL::ABS-NONNEGATIVE-ACL2-NUMBERP-TYPE
 (5 5 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (5 5 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(RTL::ABS-NONNEGATIVE-RATIONALP-TYPE
 (3 3 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 3 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(RTL::ABS-NONNEGATIVE-INTEGERP-TYPE)
(RTL::ABS-NONNEGATIVE
 (23 23 (:TYPE-PRESCRIPTION RTL::ABS-NONNEGATIVE-INTEGERP-TYPE))
 (7 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (4 4 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (4 4 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(RTL::FL-DEF
 (48 48 (:TYPE-PRESCRIPTION RTL::FL-NON-NEGATIVE-INTEGER-TYPE-PRESCRIPTION))
 (3 1 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE RTL::FL-OF-NON-RATIONAL))
 (2 2 (:REWRITE RTL::FL-MINUS-GEN))
 (2 2 (:REWRITE RTL::FL-INT))
 (2 2 (:REWRITE RTL::A10))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(RTL::EXPT-EXEC
 (102 4 (:DEFINITION EXPT))
 (54 54 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (24 6 (:REWRITE DEFAULT-*-2))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-*-1))
 (5 5 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (5 5 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (5 5 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (5 5 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE ZIP-OPEN))
 (4 4 (:DEFINITION FIX))
 (3 3 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (3 3 (:REWRITE RTL::EQUAL-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 )
(RTL::EXPT-2-EVALUATOR
 (50 2 (:DEFINITION EXPT))
 (21 21 (:TYPE-PRESCRIPTION RTL::EXPT-2-POSITIVE-INTEGER-TYPE))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 4 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(RTL::*-DOUBLY-MONOTONIC)
(RTL::FL-HALF)
(RTL::FL-HALF-LEMMA
 (46 2 (:LINEAR RTL::FL-NON-NEGATIVE-LINEAR))
 (17 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (8 8 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (8 8 (:LINEAR RTL::*-WEAKLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (8 8 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 2))
 (8 8 (:LINEAR RTL::*-WEAKLY-MONOTONIC . 1))
 (8 8 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 2))
 (8 8 (:LINEAR RTL::*-STRONGLY-MONOTONIC-NEGATIVE-MULTIPLIER . 1))
 (8 8 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 2))
 (8 8 (:LINEAR RTL::*-STRONGLY-MONOTONIC . 1))
 (5 5 (:REWRITE RTL::FL-OF-NON-RATIONAL))
 (5 5 (:REWRITE RTL::FL-MINUS-GEN))
 (4 4 (:LINEAR RTL::FL-WEAKLY-MONOTONIC . 2))
 (4 4 (:LINEAR RTL::FL-WEAKLY-MONOTONIC . 1))
 (4 4 (:LINEAR RTL::FL-MONOTONE-LINEAR))
 (2 2 (:REWRITE RTL::NON-INTEGERP-<-INTEGERP))
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
 (2 2 (:REWRITE RTL::LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE))
 (2 2 (:REWRITE RTL::INTEGERP-<-NON-INTEGERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR RTL::N<=FL-LINEAR))
 (1 1 (:REWRITE RTL::PULL-CONSTANT-OUT-OF-FL))
 (1 1 (:REWRITE RTL::FL-PLUS-INTEGER-ERIC))
 (1 1 (:REWRITE RTL::FL+INT-REWRITE))
 )
