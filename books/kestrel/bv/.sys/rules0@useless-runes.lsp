(BVMULT-1-BECOMES-BITAND
 (150 54 (:REWRITE BVCHOP-IDENTITY))
 (54 54 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (48 16 (:DEFINITION NATP))
 (45 15 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (45 15 (:REWRITE GETBIT-IDENTITY))
 (42 42 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (42 42 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (42 42 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (42 42 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (42 42 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (42 42 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (42 42 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (40 8 (:LINEAR <=-OF-BVAND-ARG2-LINEAR))
 (40 8 (:LINEAR <=-OF-BVAND-ARG1-LINEAR))
 (36 36 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (36 36 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (36 36 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (36 20 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (32 24 (:REWRITE DEFAULT-<-1))
 (32 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (30 15 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (25 25 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (24 24 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (20 20 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (16 16 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (15 15 (:TYPE-PRESCRIPTION BITP))
 (15 15 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (15 15 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (15 15 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (15 15 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (15 15 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (15 15 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (15 15 (:REWRITE SLICE-OUT-OF-ORDER))
 (15 15 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (15 15 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (15 15 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (15 15 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (15 15 (:REWRITE GETBIT-IDENTITY-FREE))
 (15 15 (:DEFINITION BITP))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE BVMULT-1-1))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (4 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (4 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE EVENP-OF-BVCHOP))
 (2 2 (:REWRITE LOGAND-OF-BVCHOP-TIGHTEN-FREE))
 (2 2 (:REWRITE BVAND-WITH-MASK-DROP))
 (2 2 (:REWRITE BVAND-WITH-CONSTANT-MASK-ARG2))
 (2 2 (:REWRITE BVAND-WHEN-Y-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVAND-WHEN-X-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVAND-WHEN-SIZE-IS-NOT-POSITIVE))
 (2 2 (:REWRITE BVAND-WHEN-SIZE-IS-NOT-INTEGERP))
 (2 2 (:REWRITE BVAND-OF-CONSTANT-CHOP-ARG3))
 (2 2 (:REWRITE BVAND-OF-CONSTANT-CHOP-ARG2))
 )
(BVPLUS-1-BECOMES-BITXOR
 (42 14 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (42 14 (:REWRITE GETBIT-IDENTITY))
 (37 37 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (28 14 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (17 17 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (17 12 (:REWRITE BVPLUS-TRIM-LEADING-CONSTANT))
 (14 14 (:TYPE-PRESCRIPTION BITP))
 (14 14 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (14 14 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (14 14 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (14 14 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (14 14 (:REWRITE GETBIT-IDENTITY-FREE))
 (14 14 (:DEFINITION BITP))
 (12 12 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (12 12 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (12 12 (:REWRITE BVPLUS-SUBST-SMALLER-TERM-ARG2))
 (12 12 (:REWRITE BVPLUS-SUBST-SMALLER-TERM-ARG1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-AND-BITXOR-OF-CONSTANT))
 (2 2 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (2 2 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (2 2 (:REWRITE BVPLUS-SUBST-VALUE))
 (2 2 (:REWRITE BITXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BITXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BITXOR-SUBST-ARG1))
 (2 2 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG2))
 (2 2 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG1))
 )
(GETBIT-0-OF-BVPLUS
 (36 3 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (30 30 (:TYPE-PRESCRIPTION BVPLUS))
 (24 3 (:DEFINITION BITP))
 (18 3 (:REWRITE GETBIT-IDENTITY))
 (9 3 (:REWRITE UNSIGNED-BYTE-P-OF-BVPLUS))
 (6 3 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (6 3 (:REWRITE GETBIT-WHEN-NOT-1))
 (6 3 (:REWRITE GETBIT-WHEN-NOT-0))
 (6 3 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE BITXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BITXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BITXOR-SUBST-ARG2))
 (4 4 (:REWRITE BITXOR-SUBST-ARG1))
 (4 4 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG2))
 (4 4 (:REWRITE BITXOR-OF-CONSTANT-CHOP-ARG1))
 (4 4 (:REWRITE BITXOR-COMMUTATIVE-ALT))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 3 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (3 3 (:REWRITE SLICE-WHEN-INDICES-ARE-NEGATIVE))
 (3 3 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (3 3 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (3 3 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (3 3 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (3 3 (:REWRITE SLICE-OUT-OF-ORDER))
 (3 3 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (3 3 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (3 3 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (3 3 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (3 3 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:REWRITE BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE))
 (1 1 (:REWRITE BVPLUS-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG3))
 (1 1 (:REWRITE BVPLUS-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-ARG2))
 (1 1 (:REWRITE BVPLUS-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVPLUS-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVPLUS-TRIM-LEADING-CONSTANT))
 (1 1 (:REWRITE BVPLUS-SUBST-VALUE-ALT))
 (1 1 (:REWRITE BVPLUS-SUBST-VALUE))
 (1 1 (:REWRITE BVPLUS-SUBST-SMALLER-TERM-ARG2))
 (1 1 (:REWRITE BVPLUS-SUBST-SMALLER-TERM-ARG1))
 )
