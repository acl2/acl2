(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P)
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-NECC)
(ALEOBFT-DYNAMIC::BOOLEANP-OF-LAST-ANCHOR-PRESENT-P)
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P
 (10 4 (:REWRITE SET::IN-TAIL))
 (10 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (8 1 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (5 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SETP-WHEN-POS-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-MESSAGE-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-CERTIFICATE-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-ADDRESS+POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::MESSAGE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS+POS-SETP))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (2 2 (:REWRITE |(equal (- x) 0)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESSP))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT
 (8 2 (:REWRITE SET::IN-TAIL))
 (3 3 (:REWRITE-QUOTED-CONSTANT ALEOBFT-DYNAMIC::CERTIFICATE-SET-FIX-UNDER-CERTIFICATE-SET-EQUIV))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE SET::EMPTYP-SUBSET-2))
 (3 1 (:REWRITE SET::EMPTYP-SUBSET))
 (1 1 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-UNDER-BLOCK-LIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-DYNAMIC::ADDRESS+POS-SET-FIX-UNDER-ADDRESS+POS-SET-EQUIV))
 (1 1 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (1 1 (:REWRITE ALEOBFT-DYNAMIC::NOT-EMPTYP-OF-COMMITTEE-MEMBERS))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-CREATE-CERTIFICATE-NEXT
 (20 6 (:REWRITE SET::IN-TAIL))
 (18 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-FIX-WHEN-CERTIFICATEP))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (10 2 (:REWRITE SET::INSERT-IDENTITY))
 (10 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-CERTIFICATE-OPTIONP))
 (9 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATEP))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 2 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP))
 (4 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP-WHEN-CERTIFICATEP))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-IN-CERTIFICATE-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE |(equal (- x) 0)|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-CREATE-CERTIFICATE-NEXT
 (96 24 (:REWRITE SET::IN-TAIL))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 12 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (36 12 (:REWRITE SET::NEVER-IN-EMPTY))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (20 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE |(equal (- x) 0)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-RECEIVE-CERTIFICATE-NEXT
 (8 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-RECEIVE-CERTIFICATE-NEXT
 (96 24 (:REWRITE SET::IN-TAIL))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 12 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (36 12 (:REWRITE SET::NEVER-IN-EMPTY))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (20 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE |(equal (- x) 0)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-STORE-CERTIFICATE-NEXT
 (20 6 (:REWRITE SET::IN-TAIL))
 (20 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-FIX-WHEN-ADDRESSP))
 (18 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-FIX-WHEN-CERTIFICATEP))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (10 2 (:REWRITE SET::INSERT-IDENTITY))
 (10 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-CERTIFICATE-OPTIONP))
 (10 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (9 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATEP))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESSP))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 2 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (4 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP-WHEN-CERTIFICATEP))
 (4 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-IN-CERTIFICATE-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-ADDRESS-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE |(equal (- x) 0)|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-STORE-CERTIFICATE-NEXT
 (96 24 (:REWRITE SET::IN-TAIL))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 12 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (36 12 (:REWRITE SET::NEVER-IN-EMPTY))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (20 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE |(equal (- x) 0)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-ADVANCE-ROUND-NEXT
 (8 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-ADVANCE-ROUND-NEXT
 (96 24 (:REWRITE SET::IN-TAIL))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 12 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (36 12 (:REWRITE SET::NEVER-IN-EMPTY))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (20 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE |(equal (- x) 0)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-COMMIT-ANCHORS-NEXT-DIFF
 (20 4 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (8 4 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 )
(ALEOBFT-DYNAMIC::LEMMA
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (122 122 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (115 49 (:REWRITE SET::IN-TAIL))
 (92 40 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (85 85 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (85 85 (:REWRITE NORMALIZE-ADDENDS))
 (66 35 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (46 37 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (45 30 (:REWRITE SIMPLIFY-SUMS-<))
 (45 8 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (40 40 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (35 35 (:REWRITE |(< (- x) (- y))|))
 (33 11 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (32 32 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (25 25 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (17 17 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (17 17 (:META META-INTEGERP-CORRECT))
 (15 5 (:REWRITE SET::NEVER-IN-EMPTY))
 (12 12 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (9 6 (:REWRITE |(< (+ c x) d)|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE |(integerp (* c x))|))
 (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-COMMIT-ANCHORS-NEXT-SAME)
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-COMMIT-ANCHORS-NEXT
 (136 34 (:REWRITE SET::IN-TAIL))
 (120 24 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (68 68 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (51 17 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (51 17 (:REWRITE SET::NEVER-IN-EMPTY))
 (48 48 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (48 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (48 30 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (48 30 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (48 24 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (30 30 (:REWRITE |(equal (- x) (- y))|))
 (30 10 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (20 20 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (12 12 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (12 12 (:REWRITE |(equal (- x) 0)|))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-NOT-NIL-OF-TIMER-EXPIRES-NEXT
 (8 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-TIMER-EXPIRES-NEXT
 (96 24 (:REWRITE SET::IN-TAIL))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 12 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (36 12 (:REWRITE SET::NEVER-IN-EMPTY))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (20 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE |(equal (- x) 0)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-OF-EVENT-NEXT
 (21 7 (:REWRITE ALEOBFT-DYNAMIC::LAST-ANCHOR-PRESENT-P-WHEN-INIT))
 (14 14 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::SYSTEM-INITP))
 (10 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 )
