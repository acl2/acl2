(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P)
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-NECC)
(ALEOBFT-STATIC::BOOLEANP-OF-SYSTEM-LAST-IS-EVEN-P)
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P
 (12 6 (:REWRITE SET::IN-TAIL))
 (10 5 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (7 5 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SETP-WHEN-POS-SETP))
 (3 1 (:REWRITE ALEOBFT-STATIC::SETP-WHEN-MESSAGE-SETP))
 (3 1 (:REWRITE ALEOBFT-STATIC::SETP-WHEN-CERTIFICATE-SETP))
 (3 1 (:REWRITE ALEOBFT-STATIC::SETP-WHEN-ADDRESS+POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::MESSAGE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::CERTIFICATE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::ADDRESS+POS-SETP))
 (1 1 (:REWRITE ALEOBFT-STATIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP
 (14 2 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (10 3 (:REWRITE SET::IN-TAIL))
 (3 3 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 (3 3 (:REWRITE-QUOTED-CONSTANT ALEOBFT-STATIC::CERTIFICATE-SET-FIX-UNDER-CERTIFICATE-SET-EQUIV))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (1 1 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-STATIC::BLOCK-LIST-FIX-UNDER-BLOCK-LIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-STATIC::ADDRESS+POS-SET-FIX-UNDER-ADDRESS+POS-SET-EQUIV))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-CREATE-CERTIFICATE-NEXT
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (6 2 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (6 1 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-RECEIVE-CERTIFICATE-NEXT
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (6 2 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (6 1 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-STORE-CERTIFICATE-NEXT
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (6 2 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (6 1 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-ADVANCE-ROUND-NEXT
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (6 2 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (6 1 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 )
(ALEOBFT-STATIC::LEMMA
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (28 28 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(integerp (* c x))|))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-COMMIT-ANCHORS-NEXT
 (82 36 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (62 16 (:REWRITE SET::IN-TAIL))
 (54 54 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (46 8 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (26 26 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (22 8 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (18 6 (:REWRITE SET::NEVER-IN-EMPTY))
 (12 4 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-TIMER-EXPIRES-NEXT
 (10 10 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 (9 3 (:REWRITE ALEOBFT-STATIC::VALIDATOR-INIT-WHEN-SYSTEM-INITP))
 (8 2 (:REWRITE SET::IN-TAIL))
 (6 2 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (6 1 (:REWRITE ALEOBFT-STATIC::IN-CORRECT-VALIDATOR-ADDRESESS-WHEN-GET-VALIDATOR-STATE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::GET-VALIDATOR-STATE))
 )
(ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-OF-EVENT-NEXT
 (3 1 (:REWRITE ALEOBFT-STATIC::SYSTEM-LAST-IS-EVEN-P-WHEN-SYSTEM-STATE-INITP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-STATIC::SYSTEM-STATE-INITP))
 )
