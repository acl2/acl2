(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (33 33 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (8 8 (:TYPE-PRESCRIPTION OBAG::EMPTYP))
 (7 3 (:REWRITE OBAG::BFIX-WHEN-EMPTYP))
 (7 1 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (6 2 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTYP))
 (3 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1 1 (:REWRITE SET::IN-SET))
 )
(OBAG::BEQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::BEQUIV-IS-AN-EQUIVALENCE)
(OBAG::BEQUIV-IMPLIES-EQUAL-BFIX-1)
(OBAG::BFIX-UNDER-BEQUIV)
(OBAG::EQUAL-OF-BFIX-1-FORWARD-TO-BEQUIV)
(OBAG::EQUAL-OF-BFIX-2-FORWARD-TO-BEQUIV)
(OBAG::BEQUIV-OF-BFIX-1-FORWARD)
(OBAG::BEQUIV-OF-BFIX-2-FORWARD)
