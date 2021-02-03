(STR::SUBSTRP$INLINE (104 3 (:REWRITE SUBLISTP-WHEN-PREFIXP))
                     (83 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                     (38 2 (:DEFINITION LEN))
                     (24 4 (:REWRITE LEN-WHEN-ATOM))
                     (18 10 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (13 13 (:TYPE-PRESCRIPTION LEN))
                     (12 12 (:REWRITE CONSP-BY-LEN))
                     (10 2 (:REWRITE DEFAULT-CDR))
                     (8 3 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                     (8 3 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                     (6 6
                        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                     (6 6
                        (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
                     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                     (6 1
                        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                     (6 1
                        (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                     (4 4
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (4 2 (:REWRITE DEFAULT-+-2))
                     (3 3 (:REWRITE SUBLISTP-COMPLETE))
                     (3 3
                        (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                     (2 2 (:TYPE-PRESCRIPTION PREFIXP))
                     (2 2 (:REWRITE DEFAULT-+-1))
                     (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
                     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                     (1 1
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                     (1 1
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-1)
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-2)
