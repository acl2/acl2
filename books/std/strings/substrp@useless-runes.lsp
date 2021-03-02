(STR::SUBSTRP$INLINE (198 3 (:REWRITE SUBLISTP-WHEN-PREFIXP))
                     (156 2 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                     (104 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
                     (76 4 (:DEFINITION LEN))
                     (38 8 (:REWRITE LEN-WHEN-ATOM))
                     (28 16 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (26 26 (:TYPE-PRESCRIPTION LEN))
                     (20 20 (:REWRITE CONSP-BY-LEN))
                     (20 4 (:REWRITE DEFAULT-CDR))
                     (12 12
                         (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                     (12 12
                         (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
                     (12 12 (:LINEAR LEN-WHEN-PREFIXP))
                     (12 2
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                     (12 2
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                     (8 4 (:REWRITE DEFAULT-+-2))
                     (8 3 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                     (8 3 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                     (6 6
                        (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                     (5 5 (:TYPE-PRESCRIPTION PREFIXP))
                     (4 4
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (4 4 (:REWRITE DEFAULT-+-1))
                     (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
                     (3 3 (:REWRITE SUBLISTP-COMPLETE))
                     (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                     (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                     (2 2
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                     (2 2
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-1)
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-2)
