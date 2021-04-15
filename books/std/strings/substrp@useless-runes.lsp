(STR::SUBSTRP$INLINE (228 5 (:REWRITE SUBLISTP-WHEN-PREFIXP))
                     (186 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                     (120 3 (:REWRITE PREFIXP-WHEN-PREFIXP))
                     (76 4 (:DEFINITION LEN))
                     (38 8 (:REWRITE LEN-WHEN-ATOM))
                     (36 2
                         (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                     (32 18 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (23 23 (:TYPE-PRESCRIPTION LEN))
                     (22 22 (:REWRITE CONSP-BY-LEN))
                     (20 4 (:REWRITE DEFAULT-CDR))
                     (15 5 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                     (15 5 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                     (14 2 (:REWRITE LEN-WHEN-PREFIXP))
                     (13 3
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                     (13 3
                         (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                     (11 11 (:TYPE-PRESCRIPTION PREFIXP))
                     (8 4 (:REWRITE DEFAULT-+-2))
                     (6 6
                        (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                     (6 6
                        (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
                     (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                     (5 5 (:REWRITE SUBLISTP-COMPLETE))
                     (4 4
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (4 4 (:REWRITE DEFAULT-+-1))
                     (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
                     (4 2 (:REWRITE DEFAULT-<-2))
                     (4 2 (:REWRITE DEFAULT-<-1))
                     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 2))
                     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
                     (3 3
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                     (3 3
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                     (3 3
                        (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE)))
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-1)
(STR::STREQV-IMPLIES-EQUAL-SUBSTRP-2)
