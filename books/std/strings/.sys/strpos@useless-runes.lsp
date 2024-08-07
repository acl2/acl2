(STR::STRPOS-FAST
 (1001 9 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
 (895 47 (:DEFINITION LEN))
 (766 9 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (602 8 (:REWRITE LEN-OF-NTHCDR))
 (464 94 (:REWRITE LEN-WHEN-ATOM))
 (306 8 (:REWRITE CONSP-OF-NTHCDR))
 (265 52 (:REWRITE DEFAULT-CDR))
 (229 138 (:REWRITE STR::CONSP-OF-EXPLODE))
 (198 9 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (198 9 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (190 190 (:REWRITE CONSP-BY-LEN))
 (155 97 (:REWRITE DEFAULT-+-2))
 (155 5 (:DEFINITION NTHCDR))
 (112 78 (:REWRITE DEFAULT-<-1))
 (107 97 (:REWRITE DEFAULT-+-1))
 (104 78 (:REWRITE DEFAULT-<-2))
 (77 10 (:REWRITE NTHCDR-WHEN-ZP))
 (58 58 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (58 58 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (58 58 (:LINEAR LEN-WHEN-PREFIXP))
 (55 10 (:REWRITE NTHCDR-WHEN-ATOM))
 (52 52 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (33 33 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (29 29 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (20 4 (:REWRITE <-+-NEGATIVE-0-2))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (9 9 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (9 9 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (9 9 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(STR::L0
 (1139 12 (:REWRITE SUBLISTP-WHEN-PREFIXP))
 (429 41 (:DEFINITION LEN))
 (297 24 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (188 188 (:REWRITE CONSP-BY-LEN))
 (130 21 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (118 5 (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (110 55 (:REWRITE DEFAULT-+-2))
 (109 109 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (67 55 (:REWRITE DEFAULT-+-1))
 (46 2 (:LINEAR LISTPOS-UPPER-BOUND-WEAK))
 (45 5 (:REWRITE LEN-WHEN-PREFIXP))
 (30 15 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (30 10 (:REWRITE LISTPOS-WHEN-ATOM-RIGHT))
 (30 6 (:REWRITE COMMUTATIVITY-OF-+))
 (28 28 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (28 15 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (25 11 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
 (20 20 (:LINEAR LEN-WHEN-PREFIXP))
 (20 10 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
 (18 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (17 17 (:TYPE-PRESCRIPTION LISTPOS))
 (17 17 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (17 17 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (17 17 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (17 17 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (16 2 (:LINEAR LISTPOS-LOWER-BOUND-WEAK))
 (14 7 (:REWRITE DEFAULT-<-2))
 (14 7 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE SUBLISTP-COMPLETE))
 (12 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 2 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-1))
 (4 1 (:REWRITE LIST-EQUIV-OF-NIL-RIGHT))
 (3 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 (2 2 (:LINEAR LISTPOS-COMPLETE))
 (2 1 (:REWRITE |(< 0 (len x))|))
 (1 1 (:TYPE-PRESCRIPTION LIST-EQUIV))
 )
(STR::STRPOS-FAST-REMOVAL
 (20521 244 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
 (11461 97 (:REWRITE SUBLISTP-WHEN-PREFIXP))
 (10529 577 (:DEFINITION LEN))
 (5305 1154 (:REWRITE LEN-WHEN-ATOM))
 (5091 1101 (:REWRITE DEFAULT-+-2))
 (4025 732 (:REWRITE DEFAULT-CDR))
 (3257 14 (:REWRITE ACL2-NUMBERP-OF-LISTPOS))
 (2626 2626 (:REWRITE CONSP-BY-LEN))
 (2038 69 (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (1316 1101 (:REWRITE DEFAULT-+-1))
 (1144 1144 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (829 114 (:REWRITE NTHCDR-WHEN-ZP))
 (778 65 (:REWRITE LEN-WHEN-PREFIXP))
 (661 381 (:REWRITE DEFAULT-<-2))
 (660 46 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (599 114 (:REWRITE NTHCDR-WHEN-ATOM))
 (591 97 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
 (579 97 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
 (541 381 (:REWRITE DEFAULT-<-1))
 (525 115 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
 (428 19 (:REWRITE NATP-RW))
 (246 246 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (246 246 (:LINEAR LEN-WHEN-PREFIXP))
 (245 245 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (244 244 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (209 24 (:REWRITE <-+-NEGATIVE-0-1))
 (173 138 (:REWRITE DEFAULT-UNARY-MINUS))
 (127 127 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (97 97 (:REWRITE SUBLISTP-COMPLETE))
 (95 95 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (70 2 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
 (57 57 (:REWRITE OPEN-SMALL-NTHCDR))
 (46 46 (:TYPE-PRESCRIPTION LIST-EQUIV))
 (26 26 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 (13 13 (:REWRITE LISTPOS-COMPLETE))
 (12 3 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (7 7 (:LINEAR LISTPOS-COMPLETE))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(STR::STRPOS$INLINE
 (76 4 (:DEFINITION LEN))
 (48 8 (:REWRITE LEN-WHEN-ATOM))
 (24 14 (:REWRITE STR::CONSP-OF-EXPLODE))
 (20 4 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE CONSP-BY-LEN))
 (9 5 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (8 3 (:REWRITE LISTPOS-WHEN-ATOM-RIGHT))
 (8 3 (:REWRITE LISTPOS-WHEN-ATOM-LEFT))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(STR::STREQV-IMPLIES-EQUAL-STRPOS-1)
(STR::STREQV-IMPLIES-EQUAL-STRPOS-2)
