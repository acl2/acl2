(NTHCDR-OF-LEN
 (459 12 (:REWRITE NTHCDR-WHEN-ZP))
 (353 9 (:REWRITE NTHCDR-WHEN-LESS-THAN-LEN-UNDER-IFF))
 (234 16 (:REWRITE ZP-WHEN-GT-0))
 (199 16 (:REWRITE ZP-WHEN-INTEGERP))
 (152 9 (:REWRITE NFIX-WHEN-NATP))
 (100 10 (:REWRITE <-0-+-NEGATIVE-1))
 (98 49 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (78 32 (:REWRITE DEFAULT-CDR))
 (76 4 (:REWRITE NATP-WHEN-INTEGERP))
 (72 4 (:REWRITE NATP-WHEN-GTE-0))
 (61 61 (:META CANCEL_PLUS-LESSP-CORRECT))
 (54 54 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (54 54 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (54 54 (:LINEAR LEN-WHEN-PREFIXP))
 (48 27 (:REWRITE DEFAULT-<-2))
 (48 9 (:REWRITE NFIX-WHEN-NOT-NATP))
 (42 24 (:REWRITE DEFAULT-+-2))
 (40 4 (:REWRITE <-+-NEGATIVE-0-1))
 (39 27 (:REWRITE DEFAULT-<-1))
 (39 18 (:REWRITE LEN-WHEN-ATOM))
 (34 17 (:REWRITE |(< 0 (len x))|))
 (30 24 (:REWRITE DEFAULT-+-1))
 (27 27 (:LINEAR INDEX-OF-<-LEN))
 (24 6 (:REWRITE NEGATIVE-WHEN-NATP))
 (23 12 (:REWRITE NTHCDR-WHEN-ATOM))
 (17 17 (:TYPE-PRESCRIPTION NFIX))
 (16 4 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (11 11 (:TYPE-PRESCRIPTION ZP))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:REWRITE OPEN-SMALL-NTHCDR))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (2 2 (:LINEAR LISTPOS-COMPLETE))
 )
(NTHCDR-OF-LEN-FREE
 (11 1 (:DEFINITION LEN))
 (6 4 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (5 2 (:REWRITE LEN-WHEN-ATOM))
 (4 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(CDR-OF-NTHCDR
 (302 7 (:REWRITE NTHCDR-OF-LEN-FREE))
 (99 7 (:DEFINITION LEN))
 (93 6 (:REWRITE NTHCDR-WHEN-ZP))
 (84 13 (:REWRITE DEFAULT-CDR))
 (65 14 (:REWRITE LEN-WHEN-ATOM))
 (64 31 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (57 11 (:REWRITE ZP-WHEN-GT-0))
 (55 11 (:REWRITE ZP-WHEN-INTEGERP))
 (52 52 (:TYPE-PRESCRIPTION LEN))
 (52 1 (:REWRITE CONSP-OF-NTHCDR))
 (34 1 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (30 30 (:REWRITE CONSP-BY-LEN))
 (26 26 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (26 26 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (26 26 (:LINEAR LEN-WHEN-PREFIXP))
 (25 15 (:REWRITE DEFAULT-+-2))
 (25 6 (:DEFINITION NOT))
 (21 21 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (21 6 (:REWRITE NTHCDR-WHEN-ATOM))
 (18 18 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (17 17 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 15 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE <-0-+-NEGATIVE-1))
 (14 2 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (13 13 (:LINEAR INDEX-OF-<-LEN))
 (13 3 (:REWRITE NFIX-WHEN-NATP))
 (10 9 (:REWRITE DEFAULT-<-2))
 (10 9 (:REWRITE DEFAULT-<-1))
 (10 2 (:REWRITE |(< 0 (len x))|))
 (9 9 (:TYPE-PRESCRIPTION ZP))
 (8 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (7 7 (:REWRITE ZP-OPEN))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:LINEAR LISTPOS-COMPLETE))
 (4 4 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (2 2 (:REWRITE NATP-WHEN-INTEGERP))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (2 1 (:REWRITE NEGATIVE-WHEN-NATP))
 (1 1 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (1 1 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 )
(NTH-WHEN-INDEX-TOO-BIG)
(NTHCDR-UNDER-IFF-WHEN-TRUE-LISTP
 (1049 32 (:REWRITE NTHCDR-OF-LEN-FREE))
 (447 23 (:REWRITE NTHCDR-WHEN-ZP))
 (281 131 (:REWRITE LEN-WHEN-ATOM))
 (273 62 (:REWRITE ZP-WHEN-GT-0))
 (249 249 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (248 143 (:REWRITE DEFAULT-+-2))
 (246 34 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (237 155 (:META CANCEL_PLUS-LESSP-CORRECT))
 (230 62 (:REWRITE ZP-WHEN-INTEGERP))
 (184 181 (:REWRITE DEFAULT-CDR))
 (156 35 (:REWRITE NATP-WHEN-GTE-0))
 (155 50 (:REWRITE ZP-OPEN))
 (153 143 (:REWRITE DEFAULT-+-1))
 (138 12 (:REWRITE NATP-POSP--1))
 (129 97 (:REWRITE DEFAULT-<-2))
 (129 30 (:REWRITE <-0-+-NEGATIVE-1))
 (126 12 (:REWRITE POSP-REDEFINITION))
 (122 97 (:REWRITE DEFAULT-<-1))
 (117 6 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (73 73 (:TYPE-PRESCRIPTION NATP))
 (69 7 (:REWRITE NFIX-EQUAL-TO-NONZERO))
 (68 68 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (68 68 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (68 68 (:LINEAR LEN-WHEN-PREFIXP))
 (59 35 (:REWRITE NATP-WHEN-INTEGERP))
 (48 48 (:LINEAR LISTPOS-COMPLETE))
 (40 17 (:REWRITE NEGATIVE-WHEN-NATP))
 (40 10 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (34 34 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (34 34 (:LINEAR INDEX-OF-<-LEN))
 (24 6 (:REWRITE <-+-NEGATIVE-0-1))
 (23 23 (:REWRITE NATP-RW))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (15 15 (:REWRITE EQUAL-CONSTANT-+))
 (10 10 (:REWRITE CONSP-BY-LEN))
 (8 2 (:REWRITE |(equal 0 (len x))|))
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 6 (:REWRITE NFIX-EQUAL-TO-NONZERO-CONST))
 (6 6 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (6 2 (:DEFINITION ATOM))
 (4 4 (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
 )
(TRUE-LISTP-WHEN-CHARACTER-LISTP)
(CHARACTER-LISTP-OF-NTHCDR
 (1636 6 (:REWRITE CAR-OF-NTHCDR))
 (1039 7 (:DEFINITION NTH))
 (954 91 (:DEFINITION LEN))
 (657 14 (:REWRITE NTH-WHEN-INDEX-TOO-BIG))
 (606 259 (:REWRITE DEFAULT-CDR))
 (569 15 (:REWRITE NTHCDR-OF-LEN-FREE))
 (559 14 (:REWRITE NTH-WHEN-BIGGER))
 (504 14 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (447 432 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (435 182 (:REWRITE LEN-WHEN-ATOM))
 (370 9 (:REWRITE CONSP-OF-NTHCDR))
 (271 149 (:REWRITE DEFAULT-+-2))
 (249 13 (:REWRITE NTHCDR-WHEN-ZP))
 (191 28 (:REWRITE ZP-WHEN-INTEGERP))
 (174 53 (:REWRITE NFIX-WHEN-NATP))
 (171 111 (:REWRITE DEFAULT-<-1))
 (163 111 (:REWRITE DEFAULT-<-2))
 (158 158 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (158 158 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (158 158 (:LINEAR LEN-WHEN-PREFIXP))
 (154 28 (:REWRITE ZP-WHEN-GT-0))
 (153 149 (:REWRITE DEFAULT-+-1))
 (149 149 (:META CANCEL_PLUS-LESSP-CORRECT))
 (144 53 (:REWRITE NFIX-WHEN-NOT-NATP))
 (128 32 (:REWRITE <-0-+-NEGATIVE-1))
 (118 8 (:REWRITE CHARACTERP-NTH))
 (85 2 (:REWRITE NTHCDR-UNDER-IFF-WHEN-TRUE-LISTP))
 (82 82 (:TYPE-PRESCRIPTION NFIX))
 (79 79 (:LINEAR INDEX-OF-<-LEN))
 (69 69 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (56 18 (:REWRITE NATP-WHEN-GTE-0))
 (38 14 (:REWRITE NTH-WHEN-ATOM))
 (34 34 (:TYPE-PRESCRIPTION NATP))
 (33 33 (:REWRITE CONSP-BY-LEN))
 (30 10 (:REWRITE NATP-WHEN-INTEGERP))
 (29 29 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (28 8 (:REWRITE NEGATIVE-WHEN-NATP))
 (26 26 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (25 9 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (14 14 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (11 11 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (10 10 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (10 10 (:REWRITE EQUAL-CONSTANT-+))
 (10 10 (:LINEAR LISTPOS-COMPLETE))
 (9 9 (:REWRITE ZP-OPEN))
 (9 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP))
 (8 2 (:REWRITE <-0-+-NEGATIVE-2))
 (7 7 (:REWRITE NTH-WHEN-PREFIXP))
 (6 6 (:REWRITE NATP-RW))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 (1 1 (:REWRITE |(equal 0 (len x))|))
 )
