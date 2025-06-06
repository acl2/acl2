(STR::PREFIX-LINES-AUX
 (128 7 (:DEFINITION LEN))
 (77 14 (:REWRITE LEN-WHEN-ATOM))
 (68 2 (:REWRITE NTH-WHEN-BIGGER))
 (59 43 (:REWRITE DEFAULT-+-2))
 (56 56 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (53 1 (:DEFINITION NTH))
 (49 43 (:REWRITE DEFAULT-+-1))
 (44 36 (:REWRITE DEFAULT-<-2))
 (44 36 (:REWRITE DEFAULT-<-1))
 (36 8 (:REWRITE DEFAULT-CDR))
 (32 20 (:REWRITE STR::CONSP-OF-EXPLODE))
 (29 29 (:REWRITE CONSP-BY-LEN))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (9 9 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 6 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (5 1 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 )
(STR::PREFIX-LINES)
(STR::CHARACTER-LISTP-OF-PREFIX-LINES-AUX
 (1945 60 (:REWRITE NTH-WHEN-BIGGER))
 (1448 87 (:DEFINITION LEN))
 (934 174 (:REWRITE LEN-WHEN-ATOM))
 (478 144 (:REWRITE DEFAULT-CDR))
 (400 400 (:REWRITE CONSP-BY-LEN))
 (313 191 (:REWRITE DEFAULT-+-2))
 (211 191 (:REWRITE DEFAULT-+-1))
 (162 162 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (151 78 (:REWRITE DEFAULT-<-2))
 (133 47 (:REWRITE DEFAULT-CAR))
 (112 78 (:REWRITE DEFAULT-<-1))
 (65 5 (:REWRITE COMMUTATIVITY-2-OF-+))
 (60 60 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (50 20 (:REWRITE FOLD-CONSTS-IN-+))
 (45 45 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 5 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (13 13 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (10 5 (:REWRITE UNICITY-OF-0))
 (8 8 (:REWRITE NATP-RW))
 (5 5 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (5 5 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
 (5 5 (:DEFINITION FIX))
 )
(STR::PREFIX-LINES
 (112 6 (:DEFINITION LEN))
 (95 1 (:DEFINITION STR::PREFIX-LINES-AUX))
 (70 12 (:REWRITE LEN-WHEN-ATOM))
 (67 1 (:DEFINITION CHAR))
 (55 1 (:REWRITE NTH-WHEN-BIGGER))
 (54 54 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (30 21 (:REWRITE STR::CONSP-OF-EXPLODE))
 (30 6 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE CONSP-BY-LEN))
 (26 1 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (15 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (9 1 (:REWRITE ZP-OPEN))
 (9 1 (:DEFINITION NTH))
 (7 1 (:REWRITE COMMUTATIVITY-OF-+))
 (6 6 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (6 6 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (5 1 (:REWRITE DEFAULT-CAR))
 (5 1 (:REWRITE |(< 0 (len x))|))
 (5 1 (:DEFINITION LNFIX$INLINE))
 (4 1 (:DEFINITION NFIX))
 (3 1 (:REWRITE UNICITY-OF-0))
 (2 2 (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (2 1 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION NFIX))
 )
(STR::STRINGP-OF-PREFIX-LINES
 (91 1 (:DEFINITION STR::PREFIX-LINES-AUX))
 (50 1 (:DEFINITION CHAR))
 (47 3 (:DEFINITION LEN))
 (37 1 (:REWRITE NTH-WHEN-BIGGER))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (29 6 (:REWRITE LEN-WHEN-ATOM))
 (22 22 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (19 1 (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-CHARACTER-LISTP))
 (18 18 (:REWRITE CONSP-BY-LEN))
 (15 9 (:REWRITE STR::CONSP-OF-EXPLODE))
 (15 1 (:DEFINITION CHARACTER-LISTP))
 (12 4 (:REWRITE DEFAULT-CDR))
 (12 1 (:REWRITE ZP-OPEN))
 (11 7 (:DEFINITION NOT))
 (10 5 (:REWRITE DEFAULT-+-2))
 (10 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 1 (:DEFINITION NTH))
 (9 1 (:REWRITE COMMUTATIVITY-OF-+))
 (8 1 (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-ATOM))
 (7 7 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (7 5 (:REWRITE DEFAULT-+-1))
 (7 1 (:DEFINITION LNFIX$INLINE))
 (6 2 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE STR::CONSP-OF-MAKE-CHARACTER-LIST))
 (6 1 (:DEFINITION NFIX))
 (5 1 (:REWRITE |(< 0 (len x))|))
 (4 1 (:REWRITE UNICITY-OF-0))
 (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 1 (:REWRITE NEGATIVE-WHEN-NATP))
 (3 1 (:REWRITE DEFAULT-<-2))
 (3 1 (:DEFINITION FIX))
 (2 2 (:TYPE-PRESCRIPTION MAKE-CHARACTER-LIST))
 (2 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 1 (:REWRITE REVERSE-REMOVAL))
 (2 1 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (2 1 (:REWRITE CHARACTER-LISTP-OF-CDR-WHEN-CHARACTER-LISTP))
 (1 1 (:TYPE-PRESCRIPTION NFIX))
 (1 1 (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE STR::CHARACTER-LISTP-OF-PREFIX-LINES-AUX))
 (1 1 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
 )
