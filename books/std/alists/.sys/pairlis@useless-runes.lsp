(PAIRLIS$-WHEN-ATOM)
(PAIRLIS$-OF-CONS
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE PAIRLIS$-WHEN-ATOM))
 )
(LEN-OF-PAIRLIS$
 (14 7 (:REWRITE DEFAULT-+-2))
 (11 10 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(ALISTP-OF-PAIRLIS$
 (11 10 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-CDR))
 )
(STRIP-CARS-OF-PAIRLIS$
 (98 11 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (69 14 (:DEFINITION TRUE-LISTP))
 (57 57 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (56 55 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE DEFAULT-+-2))
 (25 24 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 )
(L0
 (32 4 (:REWRITE ZP-OPEN))
 (14 9 (:REWRITE DEFAULT-+-2))
 (13 12 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 7 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(STRIP-CDRS-OF-PAIRLIS$
 (145 9 (:REWRITE TAKE-OF-LEN-FREE))
 (35 19 (:REWRITE DEFAULT-+-2))
 (33 32 (:REWRITE DEFAULT-CDR))
 (24 3 (:REWRITE ZP-OPEN))
 (19 19 (:REWRITE DEFAULT-+-1))
 (17 16 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(PAIRLIS$-OF-LIST-FIX-LEFT
 (72 9 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (47 10 (:DEFINITION TRUE-LISTP))
 (43 43 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (34 34 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 )
(PAIRLIS$-OF-LIST-FIX-RIGHT)
(LIST-EQUIV-IMPLIES-EQUAL-PAIRLIS$-1
 (12 12 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 )
(LIST-EQUIV-IMPLIES-EQUAL-PAIRLIS$-2
 (12 12 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 (5 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 )
