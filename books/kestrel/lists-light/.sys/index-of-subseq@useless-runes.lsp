(INDEX-OF-SUBSEQ)
(TAKE-OF-LEN-AND-NTHCDR-OF-INDEX-OF-SUBSEQ
 (552 92 (:DEFINITION LEN))
 (442 16 (:REWRITE PREFIXP-WHEN-NOT-SHORTER))
 (316 12 (:REWRITE PREFIXP-WHEN-LONGER))
 (235 128 (:REWRITE DEFAULT-+-2))
 (228 16 (:REWRITE PREFIXP-WHEN-LEN-0))
 (156 132 (:REWRITE DEFAULT-CDR))
 (128 128 (:REWRITE DEFAULT-+-1))
 (80 40 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (64 34 (:REWRITE DEFAULT-<-2))
 (60 34 (:REWRITE DEFAULT-<-1))
 (48 18 (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
 (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (38 14 (:REWRITE DEFAULT-CAR))
 (30 10 (:DEFINITION TRUE-LIST-FIX))
 (16 16 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(INDEX-OF-SUBSEQ-SELF
 (22 1 (:REWRITE PREFIXP-WHEN-LONGER))
 (17 17 (:TYPE-PRESCRIPTION LEN))
 (15 3 (:DEFINITION LEN))
 (12 1 (:REWRITE PREFIXP-WHEN-LEN-0))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 (1 1 (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
 )
(<-OF-INDEX-OF-SUBSEQ-AND-LEN
 (185 9 (:REWRITE PREFIXP-WHEN-NOT-SHORTER))
 (185 9 (:REWRITE PREFIXP-WHEN-LONGER))
 (95 56 (:REWRITE DEFAULT-+-2))
 (72 9 (:REWRITE PREFIXP-WHEN-LEN-0))
 (56 56 (:REWRITE DEFAULT-+-1))
 (47 24 (:REWRITE DEFAULT-<-1))
 (43 24 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 (8 8 (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
 (4 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NOT-INDEX-OF-SUBSEQ-WHEN-OF-LEN-AND-LEN
 (26 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-+-1))
 (13 7 (:REWRITE DEFAULT-<-1))
 (12 7 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
 )