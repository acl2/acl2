(BYTE-LISTP-OF-REVERSE-LIST
 (562 13 (:REWRITE CDR-OF-REVERSE-LIST))
 (488 8 (:DEFINITION BINARY-APPEND))
 (377 13 (:REWRITE CAR-OF-REVERSE-LIST))
 (260 260 (:TYPE-PRESCRIPTION LEN))
 (260 13 (:DEFINITION TAKE))
 (260 13 (:DEFINITION NTH))
 (208 26 (:REWRITE ZP-OPEN))
 (182 104 (:REWRITE DEFAULT-+-2))
 (130 26 (:DEFINITION LEN))
 (104 104 (:REWRITE DEFAULT-+-1))
 (104 26 (:REWRITE FOLD-CONSTS-IN-+))
 (75 75 (:REWRITE DEFAULT-CDR))
 (52 26 (:REWRITE DEFAULT-<-2))
 (47 10 (:DEFINITION TRUE-LISTP))
 (43 43 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (42 42 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (40 40 (:REWRITE DEFAULT-CAR))
 (40 5 (:REWRITE UNSIGNED-BYTE-P-OF-NTH))
 (36 7 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (32 7 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (26 26 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (21 21 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (21 5 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-CDR))
 (20 5 (:REWRITE UNSIGNED-BYTE-P-8-OF-NTH-WHEN-BYTE-LISTP))
 (13 13 (:REWRITE CONSP-OF-REVERSE-LIST))
 (12 12 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (12 12 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 )
(UNPACKBV-LITTLE)
(LEN-OF-UNPACKBV-LITTLE
 (13 1 (:DEFINITION LEN))
 (6 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 2 (:REWRITE CONSP-OF-UNPACKBV))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE UNPACKBV-WHEN-NOT-INTEGERP))
 (4 1 (:REWRITE DEFAULT-CDR))
 (3 3 (:TYPE-PRESCRIPTION UNPACKBV))
 (3 1 (:DEFINITION POSP))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(BYTE-LISTP-OF-UNPACKBV-LITTLE
 (4 1 (:REWRITE UNPACKBV-WHEN-ZP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE UNPACKBV-WHEN-NOT-INTEGERP))
 )