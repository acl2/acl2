(CAR-MAKE-PARTITION-REC
 (9 5 (:REWRITE DEFAULT-CAR))
 (8 5 (:REWRITE DEFAULT-+-2))
 (8 5 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ZP-OPEN))
 )
(MAKE-PARTITION-REC-OPEN
 (25 18 (:REWRITE DEFAULT-+-1))
 (24 2 (:REWRITE COMMUTATIVITY-OF-+))
 (23 18 (:REWRITE DEFAULT-+-2))
 (14 2 (:REWRITE COMMUTATIVITY-2-OF-+))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 6 (:REWRITE FOLD-CONSTS-IN-+))
 (8 2 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(PARTITIONP-MAKE-PARTITION-REC
 (49 25 (:REWRITE DEFAULT-CDR))
 (17 13 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE MAKE-PARTITION-REC-OPEN))
 )
