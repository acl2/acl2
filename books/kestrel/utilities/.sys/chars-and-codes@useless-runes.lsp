(CODE-CHAR-OF-CHAR-CODE-SIMPLE
 (20 2 (:REWRITE DEFAULT-CODE-CHAR))
 (8 4 (:LINEAR CHAR-CODE-LINEAR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(CHAR-CODE-OF-CODE-CHAR-SIMPLE
 (16 8 (:REWRITE DEFAULT-CHAR-CODE))
 (11 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
