(ALL-> (2 2 (:REWRITE DEFAULT-CAR))
       (1 1 (:REWRITE DEFAULT-CDR)))
(ALL->-OF-CONS (10 10
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (10 5 (:REWRITE DEFAULT-<-2))
               (10 5 (:REWRITE DEFAULT-<-1))
               (3 3 (:REWRITE DEFAULT-CDR))
               (3 3 (:REWRITE DEFAULT-CAR)))
(ALL->-OF-NIL)
(ALL->-OF-CDR (2 2
                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
              (2 1 (:REWRITE DEFAULT-<-2))
              (2 1 (:REWRITE DEFAULT-<-1))
              (1 1 (:REWRITE DEFAULT-CAR)))
