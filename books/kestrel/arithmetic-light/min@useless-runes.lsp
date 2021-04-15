(MIN-WHEN-<=-1 (2 2
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (2 2 (:REWRITE DEFAULT-<-2))
               (2 2 (:REWRITE DEFAULT-<-1)))
(MIN-WHEN-<=-2 (19 19 (:TYPE-PRESCRIPTION MIN))
               (4 4
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (4 2 (:REWRITE DEFAULT-<-2))
               (4 2 (:REWRITE DEFAULT-<-1)))
(<-OF-MIN-ARG1 (24 12 (:REWRITE DEFAULT-<-1))
               (22 22
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (22 12 (:REWRITE DEFAULT-<-2))
               (11 11 (:TYPE-PRESCRIPTION MIN)))
(<-OF-MIN-ARG2 (22 11 (:REWRITE DEFAULT-<-2))
               (20 20
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (20 11 (:REWRITE DEFAULT-<-1))
               (11 11 (:TYPE-PRESCRIPTION MIN)))
