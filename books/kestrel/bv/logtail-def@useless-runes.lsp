(EXPT2$INLINE (30 30
                  (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
              (30 30
                  (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
              (6 4 (:REWRITE DEFAULT-<-1))
              (6 2
                 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
              (6 2
                 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
              (6 2
                 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
              (6 2
                 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
              (6 2 (:REWRITE FLOOR-WHEN-<))
              (4 4 (:REWRITE DEFAULT-<-2))
              (2 2
                 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
              (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER)))
(IFLOOR$INLINE (51 51
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
               (51 51
                   (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
               (4 2 (:REWRITE FLOOR-WHEN-<))
               (2 2
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
               (2 2
                  (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
               (2 2
                  (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
               (2 2
                  (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
               (2 2
                  (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
               (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
               (1 1 (:REWRITE DEFAULT-<-2))
               (1 1 (:REWRITE DEFAULT-<-1)))
(LOGTAIL$INLINE (34 34
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-NON-NEGATIVE))
                (34 34
                    (:TYPE-PRESCRIPTION FLOOR-TYPE-1-PART-1-BETTER))
                (17 17 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
                (14 2 (:REWRITE FLOOR-WHEN-<))
                (9 3
                   (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
                (6 4 (:REWRITE DEFAULT-<-2))
                (5 1 (:REWRITE DEFAULT-UNARY-/))
                (4 4 (:REWRITE DEFAULT-<-1))
                (3 1 (:REWRITE DEFAULT-*-2))
                (2 2
                   (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
                (2 2
                   (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
                (2 2
                   (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
                (2 2
                   (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
                (2 2 (:REWRITE FLOOR-MINUS-ERIC-BETTER))
                (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                (1 1 (:REWRITE DEFAULT-*-1)))
