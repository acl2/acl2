(TRUE-LISTP-OF-SUBRANGE-TYPE-PRESCRIPTION)
(TRUE-LISTP-OF-SUBRANGE)
(SUBRANGE-OUT-OF-ORDER (57 2 (:REWRITE TAKE-DOES-NOTHING))
                       (18 1 (:REWRITE LEN-OF-NTHCDR))
                       (7 6 (:REWRITE DEFAULT-<-1))
                       (6 6 (:REWRITE DEFAULT-<-2))
                       (5 4 (:REWRITE DEFAULT-+-1))
                       (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                       (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                       (4 4 (:REWRITE DEFAULT-+-2))
                       (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG2))
                       (3 1 (:DEFINITION POSP))
                       (2 2
                          (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                       (2 2
                          (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                       (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                       (2 2
                          (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                       (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                       (1 1 (:TYPE-PRESCRIPTION POSP))
                       (1 1
                          (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                       (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                       (1 1
                          (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(SUBRANGE-OUT-OF-ORDER-CHEAP
     (57 2 (:REWRITE TAKE-DOES-NOTHING))
     (18 1 (:REWRITE LEN-OF-NTHCDR))
     (7 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE DEFAULT-<-2))
     (5 4 (:REWRITE DEFAULT-+-1))
     (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (4 4 (:REWRITE DEFAULT-+-2))
     (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG2))
     (3 1 (:DEFINITION POSP))
     (2 2
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (2 2
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (1 1
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(CAR-OF-SUBRANGE (30 3 (:REWRITE DEFAULT-CAR))
                 (24 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
                 (12 1 (:REWRITE TAKE-DOES-NOTHING))
                 (11 9 (:REWRITE DEFAULT-<-2))
                 (11 5
                     (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                 (10 9 (:REWRITE DEFAULT-<-1))
                 (8 4 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
                 (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                 (4 4 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
                 (3 3
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (3 3
                    (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                 (2 2 (:TYPE-PRESCRIPTION ZP))
                 (1 1
                    (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                 (1 1
                    (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                 (1 1 (:REWRITE DEFAULT-+-2))
                 (1 1 (:REWRITE DEFAULT-+-1))
                 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                 (1 1
                    (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(CDR-OF-SUBRANGE (194 5 (:REWRITE TAKE-DOES-NOTHING))
                 (88 4 (:REWRITE LEN-OF-NTHCDR))
                 (65 2 (:REWRITE DEFAULT-CDR))
                 (62 5
                     (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                 (61 1 (:REWRITE LEN-OF-CDR))
                 (45 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
                 (30 21 (:REWRITE DEFAULT-+-2))
                 (25 21 (:REWRITE DEFAULT-+-1))
                 (23 17 (:REWRITE DEFAULT-<-1))
                 (22 17 (:REWRITE DEFAULT-<-2))
                 (18 10 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                 (16 4 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                 (12 1 (:REWRITE CONSP-OF-NTHCDR))
                 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
                 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                 (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                 (5 5
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (4 4
                    (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
                 (3 3
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                 (3 3
                    (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                 (3 1 (:DEFINITION POSP))
                 (2 2 (:TYPE-PRESCRIPTION ZP))
                 (2 2
                    (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                 (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                 (1 1 (:TYPE-PRESCRIPTION POSP))
                 (1 1 (:REWRITE ZP-OPEN))
                 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
                 (1 1
                    (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT)))
(NTHCDR-OF-SUBRANGE (74 4 (:REWRITE TAKE-DOES-NOTHING))
                    (38 1 (:REWRITE LEN-OF-NTHCDR))
                    (19 17 (:REWRITE DEFAULT-+-2))
                    (18 17 (:REWRITE DEFAULT-+-1))
                    (12 11 (:REWRITE DEFAULT-<-1))
                    (11 11 (:REWRITE DEFAULT-<-2))
                    (8 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                    (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                    (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
                    (6 6
                       (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                    (6 6 (:REWRITE +-COMBINE-CONSTANTS))
                    (6 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                    (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                    (5 1 (:DEFINITION POSP))
                    (2 2
                       (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                    (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                    (2 2
                       (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                    (2 2
                       (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                    (2 2
                       (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                    (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (1 1 (:TYPE-PRESCRIPTION POSP))
                    (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                    (1 1
                       (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(CONSP-OF-SUBRANGE (6 6 (:REWRITE DEFAULT-<-2))
                   (6 6 (:REWRITE DEFAULT-<-1))
                   (1 1 (:REWRITE DEFAULT-+-2))
                   (1 1 (:REWRITE DEFAULT-+-1))
                   (1 1
                      (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(SUBRANGE-OPENER (7 3 (:REWRITE SUBRANGE-OUT-OF-ORDER))
                 (4 4 (:REWRITE DEFAULT-<-2))
                 (4 4 (:REWRITE DEFAULT-<-1))
                 (4 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
                 (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
                 (3 3
                    (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
                 (2 2 (:TYPE-PRESCRIPTION ZP))
                 (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
                 (2 2 (:REWRITE DEFAULT-+-2))
                 (2 2 (:REWRITE DEFAULT-+-1))
                 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                 (1 1
                    (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(SUBRANGE-IFF (12 1 (:REWRITE TAKE-DOES-NOTHING))
              (10 10 (:REWRITE DEFAULT-<-2))
              (10 10 (:REWRITE DEFAULT-<-1))
              (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
              (3 1 (:DEFINITION POSP))
              (2 2 (:REWRITE DEFAULT-+-2))
              (2 2 (:REWRITE DEFAULT-+-1))
              (2 2
                 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
              (1 1 (:TYPE-PRESCRIPTION POSP))
              (1 1
                 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
              (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
              (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
              (1 1
                 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
              (1 1
                 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
              (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
              (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
              (1 1
                 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
              (1 1
                 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(LEN-OF-SUBRANGE (10 10 (:REWRITE DEFAULT-<-2))
                 (10 10 (:REWRITE DEFAULT-<-1))
                 (10 10 (:REWRITE DEFAULT-+-2))
                 (10 10 (:REWRITE DEFAULT-+-1))
                 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                 (2 2
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
                 (1 1 (:REWRITE +-COMBINE-CONSTANTS)))
(SUBRANGE-SAME (59 2 (:REWRITE TAKE-DOES-NOTHING))
               (22 1 (:REWRITE LEN-OF-NTHCDR))
               (7 6 (:REWRITE DEFAULT-<-1))
               (7 6 (:REWRITE DEFAULT-+-2))
               (7 6 (:REWRITE DEFAULT-+-1))
               (6 6 (:REWRITE DEFAULT-<-2))
               (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
               (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
               (4 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
               (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
               (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
               (3 1 (:DEFINITION POSP))
               (2 2 (:TYPE-PRESCRIPTION ZP))
               (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
               (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
               (2 2
                  (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
               (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
               (1 1 (:TYPE-PRESCRIPTION POSP))
               (1 1
                  (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
               (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
               (1 1 (:REWRITE FOLD-CONSTS-IN-+))
               (1 1
                  (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
               (1 1
                  (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
               (1 1
                  (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
               (1 1 (:REWRITE +-COMBINE-CONSTANTS)))
(SUBRANGE-OF-0)
(SUBRANGE-IS-ALL)
(SUBRANGE-OF-TRUE-LIST-FIX)
(TAKE-OF-NTHCDR-BECOMES-SUBRANGE
     (60 3 (:REWRITE TAKE-DOES-NOTHING))
     (22 1 (:REWRITE LEN-OF-NTHCDR))
     (9 8 (:REWRITE DEFAULT-+-2))
     (9 8 (:REWRITE DEFAULT-+-1))
     (8 7 (:REWRITE DEFAULT-<-1))
     (7 7 (:REWRITE DEFAULT-<-2))
     (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
     (3 1 (:DEFINITION POSP))
     (2 2
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE FOLD-CONSTS-IN-+))
     (1 1
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (1 1
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (1 1 (:REWRITE +-COMBINE-CONSTANTS)))
(TAKE-OF-SUBRANGE-GEN (121 5 (:REWRITE TAKE-DOES-NOTHING))
                      (44 2 (:REWRITE LEN-OF-NTHCDR))
                      (23 21 (:REWRITE DEFAULT-+-2))
                      (23 21 (:REWRITE DEFAULT-+-1))
                      (15 13 (:REWRITE DEFAULT-<-1))
                      (13 13 (:REWRITE DEFAULT-<-2))
                      (10 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                      (8 2 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                      (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                      (6 6 (:REWRITE +-COMBINE-CONSTANTS))
                      (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                      (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                      (4 4
                         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                      (3 3
                         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                      (3 3
                         (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                      (3 3
                         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                      (3 1 (:DEFINITION POSP))
                      (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
                      (2 2
                         (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                      (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                      (1 1 (:TYPE-PRESCRIPTION POSP)))
(SUBRANGE-OUT-OF-ORDER-OR-SINGLETON
     (9 7 (:REWRITE DEFAULT-<-2))
     (7 7 (:REWRITE DEFAULT-<-1))
     (6 3 (:REWRITE NTH-WHEN-ZP-CHEAP))
     (3 3 (:TYPE-PRESCRIPTION ZP))
     (3 3 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
     (3 3 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
     (3 1 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (1 1
        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP)))
(NTH-OF-SUBRANGE (12 1 (:REWRITE TAKE-DOES-NOTHING))
                 (7 7 (:REWRITE DEFAULT-<-2))
                 (7 7 (:REWRITE DEFAULT-<-1))
                 (4 4 (:REWRITE DEFAULT-+-2))
                 (4 4 (:REWRITE DEFAULT-+-1))
                 (4 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
                 (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
                 (3 3
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                 (2 2 (:TYPE-PRESCRIPTION ZP))
                 (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
                 (2 2
                    (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                 (1 1
                    (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                 (1 1
                    (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
                 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                 (1 1
                    (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(SUBRANGE-UP-TO-END-BECOMES-NTHCDR
     (67 3
         (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
     (40 1 (:REWRITE TRUE-LISTP-OF-NTHCDR-3))
     (34 2 (:DEFINITION TRUE-LISTP))
     (20 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (9 7 (:REWRITE DEFAULT-<-2))
     (9 7 (:REWRITE DEFAULT-<-1))
     (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (3 3
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (3 1 (:DEFINITION POSP))
     (3 1 (:DEFINITION NFIX))
     (2 2
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (2 2
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (1 1 (:TYPE-PRESCRIPTION POSP)))
(SUBRANGE-UP-TO-END-BECOMES-NTHCDR-STRONG
     (47 2
         (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
     (40 1 (:REWRITE TRUE-LISTP-OF-NTHCDR-3))
     (17 1 (:DEFINITION TRUE-LISTP))
     (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (8 6 (:REWRITE DEFAULT-<-1))
     (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (7 6 (:REWRITE DEFAULT-<-2))
     (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (4 2
        (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (3 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (3 1 (:DEFINITION POSP))
     (3 1 (:DEFINITION NFIX))
     (2 2
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (2 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-+-1))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (1 1
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT)))
(APPEND-OF-SUBRANGE-AND-SUBRANGE-ADJACENT
     (27 26 (:REWRITE DEFAULT-<-2))
     (26 26 (:REWRITE DEFAULT-<-1))
     (23 23 (:REWRITE DEFAULT-+-2))
     (23 23 (:REWRITE DEFAULT-+-1))
     (19 5
         (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
     (9 9 (:REWRITE FOLD-CONSTS-IN-+))
     (7 5 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (5 5
        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
     (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (2 2
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (2 1
        (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(SUBRANGE-OF-1-AND-CONS (3 3 (:REWRITE DEFAULT-<-2))
                        (3 3 (:REWRITE DEFAULT-<-1))
                        (2 2 (:REWRITE DEFAULT-+-2))
                        (2 2 (:REWRITE DEFAULT-+-1)))
(EQUAL-OF-CDR-AND-SUBRANGE-SAME
     (41 32 (:REWRITE DEFAULT-<-2))
     (41 9
         (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (38 38 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (36 13 (:REWRITE DEFAULT-CDR))
     (34 2 (:REWRITE SUBRANGE-IS-ALL))
     (32 32 (:REWRITE DEFAULT-<-1))
     (23 16 (:REWRITE DEFAULT-+-2))
     (23 7
         (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
     (22 3 (:REWRITE LEN-OF-CDR))
     (16 16 (:REWRITE DEFAULT-+-1))
     (15 15
         (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (15 5 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (14 2 (:REWRITE TAKE-DOES-NOTHING))
     (14 2
         (:REWRITE SUBRANGE-UP-TO-END-BECOMES-NTHCDR))
     (5 5
        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
     (5 5
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (5 5
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (5 1 (:REWRITE EQUAL-OF-LEN-AND-0))
     (3 3
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (2 2
        (:REWRITE <-OF-+-COMBINE-CONSTANTS-1)))
(EQUAL-OF-SUBRANGE-OPENER-HELPER
     (67 19
         (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
     (59 56 (:REWRITE DEFAULT-<-2))
     (56 56 (:REWRITE DEFAULT-<-1))
     (51 19 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (28 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (24 13 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
     (23 13 (:REWRITE NTH-WHEN-ZP-CHEAP))
     (19 19
         (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
     (17 17 (:REWRITE DEFAULT-+-2))
     (17 17 (:REWRITE DEFAULT-+-1))
     (13 13 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
     (10 10 (:TYPE-PRESCRIPTION ZP))
     (10 10
         (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (9 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (9 9
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (7 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (3 3
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (2 2 (:REWRITE FOLD-CONSTS-IN-+))
     (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (2 2 (:REWRITE +-COMBINE-CONSTANTS)))
(EQUAL-OF-SUBRANGE-OPENER)
(EQUAL-SUBRANGE-NTHCDR-REWRITE
     (54 2 (:DEFINITION NTHCDR))
     (27 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (25 3 (:REWRITE DEFAULT-CDR))
     (18 4 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (13 1 (:DEFINITION TRUE-LISTP))
     (11 3 (:DEFINITION POSP))
     (9 6 (:REWRITE DEFAULT-<-2))
     (8 6 (:REWRITE DEFAULT-+-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE DEFAULT-+-1))
     (6 2 (:REWRITE COMMUTATIVITY-OF-+))
     (6 2
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (4 4
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (4 4 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (3 3 (:TYPE-PRESCRIPTION POSP))
     (3 3 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (3 3
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(TAKE-OF-CDR-BECOMES-SUBRANGE
     (28 1 (:REWRITE TAKE-DOES-NOTHING))
     (21 1 (:REWRITE LEN-OF-CDR))
     (18 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (17 17 (:TYPE-PRESCRIPTION LEN))
     (14 1 (:REWRITE EQUAL-OF-LEN-AND-0))
     (10 1 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (5 4 (:REWRITE DEFAULT-+-2))
     (4 4 (:REWRITE DEFAULT-+-1))
     (4 3 (:REWRITE DEFAULT-<-2))
     (4 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (3 3 (:REWRITE DEFAULT-<-1))
     (3 1
        (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
     (3 1 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (2 2
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (1 1
        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER)))
(CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER (2 2 (:REWRITE DEFAULT-<-2))
                                     (2 2 (:REWRITE DEFAULT-<-1))
                                     (2 2 (:REWRITE DEFAULT-+-2))
                                     (2 2 (:REWRITE DEFAULT-+-1)))
(SUBRANGE-WHEN-START-IS-NEGATIVE
     (275 8 (:REWRITE TAKE-DOES-NOTHING))
     (204 12 (:REWRITE LEN-OF-CDR))
     (188 22 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (124 10 (:REWRITE EQUAL-OF-LEN-AND-0))
     (90 6 (:REWRITE DEFAULT-CAR))
     (50 6 (:REWRITE DEFAULT-CDR))
     (45 45 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (43 7
         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (35 20 (:REWRITE DEFAULT-+-2))
     (34 18
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (31 17 (:REWRITE DEFAULT-<-2))
     (22 22
         (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (20 20 (:REWRITE DEFAULT-+-1))
     (18 17 (:REWRITE DEFAULT-<-1))
     (16 16
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 14 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (5 5
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (4 4
        (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
     (2 2
        (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
     (2 2
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (2 1
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN)))
(SUBRANGE-WHEN-END-IS-NEGATIVE
     (12 1 (:REWRITE TAKE-DOES-NOTHING))
     (2 2
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (2 1 (:REWRITE DEFAULT-<-1))
     (1 1 (:REWRITE ZP-OPEN))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (1 1
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-+-2))
     (1 1 (:REWRITE DEFAULT-+-1)))
(CONS-NTH-ONTO-SUBRANGE (13 3
                            (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
                        (10 9 (:REWRITE DEFAULT-<-1))
                        (9 9 (:REWRITE DEFAULT-<-2))
                        (5 3 (:REWRITE SUBRANGE-OUT-OF-ORDER))
                        (4 4 (:REWRITE DEFAULT-+-2))
                        (4 4 (:REWRITE DEFAULT-+-1))
                        (4 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
                        (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
                        (3 3
                           (:REWRITE SUBRANGE-WHEN-START-IS-NEGATIVE))
                        (3 3
                           (:REWRITE SUBRANGE-WHEN-END-IS-NEGATIVE))
                        (3 3
                           (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
                        (2 2 (:TYPE-PRESCRIPTION ZP))
                        (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
                        (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                        (2 2
                           (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                        (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                        (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                        (1 1
                           (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                        (1 1
                           (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(SUBRANGE-OF-TAKE (73 5 (:REWRITE TAKE-DOES-NOTHING))
                  (22 1 (:REWRITE LEN-OF-NTHCDR))
                  (13 12 (:REWRITE DEFAULT-<-1))
                  (13 12 (:REWRITE DEFAULT-+-2))
                  (13 12 (:REWRITE DEFAULT-+-1))
                  (12 12 (:REWRITE DEFAULT-<-2))
                  (6 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                  (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                  (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                  (4 4 (:REWRITE +-COMBINE-CONSTANTS))
                  (4 4
                     (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                  (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                  (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                  (3 1 (:DEFINITION POSP))
                  (2 2
                     (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                  (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                  (2 2
                     (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                  (2 2
                     (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                  (2 2
                     (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                  (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                  (1 1 (:TYPE-PRESCRIPTION POSP)))
(SUBRANGE-OF-CONS (185 6 (:REWRITE TAKE-DOES-NOTHING))
                  (74 2 (:REWRITE LEN-OF-NTHCDR))
                  (24 19 (:REWRITE DEFAULT-+-2))
                  (21 19 (:REWRITE DEFAULT-+-1))
                  (17 3 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                  (15 13 (:REWRITE DEFAULT-<-1))
                  (13 13 (:REWRITE DEFAULT-<-2))
                  (13 9 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                  (12 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                  (11 3 (:DEFINITION POSP))
                  (11 1 (:REWRITE EQUAL-OF-+-AND-+-CANCEL-1))
                  (10 10
                      (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                  (8 8 (:REWRITE FOLD-CONSTS-IN-+))
                  (8 2 (:REWRITE COMMUTATIVITY-OF-+))
                  (6 2
                     (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                  (5 1 (:REWRITE LEN-OF-CONS))
                  (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
                  (4 4
                     (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                  (4 3
                     (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                  (3 3 (:TYPE-PRESCRIPTION POSP))
                  (3 3 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                  (3 3
                     (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                  (3 3
                     (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                  (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
                  (2 2 (:REWRITE ZP-OPEN)))
(SUBRANGE-OF-CONS-CONSTANT-VERSION)
(SUBRANGE-TO-END-BECOMES-NTHCDR
     (6 5 (:REWRITE DEFAULT-+-2))
     (6 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (6 1 (:DEFINITION TRUE-LISTP))
     (5 5 (:REWRITE DEFAULT-+-1))
     (5 4 (:REWRITE DEFAULT-<-1))
     (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (3 1 (:REWRITE DEFAULT-CDR))
     (3 1 (:DEFINITION POSP))
     (2 2
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (2 2
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (2 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (1 1
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
     (1 1
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP)))
(CONS-NTH-ONTO-SUBRANGE-ALT
     (73 3
         (:REWRITE SUBRANGE-TO-END-BECOMES-NTHCDR))
     (62 62 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (48 6
         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (26 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
     (19 15
         (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (13 12 (:REWRITE DEFAULT-<-2))
     (13 3
         (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
     (12 12 (:REWRITE DEFAULT-<-1))
     (10 1 (:REWRITE DEFAULT-CDR))
     (10 1 (:REWRITE DEFAULT-CAR))
     (9 7 (:REWRITE DEFAULT-+-2))
     (7 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (7 7 (:REWRITE DEFAULT-+-1))
     (6 3
        (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
     (5 3 (:REWRITE SUBRANGE-OUT-OF-ORDER))
     (4 4
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (4 2 (:REWRITE NTH-WHEN-ZP-CHEAP))
     (4 2 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
     (4 2 (:DEFINITION FIX))
     (3 3
        (:REWRITE SUBRANGE-WHEN-START-IS-NEGATIVE))
     (3 3
        (:REWRITE SUBRANGE-WHEN-END-IS-NEGATIVE))
     (3 3
        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
     (3 3
        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
     (2 2 (:TYPE-PRESCRIPTION ZP))
     (2 2 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
     (2 2
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
     (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
     (1 1
        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT)))
(NTHCDR-OF-TAKE-BECOMES-SUBRANGE
     (162 5 (:REWRITE TAKE-DOES-NOTHING))
     (66 3 (:REWRITE LEN-OF-NTHCDR))
     (21 18 (:REWRITE DEFAULT-<-1))
     (18 18 (:REWRITE DEFAULT-<-2))
     (14 11 (:REWRITE DEFAULT-+-2))
     (14 11 (:REWRITE DEFAULT-+-1))
     (14 8 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (11 3 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
     (6 2 (:DEFINITION POSP))
     (4 4
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (3 3
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (3 3 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (3 3
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:TYPE-PRESCRIPTION POSP)))
(SUBRANGE-SPLIT-TOP (156 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
                    (115 3 (:REWRITE DEFAULT-CDR))
                    (110 2 (:REWRITE LEN-OF-NTHCDR))
                    (106 10
                         (:REWRITE SUBRANGE-TO-END-BECOMES-NTHCDR))
                    (98 83 (:REWRITE DEFAULT-<-2))
                    (93 83 (:REWRITE DEFAULT-+-2))
                    (87 83 (:REWRITE DEFAULT-<-1))
                    (83 83 (:REWRITE DEFAULT-+-1))
                    (73 21
                        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                    (36 4 (:REWRITE ASSOCIATIVITY-OF-+))
                    (27 15
                        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                    (23 23 (:REWRITE FOLD-CONSTS-IN-+))
                    (23 23 (:REWRITE +-COMBINE-CONSTANTS))
                    (23 19 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                    (21 7 (:REWRITE SUBRANGE-OUT-OF-ORDER))
                    (20 18 (:REWRITE DEFAULT-UNARY-MINUS))
                    (20 1 (:REWRITE TAKE-DOES-NOTHING))
                    (17 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                    (13 13
                        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                    (13 13
                        (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                    (13 10
                        (:REWRITE SUBRANGE-WHEN-END-IS-NEGATIVE))
                    (13 8 (:REWRITE NTH-WHEN-ZP-CHEAP))
                    (10 10
                        (:REWRITE SUBRANGE-WHEN-START-IS-NEGATIVE))
                    (9 9
                       (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                    (9 8 (:REWRITE NTH-WHEN-NOT-CONSP-CHEAP))
                    (9 8 (:REWRITE NTH-WHEN-<=-LEN-CHEAP))
                    (7 7
                       (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
                    (7 3
                       (:REWRITE SUBRANGE-UP-TO-END-BECOMES-NTHCDR))
                    (5 5 (:TYPE-PRESCRIPTION ZP))
                    (5 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                    (3 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                    (3 1 (:DEFINITION POSP))
                    (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
                    (2 2
                       (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                    (2 1
                       (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                    (2 1
                       (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                    (1 1 (:TYPE-PRESCRIPTION POSP))
                    (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN)))
(APPEND-OF-TAKE-AND-SUBRANGE
     (131 6 (:REWRITE TAKE-DOES-NOTHING))
     (44 2 (:REWRITE LEN-OF-NTHCDR))
     (20 18 (:REWRITE DEFAULT-<-1))
     (18 18 (:REWRITE DEFAULT-<-2))
     (14 12 (:REWRITE DEFAULT-+-2))
     (14 12 (:REWRITE DEFAULT-+-1))
     (11 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
     (10 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
     (8 2 (:REWRITE <-OF-+-OF---AND-0-ARG1))
     (6 6
        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
     (6 2 (:DEFINITION POSP))
     (4 4 (:REWRITE FOLD-CONSTS-IN-+))
     (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
     (4 4
        (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
     (4 4 (:REWRITE +-COMBINE-CONSTANTS))
     (3 3
        (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
     (3 3
        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
     (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (2 2 (:TYPE-PRESCRIPTION POSP))
     (2 2
        (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
     (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
     (2 1
        (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP)))
(SUBRANGE-OF-APPEND-LEMMA (896 23 (:REWRITE TAKE-DOES-NOTHING))
                          (380 10 (:REWRITE LEN-OF-NTHCDR))
                          (140 104 (:REWRITE DEFAULT-<-2))
                          (107 14 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                          (98 74 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                          (73 12 (:DEFINITION POSP))
                          (67 44 (:REWRITE DEFAULT-UNARY-MINUS))
                          (66 4 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
                          (58 10 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                          (35 35 (:REWRITE FOLD-CONSTS-IN-+))
                          (35 35 (:REWRITE +-COMBINE-CONSTANTS))
                          (19 19 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                          (19 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
                          (18 18
                              (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                          (15 15
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
                          (14 14
                              (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                          (14 14
                              (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                          (12 12 (:TYPE-PRESCRIPTION POSP))
                          (12 4
                              (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
                          (4 4
                             (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                          (4 4 (:DEFINITION TRUE-LISTP))
                          (3 3
                             (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                          (3 1 (:REWRITE DEFAULT-CAR))
                          (2 2 (:REWRITE EQUAL-OF---AND-CONSTANT))
                          (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER)))
(SUBRANGE-OF-CDR (109 4 (:REWRITE TAKE-DOES-NOTHING))
                 (32 1 (:REWRITE LEN-OF-NTHCDR))
                 (21 1 (:REWRITE LEN-OF-CDR))
                 (19 17 (:REWRITE DEFAULT-+-2))
                 (18 17 (:REWRITE DEFAULT-+-1))
                 (18 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
                 (14 1 (:REWRITE EQUAL-OF-LEN-AND-0))
                 (13 9 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                 (12 6
                     (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                 (11 10 (:REWRITE DEFAULT-<-2))
                 (11 10 (:REWRITE DEFAULT-<-1))
                 (11 2 (:REWRITE DEFAULT-CDR))
                 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
                 (6 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                 (5 5
                    (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
                 (4 4
                    (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                 (4 4
                    (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                 (2 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                 (2 2
                    (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                 (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                 (2 2
                    (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER)))
(SUBRANGE-OF-APPEND-IRREL (228 9
                               (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
                          (173 7 (:REWRITE TRUE-LISTP-OF-NTHCDR-3))
                          (144 144 (:TYPE-PRESCRIPTION TRUE-LISTP))
                          (87 81 (:REWRITE DEFAULT-<-2))
                          (85 81 (:REWRITE DEFAULT-<-1))
                          (80 8 (:DEFINITION TRUE-LISTP))
                          (57 16 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                          (56 56 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                          (46 19 (:REWRITE CONSP-FROM-LEN-CHEAP))
                          (38 38 (:REWRITE DEFAULT-+-2))
                          (38 38 (:REWRITE DEFAULT-+-1))
                          (34 2 (:REWRITE EQUAL-OF-LEN-AND-0))
                          (33 8 (:DEFINITION POSP))
                          (22 22
                              (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                          (22 8 (:REWRITE DEFAULT-CDR))
                          (19 19
                              (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                          (17 17 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                          (12 12
                              (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                          (12 12
                              (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                          (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
                          (12 6
                              (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                          (11 11 (:REWRITE FOLD-CONSTS-IN-+))
                          (11 11 (:REWRITE +-COMBINE-CONSTANTS))
                          (8 8 (:TYPE-PRESCRIPTION POSP))
                          (8 8 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                          (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
                          (2 2
                             (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT)))
(SUBRANGE-OF-APPEND-LEMMA2 (103 1 (:REWRITE EQUAL-OF-+-AND-+-CANCEL-1))
                           (82 40 (:REWRITE DEFAULT-+-2))
                           (65 40 (:REWRITE DEFAULT-+-1))
                           (54 41 (:REWRITE DEFAULT-<-2))
                           (50 41 (:REWRITE DEFAULT-<-1))
                           (42 39 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                           (30 3 (:DEFINITION TRUE-LISTP))
                           (20 14 (:REWRITE DEFAULT-UNARY-MINUS))
                           (18 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
                           (15 3 (:REWRITE DEFAULT-CDR))
                           (14 7
                               (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                           (11 11
                               (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                           (9 9 (:REWRITE FOLD-CONSTS-IN-+))
                           (9 9 (:REWRITE +-COMBINE-CONSTANTS))
                           (9 6
                              (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                           (7 7 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                           (7 7
                              (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                           (7 7
                              (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                           (6 6
                              (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                           (6 6
                              (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                           (3 3
                              (:REWRITE <-OF-+-COMBINE-CONSTANTS-1)))
(SUBRANGE-OF-APPEND (449 15
                         (:REWRITE SUBRANGE-TO-END-BECOMES-NTHCDR))
                    (276 34
                         (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                    (109 85 (:REWRITE DEFAULT-<-2))
                    (95 95
                        (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                    (95 68 (:REWRITE DEFAULT-+-2))
                    (89 85 (:REWRITE DEFAULT-<-1))
                    (88 8 (:REWRITE SUBRANGE-OF-APPEND-LEMMA2))
                    (77 4
                        (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
                    (76 70 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                    (69 68 (:REWRITE DEFAULT-+-1))
                    (63 63 (:TYPE-PRESCRIPTION TRUE-LISTP))
                    (63 12
                        (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
                    (61 5 (:REWRITE TAKE-DOES-NOTHING))
                    (58 3 (:REWRITE TRUE-LISTP-OF-NTHCDR-3))
                    (54 6 (:DEFINITION TRUE-LISTP))
                    (50 10 (:REWRITE SUBRANGE-OUT-OF-ORDER))
                    (48 2 (:REWRITE SUBRANGE-IS-ALL))
                    (47 15
                        (:REWRITE SUBRANGE-WHEN-END-IS-NEGATIVE))
                    (39 11
                        (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                    (27 21 (:REWRITE DEFAULT-UNARY-MINUS))
                    (25 4 (:REWRITE LEN-OF-APPEND))
                    (24 24
                        (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                    (21 5 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                    (20 20 (:REWRITE FOLD-CONSTS-IN-+))
                    (20 20 (:REWRITE +-COMBINE-CONSTANTS))
                    (18 6 (:REWRITE DEFAULT-CDR))
                    (12 12
                        (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
                    (12 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
                    (12 8
                        (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
                    (12 4 (:DEFINITION POSP))
                    (10 10
                        (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
                    (9 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
                    (7 7 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
                    (7 7
                       (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                    (6 5
                       (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                    (5 5 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                    (4 4 (:TYPE-PRESCRIPTION POSP)))
(SUBRANGE-NOT-NIL1 (61 2 (:REWRITE TAKE-DOES-NOTHING))
                   (22 1 (:REWRITE LEN-OF-NTHCDR))
                   (20 19 (:REWRITE DEFAULT-<-1))
                   (19 19 (:REWRITE DEFAULT-<-2))
                   (10 9 (:REWRITE DEFAULT-+-2))
                   (10 9 (:REWRITE DEFAULT-+-1))
                   (10 2 (:REWRITE NTHCDR-WHEN-NOT-POSP))
                   (6 2 (:DEFINITION POSP))
                   (5 3 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
                   (4 1 (:REWRITE <-OF-+-OF---AND-0-ARG1))
                   (3 3 (:REWRITE FOLD-CONSTS-IN-+))
                   (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
                   (3 3
                      (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
                   (3 3 (:REWRITE +-COMBINE-CONSTANTS))
                   (2 2 (:TYPE-PRESCRIPTION POSP))
                   (2 2
                      (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
                   (2 2 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
                   (2 2
                      (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                   (2 2
                      (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                   (2 2
                      (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
                   (2 2
                      (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                   (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(SUBRANGE-NOT-NIL2 (36 1
                       (:REWRITE SUBRANGE-TO-END-BECOMES-NTHCDR))
                   (24 3
                       (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
                   (18 18 (:TYPE-PRESCRIPTION LEN))
                   (6 6
                      (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
                   (3 3 (:REWRITE DEFAULT-<-2))
                   (3 3 (:REWRITE DEFAULT-<-1))
                   (3 2 (:REWRITE DEFAULT-+-2))
                   (3 1
                      (:REWRITE SUBRANGE-OUT-OF-ORDER-OR-SINGLETON))
                   (3 1 (:REWRITE SUBRANGE-OUT-OF-ORDER))
                   (2 2
                      (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (2 1 (:DEFINITION FIX))
                   (1 1
                      (:REWRITE SUBRANGE-WHEN-START-IS-NEGATIVE))
                   (1 1
                      (:REWRITE SUBRANGE-WHEN-END-IS-NEGATIVE))
                   (1 1
                      (:REWRITE SUBRANGE-OUT-OF-ORDER-CHEAP))
                   (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP)))
