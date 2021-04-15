(SMT::MY-SPLIT-KWD-ALIST (96 3
                             (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                         (90 1 (:REWRITE SUBLISTP-WHEN-PREFIXP))
                         (71 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                         (44 4 (:REWRITE PREFIXP-WHEN-PREFIXP))
                         (26 13 (:REWRITE DEFAULT-+-2))
                         (25 3 (:REWRITE LEN-WHEN-PREFIXP))
                         (18 18 (:REWRITE DEFAULT-CDR))
                         (13 13 (:REWRITE DEFAULT-+-1))
                         (11 11 (:TYPE-PRESCRIPTION PREFIXP))
                         (8 8
                            (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
                         (8 8
                            (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
                         (8 8 (:LINEAR LEN-WHEN-PREFIXP))
                         (5 3 (:REWRITE DEFAULT-<-1))
                         (4 4 (:TYPE-PRESCRIPTION SUBLISTP))
                         (4 4
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                         (4 4
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                         (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
                         (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
                         (4 4
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                         (4 4
                            (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                         (4 4
                            (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
                         (4 3 (:REWRITE DEFAULT-<-2))
                         (1 1 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
                         (1 1 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
                         (1 1 (:REWRITE SUBLISTP-COMPLETE))
                         (1 1 (:REWRITE DEFAULT-CAR)))
(SMT::TRUE-LISTP-OF-MY-SPLIT-KWD-ALIST.PRE
     (144 24
          (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (96 12 (:DEFINITION TRUE-LISTP))
     (48 48 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (48 24 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (24 24 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (24 24 (:REWRITE SET::IN-SET))
     (23 23 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE DEFAULT-CAR)))
(SMT::TRUE-LISTP-OF-MY-SPLIT-KWD-ALIST.POST
     (144 24
          (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (96 12 (:DEFINITION TRUE-LISTP))
     (48 48 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (48 24 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (24 24 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (24 24 (:REWRITE SET::IN-SET))
     (23 23 (:REWRITE DEFAULT-CDR))
     (15 15 (:REWRITE DEFAULT-CAR)))
(SMT::TREAT-IN-THEORY-HINT)
(SMT::TRUE-LISTP-OF-TREAT-IN-THEORY-HINT
     (31 31 (:REWRITE DEFAULT-CDR))
     (20 20 (:REWRITE DEFAULT-CAR))
     (20 5 (:DEFINITION BINARY-APPEND))
     (12 2
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (10 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (8 1 (:DEFINITION TRUE-LISTP))
     (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:REWRITE SET::IN-SET)))
(SMT::TREAT-EXPAND-HINT)
(SMT::TRUE-LISTP-OF-TREAT-EXPAND-HINT
     (16 4 (:DEFINITION BINARY-APPEND))
     (12 2
         (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
     (8 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (8 1 (:DEFINITION TRUE-LISTP))
     (7 7 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
     (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
     (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
     (2 2 (:REWRITE SET::IN-SET)))
(SMT::EXTRACT-HINT-WRAPPER)
(SMT::SMT-COMPUTED-HINT)
(SMT::SMT-DELAYED-HINT)
