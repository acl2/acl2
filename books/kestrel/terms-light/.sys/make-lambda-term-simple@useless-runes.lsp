(MAKE-LAMBDA-TERM-SIMPLE)
(PSEUDO-TERMP-OF-MAKE-LAMBDA-TERM-SIMPLE
 (62 38 (:REWRITE DEFAULT-CAR))
 (48 42 (:REWRITE DEFAULT-CDR))
 (47 3 (:DEFINITION PSEUDO-TERM-LISTP))
 (45 3 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (36 11 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (27 1 (:REWRITE PSEUDO-TERM-LISTP-OF-SET-DIFFERENCE-EQUAL))
 (26 13 (:REWRITE DEFAULT-+-2))
 (15 13 (:REWRITE DEFAULT-+-1))
 (15 3 (:DEFINITION MEMBER-EQUAL))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 4 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (8 4 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (6 6 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (6 6 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (6 2 (:DEFINITION TRUE-LIST-FIX))
 (4 4 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3 3 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
(LAMBDAS-CLOSED-IN-TERMP-OF-MAKE-LAMBDA-TERM-SIMPLE
 (56 1 (:DEFINITION PSEUDO-TERMP))
 (54 2 (:REWRITE SYMBOL-LISTP-OF-APPEND2))
 (47 2 (:REWRITE LAMBDAS-CLOSED-IN-TERMP-OF-CAR))
 (39 36 (:REWRITE DEFAULT-CDR))
 (36 1 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CAR-CHAIN))
 (34 3 (:REWRITE LAMBDAS-CLOSED-IN-TERMSP-OF-CDR))
 (32 29 (:REWRITE DEFAULT-CAR))
 (30 2 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (27 27 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-1))
 (25 5 (:DEFINITION LEN))
 (24 2 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN))
 (22 3 (:REWRITE LAMBDAS-CLOSED-IN-TERMSP-OF-WHEN-LAMBDAS-CLOSED-IN-TERMP))
 (14 9 (:REWRITE LAMBDAS-CLOSED-IN-TERMP-WHEN-SYMBOLP))
 (13 4 (:REWRITE SYMBOL-LISTP-OF-CDR))
 (12 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (10 5 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (10 4 (:REWRITE SYMBOL-LISTP-OF-TRUE-LIST-FIX))
 (10 2 (:DEFINITION MEMBER-EQUAL))
 (8 4 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (8 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (6 3 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (6 2 (:DEFINITION TRUE-LIST-FIX))
 (5 5 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (5 5 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 1 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERM-OF-LAMBDA-BODY-AND-LAMBDA-FORMALS))
 (5 1 (:REWRITE LAMBDAS-CLOSED-IN-TERMSP-OF-CADDR-OF-CAR))
 (4 4 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (4 4 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 (4 4 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (4 2 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (3 3 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 3 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
