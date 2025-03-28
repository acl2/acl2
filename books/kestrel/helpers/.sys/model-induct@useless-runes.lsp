(INDUCTION-DEPTH-LIMIT)
(FLAG-LEMMA-FOR-THEOREM-FOR-FIND-ALL-FN-CALL-SUBTERMS
 (4643 4631 (:REWRITE DEFAULT-CDR))
 (4618 4606 (:REWRITE DEFAULT-CAR))
 (1182 591 (:REWRITE DEFAULT-+-2))
 (1062 118 (:REWRITE NOT-MEMBER-EQUAL-OF-NON-TRIVIAL-FORMALS))
 (1008 453 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (946 86 (:REWRITE FREE-VARS-IN-TERMS-WHEN-QUOTE-LISTP))
 (896 453 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (796 199 (:REWRITE FREE-VARS-IN-TERM-WHEN-QUOTEP))
 (688 86 (:DEFINITION QUOTE-LISTP))
 (591 591 (:REWRITE DEFAULT-+-1))
 (507 169 (:DEFINITION SYMBOL-LISTP))
 (430 430 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (306 306 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (293 293 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (199 199 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (172 172 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERMS))
 (86 86 (:REWRITE FREE-VARS-IN-TERMS-WHEN-NOT-CONSP-CHEAP))
 )
(HELP::THEOREM-FOR-FIND-ALL-FN-CALL-SUBTERMS)
(HELP::THEOREM-FOR-FIND-ALL-FN-CALL-SUBTERMS-LST)
(HELP::CONS-LISTP$-OF-FIND-ALL-FN-CALL-SUBTERMS)
(HELP::FILTER-ACTUALS-FOR-FORMALS
 (30 10 (:DEFINITION MEMBER-EQUAL))
 (25 25 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(HELP::FILTER-GOOD-INDUCT-CALLS
 (242 218 (:REWRITE DEFAULT-CDR))
 (223 223 (:REWRITE DEFAULT-CAR))
 (165 15 (:DEFINITION FGETPROP))
 (144 24 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NO-DUPLICATESP-EQUAL-OF-CDR))
 (117 9 (:DEFINITION HELP::FILTER-ACTUALS-FOR-FORMALS))
 (56 8 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (48 24 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (27 9 (:DEFINITION MEMBER-EQUAL))
 (20 20 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 4 (:DEFINITION TRUE-LISTP))
 )
(HELP::NOT-MEMBER-EQUAL-OF-FILTER-GOOD-INDUCT-CALLS
 (196 192 (:REWRITE DEFAULT-CAR))
 (186 161 (:REWRITE DEFAULT-CDR))
 (148 22 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NO-DUPLICATESP-EQUAL-OF-CDR))
 (143 11 (:DEFINITION HELP::FILTER-ACTUALS-FOR-FORMALS))
 (44 8 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (42 21 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-FN-FORMALS))
 )
(HELP::NO-DUPLICATESP-EQUAL-OF-FILTER-GOOD-INDUCT-CALLS
 (306 24 (:DEFINITION HELP::FILTER-ACTUALS-FOR-FORMALS))
 (276 48 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (222 129 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (205 40 (:DEFINITION MEMBER-EQUAL))
 (160 160 (:TYPE-PRESCRIPTION HELP::FILTER-GOOD-INDUCT-CALLS))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-FN-FORMALS))
 (22 1 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CONS-NO-SPLIT))
 )
(HELP::INDUCT-EXPRESSIONS-IN-TERM)
(HELP::NO-DUPLICATESP-EQUAL-OF-INDUCT-EXPRESSIONS-IN-TERM)
(HELP::INDUCT-EXPRESSIONS-IN-TERMS
 (20 2 (:DEFINITION PLIST-WORLDP))
 (14 14 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(HELP::NO-DUPLICATESP-EQUAL-OF-INDUCT-EXPRESSIONS-IN-TERMS
 (40 7 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (34 34 (:TYPE-PRESCRIPTION HELP::INDUCT-EXPRESSIONS-IN-TERMS))
 (29 19 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (12 1 (:DEFINITION MEMBER-EQUAL))
 (6 3 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (6 3 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION HELP::INDUCT-EXPRESSIONS-IN-TERM))
 )
(HELP::INDUCT-EXPRESSIONS-IN-TERM-LISTS
 (30 3 (:DEFINITION PLIST-WORLDP))
 (22 22 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(HELP::NO-DUPLICATESP-EQUAL-OF-INDUCT-EXPRESSIONS-IN-TERM-LISTS
 (40 7 (:REWRITE NO-DUPLICATESP-EQUAL-OF-CDR))
 (34 34 (:TYPE-PRESCRIPTION HELP::INDUCT-EXPRESSIONS-IN-TERM-LISTS))
 (29 19 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (12 1 (:DEFINITION MEMBER-EQUAL))
 (6 3 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (6 3 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (6 3 (:REWRITE REMOVE-DUPLICATES-EQUAL-WHEN-NO-DUPLICATESP-EQUAL-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION REMOVE-DUPLICATES-EQUAL))
 )
(HELP::MAKE-INDUCT-RECS-AUX)
(HELP::MAKE-INDUCT-RECS)
