(IF-AND-NOT-EVAL-OF-CONJOIN-OF-DISJOIN-LST-OF-CLAUSE-TO-CLAUSE-LIST
 (44 44 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (17 17 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (17 17 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (16 15 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (10 2 (:DEFINITION PAIRLIS$))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-LIST-OF-ATOM))
 (4 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (4 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (4 1 (:DEFINITION KWOTE-LST))
 (2 2 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (2 2 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-EQUAL-OF-T-AND-REMOVE-CONJUNCT))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (1 1 (:DEFINITION KWOTE))
 )
(IF-AND-NOT-EVAL-OF-DROP-CLEARLY-IMPLIED-CONJUNCTS
 (18 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (18 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (12 12 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (12 12 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 5 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (6 6 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (6 6 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (6 6 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-EQUAL-OF-T-AND-REMOVE-CONJUNCT))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(SIMPLIFY-ASSUMPTIONS-IN-CLAUSE
 (100 12 (:DEFINITION LENGTH))
 (97 97 (:REWRITE DEFAULT-CDR))
 (88 88 (:REWRITE DEFAULT-CAR))
 (44 22 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (22 22 (:REWRITE DEFAULT-+-1))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERM-LISTP-OF-SIMPLIFY-ASSUMPTIONS-IN-CLAUSE
 (350 42 (:DEFINITION LENGTH))
 (346 345 (:REWRITE DEFAULT-CDR))
 (301 300 (:REWRITE DEFAULT-CAR))
 (152 76 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (76 76 (:REWRITE DEFAULT-+-1))
 (68 68 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (66 14 (:DEFINITION SYMBOL-LISTP))
 (64 64 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (46 46 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 )
(ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-OF-SIMPLIFY-ASSUMPTIONS-IN-CLAUSE
 (1748 101 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (462 374 (:DEFINITION DISJOIN2))
 (398 398 (:TYPE-PRESCRIPTION SIMPLIFY-ASSUMPTIONS-IN-CLAUSE))
 (193 91 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (138 69 (:REWRITE DEFAULT-+-2))
 (105 35 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (105 35 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (76 32 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (70 70 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (70 70 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (69 69 (:REWRITE DEFAULT-+-1))
 (42 28 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (42 28 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (35 35 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (35 35 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (35 35 (:REWRITE IF-AND-NOT-EVAL-WHEN-EQUAL-OF-T-AND-REMOVE-CONJUNCT))
 (35 35 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (34 28 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (32 32 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (8 8 (:REWRITE CONS-EQUAL))
 )
(SIMPLIFY-ASSUMPTIONS-CLAUSE-PROCESSOR)
(SIMPLIFY-ASSUMPTIONS-CLAUSE-PROCESSOR-CORRECT
 (38 6 (:DEFINITION DISJOIN))
 (14 2 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (14 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:DEFINITION DISJOIN2))
 (6 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-DISJUNCTIONP))
 (6 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (4 4 (:TYPE-PRESCRIPTION TERM-IS-DISJUNCTIONP))
 (4 4 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (2 2 (:TYPE-PRESCRIPTION SIMPLIFY-ASSUMPTIONS-IN-CLAUSE))
 (2 2 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-NOT-IF-AND-NOT-EVAL-OF-REMOVE-CONJUNCT-WHEN-TRUE))
 (2 2 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-FIND-COMBINABLE-CONJUNCT-AND-FALSE))
 (2 2 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-EQUAL-OF-T-AND-REMOVE-CONJUNCT))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-COMPLEMENTARY-TERMSP))
 (2 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 )