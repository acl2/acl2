(APPLY-FOR-DEFEVALUATOR)
(EMPTY-EVAL)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(EMPTY-EVAL-OF-FNCALL-ARGS)
(EMPTY-EVAL-OF-VARIABLE)
(EMPTY-EVAL-OF-QUOTE)
(EMPTY-EVAL-OF-LAMBDA)
(EMPTY-EVAL-LIST-OF-ATOM)
(EMPTY-EVAL-LIST-OF-CONS)
(EMPTY-EVAL-OF-NONSYMBOL-ATOM)
(EMPTY-EVAL-OF-BAD-FNCALL)
(EMPTY-EVAL-OF-LAMBDA-BETTER
 (10 10 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 (8 8 (:REWRITE EMPTY-EVAL-LIST-OF-CONS))
 (8 8 (:REWRITE EMPTY-EVAL-LIST-OF-ATOM))
 )
(EMPTY-EVAL-LIST-OF-APPEND
 (186 93 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (93 93 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (93 93 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (9 6 (:REWRITE DEFAULT-CAR))
 (8 5 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE EMPTY-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 )
(LEN-OF-EMPTY-EVAL-LIST
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (1 1 (:REWRITE EMPTY-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 )
(CDR-OF-EMPTY-EVAL-LIST
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (1 1 (:REWRITE EMPTY-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 )
(CAR-OF-EMPTY-EVAL-LIST
 (8 5 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (5 5 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(TRUE-LISTP-OF-EMPTY-EVAL-LIST-TYPE
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 1 (:REWRITE CDR-OF-EMPTY-EVAL-LIST))
 (3 3 (:REWRITE EMPTY-EVAL-LIST-OF-ATOM))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (1 1 (:REWRITE EMPTY-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 )
(EMPTY-EVAL-LIST-OF-TRUE-LIST_FIX
 (7 6 (:REWRITE DEFAULT-CAR))
 (6 5 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 (2 2 (:REWRITE EMPTY-EVAL-OF-VARIABLE))
 (2 2 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 )
(EMPTY-EVAL-LIST-WHEN-QUOTE-LISTP
 (10 10 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 )
(EMPTY-EVAL-LIST-OF-KWOTE-LST
 (69 6 (:DEFINITION QUOTE-LISTP))
 (24 22 (:REWRITE DEFAULT-CAR))
 (18 6 (:DEFINITION QUOTEP))
 (16 4 (:REWRITE EMPTY-EVAL-LIST-OF-ATOM))
 (14 12 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 )
(EMPTY-EVAL-LIST-WHEN-SYMBOL-LISTP
 (35 5 (:DEFINITION QUOTE-LISTP))
 (34 34 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE DEFAULT-CDR))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (9 5 (:DEFINITION QUOTEP))
 (4 4 (:REWRITE EMPTY-EVAL-LIST-OF-ATOM))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (1 1 (:REWRITE EMPTY-EVAL-OF-QUOTE))
 (1 1 (:REWRITE EMPTY-EVAL-OF-LAMBDA-BETTER))
 )
(EMPTY-EVAL-OF-FNCALL-ARGS-BACK)
