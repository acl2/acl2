(LEGAL-VARIABLE-LISTP)
(SYMBOL-LISTP-WHEN-LEGAL-VARIABLE-LISTP
 (11 11 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(LEGAL-VARIABLE-LISTP-OF-CONS
 (5 5 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(LEGAL-VARIABLE-LISTP-OF-TRUE-LIST-FIX
 (11 11 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE LEGAL-VARIABLE-OR-CONSTANT-NAMEP-IMPLIES-SYMBOLP))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
