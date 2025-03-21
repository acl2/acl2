(STRING-LISTP-OF-REV
 (91 41 (:REWRITE DEFAULT-CAR))
 (87 37 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE CONSP-OF-REV))
 (12 12 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(GET-NON-EMPTY-LINES
 (10 10 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE DEFAULT-CDR))
 )
(TRUE-LISTP-OF-GET-NON-EMPTY-LINES
 (23 8 (:DEFINITION TRUE-LISTP))
 (11 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(STRING-LISTP-OF-GET-NON-EMPTY-LINES
 (34 28 (:REWRITE DEFAULT-CAR))
 (22 16 (:REWRITE DEFAULT-CDR))
 )
(GET-BLOCK-FOR-NAME
 (2527 1428 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2428 823 (:REWRITE DEFAULT-CDR))
 (1499 590 (:REWRITE DEFAULT-CAR))
 (1266 961 (:REWRITE STR::CONSP-OF-EXPLODE))
 (1156 578 (:REWRITE DEFAULT-+-2))
 (578 578 (:REWRITE DEFAULT-+-1))
 (368 368 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (96 48 (:REWRITE DEFAULT-<-1))
 (72 48 (:REWRITE DEFAULT-<-2))
 )
(STRING-LISTP-OF-GET-BLOCK-FOR-NAME
 (1233 648 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (585 585 (:TYPE-PRESCRIPTION STRING-APPEND-LST))
 (475 286 (:REWRITE DEFAULT-CAR))
 (447 258 (:REWRITE DEFAULT-CDR))
 (252 189 (:REWRITE STR::CONSP-OF-EXPLODE))
 (192 48 (:REWRITE REV-WHEN-NOT-CONSP))
 (96 48 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-GET-NON-EMPTY-LINES))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 48 (:TYPE-PRESCRIPTION GET-NON-EMPTY-LINES))
 )
(APPEND-STRING-LINES
 (255 3 (:DEFINITION APPEND-STRING-LINES))
 (246 9 (:DEFINITION STRING-APPEND-LST))
 (117 9 (:DEFINITION STRING-APPEND))
 (96 12 (:DEFINITION BINARY-APPEND))
 (67 49 (:REWRITE DEFAULT-CDR))
 (47 29 (:REWRITE DEFAULT-CAR))
 (42 42 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (36 21 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (33 12 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (24 18 (:REWRITE STR::CONSP-OF-EXPLODE))
 (15 9 (:REWRITE STR::COERCE-TO-STRING-REMOVAL))
 (12 6 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (9 3 (:REWRITE STR::EXPLODE-OF-IMPLODE))
 (6 3 (:REWRITE STR::IMPLODE-OF-EXPLODE))
 (6 3 (:REWRITE APPEND-TO-NIL))
 (3 3 (:REWRITE STR::MAKE-CHARACTER-LIST-IS-IDENTITY-UNDER-CHARLISTEQV))
 )
(GEN-XDOC-FORM-FOR-ITEM
 (182 2 (:DEFINITION APPEND-STRING-LINES))
 (172 6 (:DEFINITION STRING-APPEND-LST))
 (80 6 (:DEFINITION STRING-APPEND))
 (66 8 (:DEFINITION BINARY-APPEND))
 (42 30 (:REWRITE DEFAULT-CDR))
 (42 30 (:REWRITE DEFAULT-CAR))
 (28 28 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (24 14 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (22 8 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (16 12 (:REWRITE STR::CONSP-OF-EXPLODE))
 (12 12 (:REWRITE DEFAULT-SYMBOL-NAME))
 (10 6 (:REWRITE STR::COERCE-TO-STRING-REMOVAL))
 (8 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE STR::EXPLODE-OF-IMPLODE))
 (4 2 (:REWRITE STR::IMPLODE-OF-EXPLODE))
 (4 2 (:REWRITE APPEND-TO-NIL))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:REWRITE STR::MAKE-CHARACTER-LIST-IS-IDENTITY-UNDER-CHARLISTEQV))
 )
(GEN-XDOC-FORMS-FOR-ITEMS
 (13 13 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (12 4 (:DEFINITION STRING-LISTP))
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 2 (:DEFINITION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(GEN-XDOC-FOR-FILE-FN)
