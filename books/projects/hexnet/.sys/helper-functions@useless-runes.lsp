(SUBSETP-EQUAL-IMPLIES-CAR-MEMBER-EQUAL
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-REMOVE-EQUAL
 (49 48 (:REWRITE DEFAULT-CAR))
 (35 34 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-IMPLIES-CADR-MEMBER-EQUAL
 (34 7 (:REWRITE SUBSETP-EQUAL-IMPLIES-CAR-MEMBER-EQUAL))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-IMPLIES-CADDR-MEMBER-EQUAL
 (63 13 (:REWRITE SUBSETP-EQUAL-IMPLIES-CAR-MEMBER-EQUAL))
 (35 7 (:REWRITE SUBSETP-EQUAL-IMPLIES-CADR-MEMBER-EQUAL))
 (14 14 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-CAR))
 )
(ASSOC-OF-APPEND
 (1526 613 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (815 613 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (613 613 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (23 20 (:REWRITE DEFAULT-CAR))
 (19 16 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(LAST-APPEND
 (284 142 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (142 142 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (69 30 (:REWRITE DEFAULT-CDR))
 (24 9 (:REWRITE DEFAULT-CAR))
 )
(SUBSETP-EQUAL-MEMBER-EQUAL
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(CAR-LAST-REV
 (21 6 (:REWRITE DEFAULT-CDR))
 (16 1 (:DEFINITION BINARY-APPEND))
 (8 8 (:REWRITE CONSP-OF-REV))
 (8 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (2 2 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(UPDATE-ALIST
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-UPDATE-ALIST
 (52 50 (:REWRITE DEFAULT-CAR))
 (13 12 (:REWRITE DEFAULT-CDR))
 )
(FLATTEN-ALIST
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
