(PROP-SUBSUME
 (13634 6361 (:REWRITE DEFAULT-+-2))
 (8840 6361 (:REWRITE DEFAULT-+-1))
 (4336 1084 (:DEFINITION INTEGER-ABS))
 (4336 542 (:DEFINITION LENGTH))
 (3452 3452 (:REWRITE DEFAULT-CDR))
 (2710 542 (:DEFINITION LEN))
 (1564 1204 (:REWRITE DEFAULT-<-2))
 (1506 1506 (:REWRITE DEFAULT-CAR))
 (1444 1204 (:REWRITE DEFAULT-<-1))
 (1084 1084 (:REWRITE DEFAULT-UNARY-MINUS))
 (542 542 (:TYPE-PRESCRIPTION LEN))
 (542 542 (:REWRITE DEFAULT-REALPART))
 (542 542 (:REWRITE DEFAULT-NUMERATOR))
 (542 542 (:REWRITE DEFAULT-IMAGPART))
 (542 542 (:REWRITE DEFAULT-DENOMINATOR))
 (542 542 (:REWRITE DEFAULT-COERCE-2))
 (542 542 (:REWRITE DEFAULT-COERCE-1))
 (72 4 (:DEFINITION WFT-LIST))
 (60 4 (:DEFINITION WFQUANT))
 (16 16 (:DEFINITION VARIABLE-TERM))
 (12 4 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (8 8 (:TYPE-PRESCRIPTION WFT-LIST))
 (8 4 (:DEFINITION RELATION-SYMBOL))
 (4 4 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (4 4 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (4 4 (:DEFINITION LOGIC-SYMBOLP))
 (4 4 (:DEFINITION FUNCTION-SYMBOL))
 )
(PROP-SUBSUME-I
 (13634 6361 (:REWRITE DEFAULT-+-2))
 (8840 6361 (:REWRITE DEFAULT-+-1))
 (4336 1084 (:DEFINITION INTEGER-ABS))
 (4336 542 (:DEFINITION LENGTH))
 (3312 3312 (:REWRITE DEFAULT-CDR))
 (2710 542 (:DEFINITION LEN))
 (1564 1204 (:REWRITE DEFAULT-<-2))
 (1444 1204 (:REWRITE DEFAULT-<-1))
 (1426 1426 (:REWRITE DEFAULT-CAR))
 (1084 1084 (:REWRITE DEFAULT-UNARY-MINUS))
 (542 542 (:TYPE-PRESCRIPTION LEN))
 (542 542 (:REWRITE DEFAULT-REALPART))
 (542 542 (:REWRITE DEFAULT-NUMERATOR))
 (542 542 (:REWRITE DEFAULT-IMAGPART))
 (542 542 (:REWRITE DEFAULT-DENOMINATOR))
 (542 542 (:REWRITE DEFAULT-COERCE-2))
 (542 542 (:REWRITE DEFAULT-COERCE-1))
 (72 4 (:DEFINITION WFT-LIST))
 (60 4 (:DEFINITION WFQUANT))
 (16 16 (:DEFINITION VARIABLE-TERM))
 (12 4 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (8 8 (:TYPE-PRESCRIPTION WFT-LIST))
 (8 4 (:DEFINITION RELATION-SYMBOL))
 (4 4 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (4 4 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (4 4 (:DEFINITION LOGIC-SYMBOLP))
 (4 4 (:DEFINITION FUNCTION-SYMBOL))
 )
(SUBST-FREE-PRESERVES-PROP-SUBSUME
 (317324 317324 (:REWRITE DEFAULT-CDR))
 (170399 170399 (:REWRITE DEFAULT-CAR))
 (156204 14236 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (113545 14236 (:DEFINITION DOMAIN-TERM-LIST))
 (100492 3589 (:DEFINITION WF-AP-TERM-TOP))
 (70984 70984 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (31963 31963 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (14090 14090 (:DEFINITION VARIABLE-TERM))
 (10767 3589 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (3589 3589 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (3589 3589 (:DEFINITION FUNCTION-SYMBOL))
 )
(PROP-SUBSUME-GROUND-XSOUND
 (44352 44352 (:REWRITE DEFAULT-CDR))
 (28860 222 (:DEFINITION SUBST-FREE))
 (16772 16772 (:REWRITE DEFAULT-CAR))
 (11100 222 (:DEFINITION SUBST-TERM-LIST))
 (9768 888 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (7104 888 (:DEFINITION DOMAIN-TERM-LIST))
 (6438 222 (:DEFINITION WFATOMTOP))
 (6216 222 (:DEFINITION WF-AP-TERM-TOP))
 (5772 444 (:DEFINITION TRUE-LISTP))
 (4440 4440 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (2442 222 (:DEFINITION WFBINARY))
 (1998 1998 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (666 222 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (444 222 (:DEFINITION RELATION-SYMBOL))
 (222 222 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (222 222 (:DEFINITION LOGIC-SYMBOLP))
 (222 222 (:DEFINITION FUNCTION-SYMBOL))
 )
(CAR-OF-ALLS-IS-ALL
 (106 106 (:TYPE-PRESCRIPTION ALLS))
 (18 9 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(PROP-SUBSUME-XSOUND-VARS
 (3738 27 (:DEFINITION SUBST-FREE))
 (3191 3119 (:REWRITE DEFAULT-CDR))
 (1763 1691 (:REWRITE DEFAULT-CAR))
 (1374 27 (:DEFINITION SUBST-TERM-LIST))
 (1188 108 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (1104 138 (:DEFINITION DOMAIN-TERM-LIST))
 (985 901 (:TYPE-PRESCRIPTION ALLS))
 (807 27 (:DEFINITION WFATOMTOP))
 (756 27 (:DEFINITION WF-AP-TERM-TOP))
 (702 54 (:DEFINITION TRUE-LISTP))
 (690 690 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (333 27 (:DEFINITION WFBINARY))
 (330 30 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (303 303 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (225 15 (:DEFINITION MEMBER-EQUAL))
 (84 84 (:TYPE-PRESCRIPTION SUBST-FREE))
 (81 27 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (80 7 (:DEFINITION WFEXISTS))
 (80 7 (:DEFINITION WFALL))
 (54 27 (:DEFINITION RELATION-SYMBOL))
 (35 7 (:DEFINITION IFF))
 (30 30 (:REWRITE NOT-MEMBER-SUBSET))
 (27 27 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (27 27 (:DEFINITION LOGIC-SYMBOLP))
 (27 27 (:DEFINITION FUNCTION-SYMBOL))
 )
(PROP-SUBSUME-XSOUND
 (42854 43 (:DEFINITION FREE-VARS))
 (26152 173 (:DEFINITION UNION-EQUAL))
 (25729 43 (:DEFINITION VARS-IN-TERM-LIST))
 (16372 7 (:DEFINITION SUBST-FREE))
 (15830 613 (:REWRITE SUBSET-UNION-2))
 (15469 35 (:REWRITE NOT-FREE-NOT-CHANGE-REMOVE))
 (15066 844 (:DEFINITION MEMBER-EQUAL))
 (13039 652 (:DEFINITION SUBSETP-EQUAL))
 (9892 356 (:REWRITE IDX-CANCEL-NOT-MEMBER))
 (7688 50 (:REWRITE FREE-OCCURRENCE-REMOVE-FREE-VARS))
 (7538 50 (:DEFINITION FREE-OCCURRENCE))
 (7086 7086 (:REWRITE DEFAULT-CDR))
 (6460 340 (:DEFINITION IDX))
 (6284 742 (:DEFINITION DOMAIN-TERM-LIST))
 (5362 5362 (:REWRITE DEFAULT-CAR))
 (4400 400 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (4112 356 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (4061 4061 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3726 3726 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (3400 340 (:REWRITE IDX-NOT-ZERO))
 (3314 100 (:DEFINITION WFATOMTOP))
 (3076 3076 (:TYPE-PRESCRIPTION IDX))
 (2828 50 (:DEFINITION VAR-OCCURRENCE-TERM-LIST))
 (2816 200 (:DEFINITION TRUE-LISTP))
 (2800 100 (:DEFINITION WF-AP-TERM-TOP))
 (2583 7 (:REWRITE XEVAL-ALLS-FREE-EXPANDED))
 (2583 7 (:REWRITE XEVAL-ALLS-FREE))
 (2012 2012 (:TYPE-PRESCRIPTION VARS-IN-TERM-LIST))
 (1858 1858 (:REWRITE PERM-MEMBER))
 (1858 1858 (:REWRITE FIRST-OF-SUBBAG-IS-MEMBER))
 (1584 1584 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (1100 100 (:DEFINITION WFBINARY))
 (1064 1064 (:REWRITE SUBSETP-EQUAL-TRANSITIVE))
 (1020 680 (:REWRITE DEFAULT-+-2))
 (860 43 (:REWRITE SUBSET-MEMBER-SUBSET-CONS))
 (680 680 (:REWRITE DEFAULT-+-1))
 (674 337 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (650 650 (:TYPE-PRESCRIPTION VAR-OCCURRENCE-TERM-LIST))
 (600 600 (:TYPE-PRESCRIPTION FREE-OCCURRENCE))
 (434 434 (:TYPE-PRESCRIPTION ALLS))
 (425 50 (:DEFINITION REMOVE-EQUAL))
 (387 63 (:REWRITE CAR-OF-ALLS-IS-ALL))
 (356 356 (:REWRITE SUBBAG-NOT-MEMBER))
 (356 356 (:REWRITE NOT-MEMBER-SUBSET))
 (350 7 (:DEFINITION SUBST-TERM-LIST))
 (348 52 (:DEFINITION ALLS))
 (326 100 (:DEFINITION RELATION-SYMBOL))
 (300 100 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (232 232 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (226 100 (:DEFINITION LOGIC-SYMBOLP))
 (144 40 (:REWRITE UNION-NOT-NIL-IF-EITHER-ARGUMENT-IS-A-CONS))
 (113 113 (:REWRITE CDR-CONS))
 (113 113 (:REWRITE CAR-CONS))
 (100 100 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (100 100 (:DEFINITION FUNCTION-SYMBOL))
 (82 82 (:TYPE-PRESCRIPTION REMOVE-EQUAL))
 (43 7 (:REWRITE ALLS-QUANT))
 (43 7 (:REWRITE ALLS-ALL))
 (30 2 (:REWRITE DOMAIN-TERM-LIST-SUBSET))
 (9 9 (:REWRITE PERM-SETP-SETP))
 (3 3 (:REWRITE PERM-NOT-SETP-NOT-SETP))
 )
