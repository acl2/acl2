(SEPARATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(TO-ADMIT-LESS-GEN
 (1003 480 (:REWRITE DEFAULT-+-2))
 (663 480 (:REWRITE DEFAULT-+-1))
 (360 90 (:DEFINITION INTEGER-ABS))
 (360 45 (:DEFINITION LENGTH))
 (225 45 (:DEFINITION LEN))
 (175 147 (:REWRITE DEFAULT-CDR))
 (152 117 (:REWRITE DEFAULT-CAR))
 (150 150 (:REWRITE FOLD-CONSTS-IN-+))
 (117 98 (:REWRITE DEFAULT-<-1))
 (106 98 (:REWRITE DEFAULT-<-2))
 (90 90 (:REWRITE DEFAULT-UNARY-MINUS))
 (45 45 (:TYPE-PRESCRIPTION LEN))
 (45 45 (:REWRITE DEFAULT-REALPART))
 (45 45 (:REWRITE DEFAULT-NUMERATOR))
 (45 45 (:REWRITE DEFAULT-IMAGPART))
 (45 45 (:REWRITE DEFAULT-DENOMINATOR))
 (45 45 (:REWRITE DEFAULT-COERCE-2))
 (45 45 (:REWRITE DEFAULT-COERCE-1))
 (35 7 (:REWRITE SYMBOL<-ASYMMETRIC))
 (18 15 (:REWRITE SYMBOL<-TRANSITIVE))
 (15 15 (:REWRITE SYMBOL<-TRICHOTOMY))
 )
(TO-ADMIT-MORE-GEN
 (589 284 (:REWRITE DEFAULT-+-2))
 (403 284 (:REWRITE DEFAULT-+-1))
 (248 62 (:DEFINITION INTEGER-ABS))
 (248 31 (:DEFINITION LENGTH))
 (243 1 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (155 31 (:DEFINITION LEN))
 (92 85 (:REWRITE DEFAULT-CDR))
 (89 70 (:REWRITE DEFAULT-<-1))
 (80 80 (:REWRITE FOLD-CONSTS-IN-+))
 (78 70 (:REWRITE DEFAULT-<-2))
 (62 62 (:REWRITE DEFAULT-UNARY-MINUS))
 (53 53 (:REWRITE DEFAULT-CAR))
 (35 7 (:REWRITE SYMBOL<-ASYMMETRIC))
 (31 31 (:TYPE-PRESCRIPTION LEN))
 (31 31 (:REWRITE DEFAULT-REALPART))
 (31 31 (:REWRITE DEFAULT-NUMERATOR))
 (31 31 (:REWRITE DEFAULT-IMAGPART))
 (31 31 (:REWRITE DEFAULT-DENOMINATOR))
 (31 31 (:REWRITE DEFAULT-COERCE-2))
 (31 31 (:REWRITE DEFAULT-COERCE-1))
 (18 15 (:REWRITE SYMBOL<-TRANSITIVE))
 (15 15 (:REWRITE SYMBOL<-TRICHOTOMY))
 )
(TO-ADMIT-LESS
 (208 4 (:DEFINITION ACL2-COUNT))
 (67 34 (:REWRITE DEFAULT-+-2))
 (47 34 (:REWRITE DEFAULT-+-1))
 (32 8 (:DEFINITION INTEGER-ABS))
 (32 4 (:DEFINITION LENGTH))
 (28 2 (:DEFINITION SEPARATE))
 (20 4 (:DEFINITION LEN))
 (14 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-<-2))
 (12 10 (:REWRITE DEFAULT-<-1))
 (10 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(TO-ADMIT-MORE
 (204 4 (:DEFINITION ACL2-COUNT))
 (67 34 (:REWRITE DEFAULT-+-2))
 (47 34 (:REWRITE DEFAULT-+-1))
 (32 8 (:DEFINITION INTEGER-ABS))
 (32 4 (:DEFINITION LENGTH))
 (28 2 (:DEFINITION SEPARATE))
 (20 4 (:DEFINITION LEN))
 (16 14 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-<-2))
 (12 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 2 (:DEFINITION MV-NTH))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(SIMPLE-CANCELLATION
 (4785 2402 (:REWRITE DEFAULT-+-2))
 (3313 2402 (:REWRITE DEFAULT-+-1))
 (2272 568 (:REWRITE COMMUTATIVITY-OF-+))
 (2272 568 (:DEFINITION INTEGER-ABS))
 (2272 284 (:DEFINITION LENGTH))
 (1420 284 (:DEFINITION LEN))
 (741 648 (:REWRITE DEFAULT-<-1))
 (726 648 (:REWRITE DEFAULT-<-2))
 (633 633 (:REWRITE FOLD-CONSTS-IN-+))
 (568 568 (:REWRITE DEFAULT-UNARY-MINUS))
 (340 340 (:REWRITE DEFAULT-CAR))
 (284 284 (:TYPE-PRESCRIPTION LEN))
 (284 284 (:REWRITE DEFAULT-REALPART))
 (284 284 (:REWRITE DEFAULT-NUMERATOR))
 (284 284 (:REWRITE DEFAULT-IMAGPART))
 (284 284 (:REWRITE DEFAULT-DENOMINATOR))
 (284 284 (:REWRITE DEFAULT-COERCE-2))
 (284 284 (:REWRITE DEFAULT-COERCE-1))
 )
(SIMPLE-CANCELLATION2
 (6780 3348 (:REWRITE DEFAULT-+-2))
 (4626 3348 (:REWRITE DEFAULT-+-1))
 (3056 764 (:DEFINITION INTEGER-ABS))
 (3056 382 (:DEFINITION LENGTH))
 (2132 18 (:REWRITE SIMPLE-CANCELLATION))
 (1910 382 (:DEFINITION LEN))
 (1012 874 (:REWRITE DEFAULT-<-2))
 (993 874 (:REWRITE DEFAULT-<-1))
 (764 764 (:REWRITE DEFAULT-UNARY-MINUS))
 (382 382 (:TYPE-PRESCRIPTION LEN))
 (382 382 (:REWRITE DEFAULT-REALPART))
 (382 382 (:REWRITE DEFAULT-NUMERATOR))
 (382 382 (:REWRITE DEFAULT-IMAGPART))
 (382 382 (:REWRITE DEFAULT-DENOMINATOR))
 (382 382 (:REWRITE DEFAULT-COERCE-2))
 (382 382 (:REWRITE DEFAULT-COERCE-1))
 )
(CDR-MORE-DECREASES
 (126 4 (:DEFINITION ACL2-COUNT))
 (42 20 (:REWRITE DEFAULT-+-2))
 (28 20 (:REWRITE DEFAULT-+-1))
 (28 2 (:DEFINITION SEPARATE))
 (16 4 (:REWRITE COMMUTATIVITY-OF-+))
 (16 4 (:DEFINITION INTEGER-ABS))
 (16 2 (:DEFINITION LENGTH))
 (15 13 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (10 2 (:DEFINITION LEN))
 (8 2 (:DEFINITION MV-NTH))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(CDR-LESS-DECREASES
 (157 6 (:DEFINITION ACL2-COUNT))
 (52 24 (:REWRITE DEFAULT-+-2))
 (39 1 (:REWRITE SIMPLE-CANCELLATION2))
 (34 24 (:REWRITE DEFAULT-+-1))
 (28 2 (:DEFINITION SEPARATE))
 (17 14 (:REWRITE DEFAULT-CAR))
 (17 13 (:REWRITE DEFAULT-CDR))
 (16 4 (:REWRITE COMMUTATIVITY-OF-+))
 (16 4 (:DEFINITION INTEGER-ABS))
 (16 2 (:DEFINITION LENGTH))
 (10 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (10 2 (:DEFINITION LEN))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 6 (:REWRITE DEFAULT-<-2))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 1 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(QUICK-ORDER
 (128 4 (:DEFINITION ACL2-COUNT))
 (42 20 (:REWRITE DEFAULT-+-2))
 (28 20 (:REWRITE DEFAULT-+-1))
 (28 2 (:DEFINITION SEPARATE))
 (17 13 (:REWRITE DEFAULT-CDR))
 (16 4 (:REWRITE COMMUTATIVITY-OF-+))
 (16 4 (:DEFINITION INTEGER-ABS))
 (16 2 (:DEFINITION LENGTH))
 (12 11 (:REWRITE DEFAULT-CAR))
 (10 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (10 2 (:DEFINITION LEN))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SEPARATE-SYMBOL-LISTP
 (107 99 (:REWRITE DEFAULT-CAR))
 (82 74 (:REWRITE DEFAULT-CDR))
 (40 31 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-LISTP-FORWARD
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(TRUE-LISTP-QUICK-ORDER)
(SYMBOL-LISTP-CDAR
 (238 204 (:REWRITE DEFAULT-CAR))
 (126 120 (:REWRITE DEFAULT-CDR))
 (97 88 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-LISTP-CAR
 (181 149 (:REWRITE DEFAULT-CAR))
 (134 33 (:REWRITE SYMBOL-LISTP-FORWARD))
 (59 59 (:REWRITE SYMBOL<-TRANSITIVE))
 (58 58 (:REWRITE DEFAULT-CDR))
 )
(SYMBOLP-FIRST-FIRST
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(SYMBOL-LISTP-APPEND
 (18 16 (:REWRITE DEFAULT-CAR))
 (15 13 (:REWRITE DEFAULT-CDR))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SYMBOL-LISTP-QUICK-ORDER-OF-SYMBOL-LISTS
 (10708 274 (:DEFINITION SEPARATE))
 (7420 1352 (:REWRITE SYMBOL<-TRICHOTOMY))
 (5744 810 (:REWRITE SYMBOL<-ASYMMETRIC))
 (3234 3234 (:TYPE-PRESCRIPTION SYMBOL<))
 (1352 1352 (:REWRITE SYMBOL<-TRANSITIVE))
 (252 63 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (63 63 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(QUICK-ORDER
 (106 2 (:DEFINITION SEPARATE))
 (97 1 (:DEFINITION QUICK-ORDER))
 (82 10 (:REWRITE SYMBOL<-TRICHOTOMY))
 (56 6 (:REWRITE SYMBOL<-ASYMMETRIC))
 (24 24 (:TYPE-PRESCRIPTION SYMBOL<))
 (22 20 (:REWRITE DEFAULT-CDR))
 (20 18 (:REWRITE DEFAULT-CAR))
 (11 1 (:DEFINITION SYMBOL-LISTP))
 (10 10 (:REWRITE SYMBOL<-TRANSITIVE))
 (7 1 (:DEFINITION BINARY-APPEND))
 )
(ORDER
 (1 1 (:TYPE-PRESCRIPTION ORDER))
 )
