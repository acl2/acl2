(ALL-CDRS-RATIONALP
 (17 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (11 2 (:REWRITE DEFAULT-CDR))
 (5 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (4 4 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 1 (:REWRITE USE-ALL-CONSP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(MERGE-BY-CDR->
 (328 38 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (242 44 (:REWRITE DEFAULT-CDR))
 (120 6 (:DEFINITION TRUE-LISTP))
 (90 90 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (64 16 (:REWRITE USE-ALL-CONSP))
 (48 48 (:TYPE-PRESCRIPTION MEMBERP))
 (39 22 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (28 14 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (25 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE USE-ALL-CONSP-2))
 (16 16 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (16 15 (:REWRITE DEFAULT-+-2))
 (16 15 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(ACL2-COUNT-OF-EVENS-BOUND
 (6701 3523 (:REWRITE DEFAULT-+-2))
 (4481 3523 (:REWRITE DEFAULT-+-1))
 (1812 1234 (:REWRITE DEFAULT-<-2))
 (1383 1234 (:REWRITE DEFAULT-<-1))
 (717 717 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (701 508 (:REWRITE DEFAULT-CAR))
 (576 576 (:REWRITE USE-ALL-CONSP-2))
 (576 576 (:REWRITE USE-ALL-CONSP))
 (576 576 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (447 447 (:REWRITE DEFAULT-UNARY-MINUS))
 (418 62 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (242 242 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (241 241 (:REWRITE DEFAULT-DENOMINATOR))
 (222 222 (:REWRITE DEFAULT-COERCE-2))
 (222 222 (:REWRITE DEFAULT-COERCE-1))
 (215 215 (:REWRITE DEFAULT-NUMERATOR))
 (206 206 (:REWRITE DEFAULT-REALPART))
 (206 206 (:REWRITE DEFAULT-IMAGPART))
 (198 198 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (150 67 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (134 134 (:TYPE-PRESCRIPTION ALL-CONSP))
 (67 67 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (45 45 (:REWRITE EQUAL-OF-LEN-AND-0))
 (31 5 (:REWRITE ALL-CONSP-OF-CDR))
 )
(<-OF-ACL2-COUNT-OF-EVENS
 (1743 999 (:REWRITE DEFAULT-+-2))
 (1259 999 (:REWRITE DEFAULT-+-1))
 (494 39 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (488 122 (:DEFINITION INTEGER-ABS))
 (438 150 (:REWRITE DEFAULT-CAR))
 (377 272 (:REWRITE DEFAULT-<-2))
 (300 272 (:REWRITE DEFAULT-<-1))
 (297 297 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (278 54 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (244 61 (:DEFINITION LENGTH))
 (201 201 (:REWRITE USE-ALL-CONSP-2))
 (201 201 (:REWRITE USE-ALL-CONSP))
 (201 201 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (141 15 (:REWRITE ALL-CONSP-OF-CDR))
 (122 122 (:REWRITE DEFAULT-UNARY-MINUS))
 (108 108 (:TYPE-PRESCRIPTION ALL-CONSP))
 (79 79 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (63 63 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (61 61 (:REWRITE DEFAULT-REALPART))
 (61 61 (:REWRITE DEFAULT-NUMERATOR))
 (61 61 (:REWRITE DEFAULT-IMAGPART))
 (61 61 (:REWRITE DEFAULT-DENOMINATOR))
 (61 61 (:REWRITE DEFAULT-COERCE-2))
 (61 61 (:REWRITE DEFAULT-COERCE-1))
 (60 4 (:REWRITE ACL2-COUNT-OF-EVENS-BOUND))
 (54 54 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTP-OF-MERGE-BY-CDR->
 (2825 296 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (806 98 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (421 397 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (332 114 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (296 296 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (294 14 (:REWRITE ALL-CONSP-OF-REVAPPEND))
 (248 248 (:REWRITE USE-ALL-CONSP-2))
 (248 248 (:REWRITE USE-ALL-CONSP))
 (248 248 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (228 228 (:TYPE-PRESCRIPTION ALL-CONSP))
 (190 176 (:REWRITE DEFAULT-CAR))
 (128 114 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (46 46 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (30 6 (:REWRITE LEN-OF-CDR))
 (30 6 (:REWRITE ALL-CONSP-OF-CDR))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(MERGE-SORT-BY-CDR->
 (7806 596 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5356 2857 (:REWRITE DEFAULT-+-2))
 (3709 2857 (:REWRITE DEFAULT-+-1))
 (1543 1041 (:REWRITE DEFAULT-<-2))
 (1185 1041 (:REWRITE DEFAULT-<-1))
 (596 596 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (587 587 (:REWRITE USE-ALL-CONSP-2))
 (587 587 (:REWRITE USE-ALL-CONSP))
 (587 587 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (508 486 (:REWRITE DEFAULT-CAR))
 (438 32 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (359 359 (:REWRITE DEFAULT-UNARY-MINUS))
 (300 60 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (266 266 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (198 198 (:REWRITE DEFAULT-DENOMINATOR))
 (183 183 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (178 178 (:REWRITE DEFAULT-COERCE-2))
 (178 178 (:REWRITE DEFAULT-COERCE-1))
 (170 170 (:REWRITE DEFAULT-NUMERATOR))
 (161 161 (:REWRITE DEFAULT-REALPART))
 (161 161 (:REWRITE DEFAULT-IMAGPART))
 (152 16 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (120 120 (:TYPE-PRESCRIPTION ALL-CONSP))
 (60 60 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (60 60 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(ALL-CONPS-OF-EVENS
 (236 19 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (217 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (135 10 (:REWRITE DEFAULT-CDR))
 (59 19 (:REWRITE USE-ALL-CONSP))
 (40 40 (:TYPE-PRESCRIPTION MEMBERP))
 (37 19 (:REWRITE DEFAULT-<-2))
 (37 5 (:REWRITE LEN-OF-CDR))
 (36 18 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (34 30 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (26 26 (:TYPE-PRESCRIPTION EVENS))
 (19 19 (:REWRITE USE-ALL-CONSP-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (19 19 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (19 19 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (9 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 )
(ALL-CONSP-OF-MERGE-BY-CDR->
 (719 78 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (620 26 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (362 54 (:REWRITE USE-ALL-CONSP))
 (308 308 (:TYPE-PRESCRIPTION MEMBERP))
 (260 44 (:REWRITE DEFAULT-CDR))
 (226 10 (:DEFINITION REVAPPEND))
 (132 66 (:REWRITE DEFAULT-<-2))
 (115 115 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (78 78 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (78 66 (:REWRITE DEFAULT-<-1))
 (54 54 (:REWRITE USE-ALL-CONSP-2))
 (54 54 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (44 44 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALL-CONSP-OF-MERGE-SORT-BY-CDR->
 (1015 85 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (737 53 (:REWRITE DEFAULT-CDR))
 (684 15 (:DEFINITION EVENS))
 (661 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (246 72 (:REWRITE USE-ALL-CONSP))
 (174 174 (:TYPE-PRESCRIPTION MEMBERP))
 (124 112 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (90 43 (:REWRITE DEFAULT-<-2))
 (85 85 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (72 72 (:REWRITE USE-ALL-CONSP-2))
 (72 72 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (71 40 (:REWRITE DEFAULT-+-2))
 (66 66 (:TYPE-PRESCRIPTION EVENS))
 (43 43 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DEFAULT-+-1))
 (26 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (25 1 (:REWRITE ALL-CONSP-OF-MERGE-BY-CDR->))
 (18 18 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (15 15 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(ALL-CDRS-RATIONALP-OF-EVENS
 (4639 330 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (543 500 (:REWRITE DEFAULT-+-2))
 (500 500 (:REWRITE DEFAULT-+-1))
 (289 192 (:REWRITE DEFAULT-<-2))
 (284 93 (:REWRITE FOLD-CONSTS-IN-+))
 (209 209 (:REWRITE USE-ALL-CONSP-2))
 (209 209 (:REWRITE USE-ALL-CONSP))
 (209 209 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (192 192 (:REWRITE DEFAULT-<-1))
 (149 32 (:REWRITE EQUAL-OF-LEN-AND-0))
 (128 128 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (60 6 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (48 6 (:LINEAR LEN-OF-CDR-LINEAR))
 )
(ALL-CDRS-RATIONALP-OF-MERGE-BY-CDR->
 (2480 270 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1702 244 (:REWRITE DEFAULT-CDR))
 (528 459 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (302 152 (:REWRITE DEFAULT-<-2))
 (270 270 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (193 166 (:REWRITE DEFAULT-CAR))
 (178 152 (:REWRITE DEFAULT-<-1))
 (126 126 (:REWRITE USE-ALL-CONSP-2))
 (126 126 (:REWRITE USE-ALL-CONSP))
 (126 126 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (52 52 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 2 (:REWRITE LEN-OF-CDR))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(ALL-CDRS-RATIONALP-OF-MERGE-SORT-BY-CDR->
 (95 89 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (59 59 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (44 21 (:REWRITE DEFAULT-<-2))
 (35 7 (:REWRITE DEFAULT-CAR))
 (33 33 (:REWRITE USE-ALL-CONSP-2))
 (33 33 (:REWRITE USE-ALL-CONSP))
 (33 33 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (30 30 (:TYPE-PRESCRIPTION EVENS))
 (26 13 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (16 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (13 13 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (6 2 (:REWRITE ALL-CDRS-RATIONALP-OF-MERGE-BY-CDR->))
 (4 4 (:REWRITE CDR-CONS))
 )
(MERGE-SORT-BY-CDR->
 (136 36 (:REWRITE DEFAULT-CDR))
 (118 2 (:DEFINITION MERGE-SORT-BY-CDR->))
 (86 80 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (86 32 (:REWRITE USE-ALL-CONSP))
 (54 54 (:TYPE-PRESCRIPTION MEMBERP))
 (50 50 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (46 22 (:REWRITE DEFAULT-<-2))
 (40 4 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (32 32 (:REWRITE USE-ALL-CONSP-2))
 (32 32 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (28 14 (:REWRITE DEFAULT-+-2))
 (24 4 (:REWRITE DEFAULT-CAR))
 (24 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (22 22 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTP-OF-EVENS
 (277 25 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (172 11 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (86 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (79 10 (:REWRITE ALL-CONSP-OF-CDR))
 (78 15 (:REWRITE LEN-OF-CDR))
 (69 2 (:REWRITE ALL-CONPS-OF-EVENS))
 (53 27 (:REWRITE DEFAULT-CDR))
 (49 47 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (43 43 (:TYPE-PRESCRIPTION ALL-CONSP))
 (40 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE USE-ALL-CONSP-2))
 (25 25 (:REWRITE USE-ALL-CONSP))
 (25 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (23 19 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (18 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(ALISTP-OF-ODDS
 (128 8 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (72 1 (:DEFINITION EVENS))
 (59 59 (:TYPE-PRESCRIPTION LEN))
 (49 6 (:REWRITE DEFAULT-CDR))
 (41 5 (:REWRITE LEN-OF-CDR))
 (20 3 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (17 8 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (13 7 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (11 6 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (8 8 (:REWRITE USE-ALL-CONSP-2))
 (8 8 (:REWRITE USE-ALL-CONSP))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (8 8 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 1 (:REWRITE ALL-CONSP-OF-CDR))
 (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (1 1 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(ALISTP-OF-MERGE-SORT-BY-CDR->
 (763 89 (:REWRITE DEFAULT-CDR))
 (724 22 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (693 20 (:DEFINITION EVENS))
 (532 46 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (511 10 (:REWRITE ALL-CONSP-OF-MERGE-SORT-BY-CDR->))
 (244 2 (:REWRITE ALISTP-OF-MERGE-BY-CDR->))
 (194 173 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (166 81 (:REWRITE DEFAULT-<-2))
 (153 153 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (126 2 (:REWRITE ALL-CONSP-OF-MERGE-BY-CDR->))
 (125 125 (:REWRITE USE-ALL-CONSP-2))
 (125 125 (:REWRITE USE-ALL-CONSP))
 (125 125 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (114 114 (:TYPE-PRESCRIPTION EVENS))
 (92 92 (:TYPE-PRESCRIPTION ALL-CONSP))
 (81 81 (:REWRITE DEFAULT-<-1))
 (80 7 (:REWRITE ALL-CONPS-OF-EVENS))
 (78 44 (:REWRITE DEFAULT-+-2))
 (68 43 (:REWRITE DEFAULT-CAR))
 (54 46 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (50 5 (:REWRITE ALL-CONSP-OF-CDR))
 (44 44 (:REWRITE DEFAULT-+-1))
 (24 3 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (18 18 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (10 10 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (4 4 (:TYPE-PRESCRIPTION ODDS))
 )
