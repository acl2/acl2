(UPDATE-NTH-WHEN-ATOM
 (6 6 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(UPDATE-NTH-WHEN-ZP
 (38 19 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 )
(UPDATE-NTH-OF-CONS
 (44 6 (:REWRITE UPDATE-NTH-WHEN-ZP))
 (42 11 (:REWRITE ZP-OPEN))
 (17 7 (:DEFINITION NOT))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (7 7 (:TYPE-PRESCRIPTION ZP))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(TRUE-LISTP-OF-UPDATE-NTH
 (217 181 (:REWRITE DEFAULT-CDR))
 (86 52 (:REWRITE DEFAULT-+-2))
 (83 67 (:REWRITE DEFAULT-<-2))
 (70 67 (:REWRITE DEFAULT-<-1))
 (54 24 (:REWRITE ZP-OPEN))
 (52 52 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 11 (:REWRITE DEFAULT-CAR))
 (5 1 (:DEFINITION BINARY-APPEND))
 )
(LEN-OF-UPDATE-NTH
 (40 8 (:DEFINITION LEN))
 (20 12 (:REWRITE DEFAULT-+-2))
 (17 12 (:REWRITE DEFAULT-<-1))
 (16 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CAR-OF-UPDATE-NTH
 (12 2 (:DEFINITION BINARY-APPEND))
 (9 9 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(CDR-OF-UPDATE-NTH
 (44 6 (:REWRITE UPDATE-NTH-WHEN-ZP))
 (42 11 (:REWRITE ZP-OPEN))
 (17 7 (:DEFINITION NOT))
 (14 11 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (7 7 (:TYPE-PRESCRIPTION ZP))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(NTH-OF-UPDATE-NTH-SAME
 (16 1 (:DEFINITION UPDATE-NTH))
 (12 2 (:REWRITE UPDATE-NTH-WHEN-ZP))
 (8 3 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 1 (:DEFINITION NOT))
 (2 2 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(NTH-OF-UPDATE-NTH-DIFF
 (120 114 (:REWRITE DEFAULT-+-2))
 (114 114 (:REWRITE DEFAULT-+-1))
 (86 83 (:REWRITE DEFAULT-<-1))
 (83 83 (:REWRITE DEFAULT-<-2))
 (12 2 (:DEFINITION BINARY-APPEND))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(NTH-OF-UPDATE-NTH-SPLIT-FOR-CONSTANTS
 (16 1 (:DEFINITION UPDATE-NTH))
 (12 2 (:REWRITE UPDATE-NTH-WHEN-ZP))
 (12 2 (:DEFINITION NTH))
 (10 5 (:REWRITE ZP-OPEN))
 (9 1 (:REWRITE NTH-OF-UPDATE-NTH-DIFF))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION NOT))
 (2 2 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 )
(UPDATE-NTH-OF-NTH
 (33 24 (:REWRITE DEFAULT-<-2))
 (33 20 (:REWRITE DEFAULT-+-2))
 (29 14 (:REWRITE ZP-OPEN))
 (26 24 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-NTH-OF-NTH-FREE
 (42 21 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (17 9 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-CDR))
 (11 8 (:REWRITE DEFAULT-<-2))
 (10 8 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE ZP-OPEN))
 )
(UPDATE-NTH-OF-UPDATE-NTH-SAME
 (404 41 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (333 33 (:DEFINITION NTH))
 (99 99 (:REWRITE DEFAULT-+-2))
 (99 99 (:REWRITE DEFAULT-+-1))
 (79 76 (:REWRITE DEFAULT-CDR))
 (78 78 (:REWRITE DEFAULT-<-2))
 (78 78 (:REWRITE DEFAULT-<-1))
 (67 37 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (53 53 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE NTH-OF-UPDATE-NTH-SAME))
 (10 10 (:REWRITE NTH-OF-UPDATE-NTH-SPLIT-FOR-CONSTANTS))
 (10 10 (:REWRITE NTH-OF-UPDATE-NTH-DIFF))
 (1 1 (:REWRITE CDR-CONS))
 (1 1 (:REWRITE CAR-CONS))
 )
(UPDATE-NTH-OF-UPDATE-NTH-DIFF
 (2548 193 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (2197 186 (:DEFINITION NTH))
 (635 404 (:REWRITE DEFAULT-CDR))
 (548 548 (:REWRITE DEFAULT-<-2))
 (548 548 (:REWRITE DEFAULT-<-1))
 (548 548 (:REWRITE DEFAULT-+-2))
 (548 548 (:REWRITE DEFAULT-+-1))
 (498 168 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (389 263 (:REWRITE DEFAULT-CAR))
 (181 16 (:REWRITE NTH-OF-UPDATE-NTH-DIFF))
 (101 6 (:REWRITE NTH-UPDATE-NTH))
 (16 16 (:REWRITE NTH-OF-UPDATE-NTH-SPLIT-FOR-CONSTANTS))
 (2 2 (:REWRITE NTH-0-CONS))
 )
(UPDATE-NTH-DIFF-GATHER-CONSTANTS
 (637 17 (:DEFINITION UPDATE-NTH))
 (434 52 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (354 40 (:DEFINITION NTH))
 (278 70 (:REWRITE ZP-OPEN))
 (94 94 (:REWRITE DEFAULT-+-2))
 (94 94 (:REWRITE DEFAULT-+-1))
 (93 31 (:REWRITE FOLD-CONSTS-IN-+))
 (89 89 (:REWRITE DEFAULT-<-2))
 (89 89 (:REWRITE DEFAULT-<-1))
 (76 76 (:REWRITE DEFAULT-CDR))
 (62 38 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (49 49 (:REWRITE DEFAULT-CAR))
 (35 3 (:REWRITE NTH-OF-UPDATE-NTH-DIFF))
 (27 27 (:TYPE-PRESCRIPTION ZP))
 (6 2 (:REWRITE CAR-OF-UPDATE-NTH))
 (4 4 (:REWRITE CDR-CONS))
 (3 3 (:REWRITE NTH-OF-UPDATE-NTH-SPLIT-FOR-CONSTANTS))
 )
(FINAL-CDR-OF-UPDATE-NTH
 (69 5 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (69 1 (:REWRITE CDR-OF-UPDATE-NTH))
 (64 7 (:DEFINITION NTH))
 (44 32 (:REWRITE DEFAULT-+-2))
 (41 13 (:REWRITE ZP-OPEN))
 (32 32 (:REWRITE DEFAULT-+-1))
 (24 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 )
(NTHCDR-PAST-UPDATE-NTH
 (686 595 (:REWRITE DEFAULT-+-2))
 (595 595 (:REWRITE DEFAULT-+-1))
 (449 143 (:REWRITE ZP-OPEN))
 (417 396 (:REWRITE DEFAULT-CDR))
 (308 277 (:REWRITE DEFAULT-<-2))
 (296 38 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (287 277 (:REWRITE DEFAULT-<-1))
 (261 87 (:REWRITE FOLD-CONSTS-IN-+))
 (258 44 (:DEFINITION NTH))
 (132 2 (:REWRITE CDR-OF-UPDATE-NTH))
 (58 58 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 16 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 )
(NTHCDR-BEFORE-UPDATE-NTH
 (924 87 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (837 80 (:DEFINITION NTH))
 (597 9 (:REWRITE CDR-OF-UPDATE-NTH))
 (332 319 (:REWRITE DEFAULT-<-2))
 (321 216 (:REWRITE DEFAULT-CDR))
 (320 319 (:REWRITE DEFAULT-<-1))
 (320 293 (:REWRITE DEFAULT-+-2))
 (293 293 (:REWRITE DEFAULT-+-1))
 (275 13 (:REWRITE NTHCDR-PAST-UPDATE-NTH))
 (171 75 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (170 122 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NTHCDR-OF-UPDATE-NTH
 (1249 101 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (1136 105 (:DEFINITION NTH))
 (585 542 (:REWRITE DEFAULT-+-2))
 (553 352 (:REWRITE DEFAULT-CDR))
 (542 542 (:REWRITE DEFAULT-+-1))
 (410 388 (:REWRITE DEFAULT-<-2))
 (391 388 (:REWRITE DEFAULT-<-1))
 (245 158 (:REWRITE DEFAULT-CAR))
 (229 85 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (186 11 (:REWRITE NTHCDR-PAST-UPDATE-NTH))
 (186 11 (:REWRITE NTHCDR-BEFORE-UPDATE-NTH))
 (130 130 (:TYPE-PRESCRIPTION LEN))
 (110 22 (:DEFINITION LEN))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(TAKE-BEFORE-UPDATE-NTH
 (407 24 (:REWRITE TAKE-OF-LEN-FREE))
 (211 20 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (202 202 (:TYPE-PRESCRIPTION LEN))
 (191 21 (:DEFINITION NTH))
 (189 3 (:REWRITE CDR-OF-UPDATE-NTH))
 (188 24 (:DEFINITION LEN))
 (159 59 (:REWRITE ZP-OPEN))
 (115 85 (:REWRITE DEFAULT-+-2))
 (85 85 (:REWRITE DEFAULT-+-1))
 (82 76 (:REWRITE DEFAULT-CDR))
 (77 4 (:REWRITE LEN-OF-UPDATE-NTH))
 (63 56 (:REWRITE DEFAULT-<-2))
 (56 56 (:REWRITE DEFAULT-<-1))
 (50 16 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:REWRITE DEFAULT-CAR))
 (28 4 (:DEFINITION MAX))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (18 18 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (10 10 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 3 (:REWRITE CAR-OF-UPDATE-NTH))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE CDR-CONS))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:DEFINITION FIX))
 )
(TAKE-AFTER-UPDATE-NTH
 (945 58 (:REWRITE TAKE-OF-LEN-FREE))
 (590 44 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (545 43 (:DEFINITION NTH))
 (454 454 (:TYPE-PRESCRIPTION LEN))
 (452 59 (:DEFINITION LEN))
 (396 6 (:REWRITE CDR-OF-UPDATE-NTH))
 (310 240 (:REWRITE DEFAULT-+-2))
 (280 197 (:REWRITE DEFAULT-CDR))
 (240 240 (:REWRITE DEFAULT-+-1))
 (198 192 (:REWRITE DEFAULT-<-2))
 (193 192 (:REWRITE DEFAULT-<-1))
 (123 6 (:REWRITE LEN-OF-UPDATE-NTH))
 (107 99 (:REWRITE DEFAULT-CAR))
 (76 12 (:REWRITE CAR-OF-TAKE))
 (69 28 (:REWRITE CONSP-OF-TAKE))
 (63 35 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (56 6 (:REWRITE TAKE-BEFORE-UPDATE-NTH))
 (42 6 (:DEFINITION MAX))
 (28 4 (:REWRITE SECOND-OF-TAKE))
 (27 6 (:REWRITE CAR-OF-UPDATE-NTH))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 3 (:REWRITE UNICITY-OF-0))
 (3 3 (:DEFINITION FIX))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NTH-0-CONS))
 )
(TAKE-OF-UPDATE-NTH
 (691 52 (:REWRITE TAKE-OF-LEN-FREE))
 (360 32 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (341 341 (:TYPE-PRESCRIPTION LEN))
 (331 49 (:DEFINITION LEN))
 (328 32 (:DEFINITION NTH))
 (240 90 (:REWRITE ZP-OPEN))
 (213 154 (:REWRITE DEFAULT-+-2))
 (197 147 (:REWRITE DEFAULT-CDR))
 (189 3 (:REWRITE CDR-OF-UPDATE-NTH))
 (154 154 (:REWRITE DEFAULT-+-1))
 (141 132 (:REWRITE DEFAULT-<-2))
 (136 132 (:REWRITE DEFAULT-<-1))
 (80 26 (:REWRITE FOLD-CONSTS-IN-+))
 (77 4 (:REWRITE LEN-OF-UPDATE-NTH))
 (76 72 (:REWRITE DEFAULT-CAR))
 (45 26 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (42 7 (:REWRITE CAR-OF-TAKE))
 (30 16 (:REWRITE CONSP-OF-TAKE))
 (28 4 (:DEFINITION MAX))
 (21 3 (:REWRITE SECOND-OF-TAKE))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE CAR-OF-UPDATE-NTH))
 (6 3 (:TYPE-PRESCRIPTION MAX))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:DEFINITION FIX))
 )
(MEMBER-EQUAL-UPDATE-NTH
 (195 3 (:REWRITE CDR-OF-UPDATE-NTH))
 (141 12 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (129 13 (:DEFINITION NTH))
 (116 34 (:REWRITE ZP-OPEN))
 (39 13 (:REWRITE FOLD-CONSTS-IN-+))
 (34 34 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE DEFAULT-+-1))
 (34 31 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-<-1))
 (26 23 (:REWRITE DEFAULT-CAR))
 (12 3 (:REWRITE CAR-OF-UPDATE-NTH))
 (11 11 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 )
(UPDATE-NTH-APPEND
 (857 65 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (702 71 (:DEFINITION NTH))
 (337 201 (:REWRITE DEFAULT-CAR))
 (244 198 (:REWRITE DEFAULT-+-2))
 (206 198 (:REWRITE DEFAULT-+-1))
 (173 74 (:REWRITE FOLD-CONSTS-IN-+))
 (159 144 (:REWRITE DEFAULT-<-2))
 (147 144 (:REWRITE DEFAULT-<-1))
 (56 38 (:REWRITE UPDATE-NTH-WHEN-ATOM))
 (30 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 10 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ELEMENT-LIST-P-OF-UPDATE-NTH
 (842 158 (:REWRITE ELEMENT-LIST-NONEMPTY-P-OF-CDR-WHEN-ELEMENT-LIST-NONEMPTY-P))
 (693 172 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (536 192 (:REWRITE ELEMENT-P-OF-CAR-WHEN-ELEMENT-LIST-P-WHEN-ELEMENT-P-NIL))
 (521 176 (:DEFINITION NTH))
 (517 503 (:REWRITE DEFAULT-<-1))
 (503 503 (:REWRITE DEFAULT-<-2))
 (426 385 (:REWRITE DEFAULT-+-2))
 (394 192 (:REWRITE ELEMENT-P-OF-CAR-WHEN-ELEMENT-LIST-P-WHEN-NOT-ELEMENT-P-NIL-AND-NOT-NEGATED))
 (385 385 (:REWRITE DEFAULT-+-1))
 )
(ELEMENTLIST-PROJECTION-OF-UPDATE-NTH
 (365 30 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (334 30 (:DEFINITION NTH))
 (250 4 (:REWRITE CDR-OF-UPDATE-NTH))
 (200 64 (:REWRITE ZP-OPEN))
 (76 72 (:REWRITE DEFAULT-CAR))
 (76 69 (:REWRITE DEFAULT-+-2))
 (71 64 (:REWRITE DEFAULT-<-1))
 (69 69 (:REWRITE DEFAULT-+-1))
 (64 64 (:REWRITE DEFAULT-<-2))
 (63 21 (:REWRITE FOLD-CONSTS-IN-+))
 (27 27 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 12 (:REWRITE CAR-OF-ELEMENTLIST-PROJECTION))
 (22 22 (:TYPE-PRESCRIPTION ZP))
 (15 4 (:REWRITE CAR-OF-UPDATE-NTH))
 (9 9 (:REWRITE CONSP-OF-ELEMENTLIST-PROJECTION))
 (1 1 (:REWRITE NTH-0-CONS))
 (1 1 (:REWRITE CDR-CONS))
 (1 1 (:REWRITE CAR-CONS))
 )
(ELEMENTLIST-PROJECTION-OF-UPDATE-NTH-NIL-PRESERVING
 (461 10 (:REWRITE CDR-OF-UPDATE-NTH))
 (429 119 (:REWRITE ZP-OPEN))
 (343 60 (:REWRITE UPDATE-NTH-OF-NTH-FREE))
 (283 60 (:DEFINITION NTH))
 (142 139 (:REWRITE DEFAULT-<-1))
 (139 139 (:REWRITE DEFAULT-<-2))
 (106 99 (:REWRITE DEFAULT-+-2))
 (106 34 (:REWRITE FOLD-CONSTS-IN-+))
 (104 10 (:REWRITE ELEMENTLIST-PROJECTION-OF-UPDATE-NTH))
 (99 99 (:REWRITE DEFAULT-+-1))
 (63 9 (:REWRITE CDR-OF-ELEMENTLIST-PROJECTION))
 (41 10 (:REWRITE CAR-OF-UPDATE-NTH))
 (30 10 (:DEFINITION NFIX))
 (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (22 22 (:TYPE-PRESCRIPTION LEN))
 (15 3 (:DEFINITION LEN))
 (14 7 (:REWRITE CAR-OF-ELEMENTLIST-PROJECTION))
 (10 10 (:TYPE-PRESCRIPTION NFIX))
 (5 5 (:REWRITE CONSP-OF-ELEMENTLIST-PROJECTION))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
