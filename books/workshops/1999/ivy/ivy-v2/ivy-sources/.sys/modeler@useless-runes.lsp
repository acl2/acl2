(EXTERNAL-MODELER)
(MODEL-ATTEMPT
 (11651 49 (:DEFINITION VARS-IN-TERM-LIST))
 (11004 7 (:REWRITE FREE-OCCURRENCE-REMOVE-FREE-VARS))
 (10983 7 (:DEFINITION FREE-OCCURRENCE))
 (9492 42 (:REWRITE NOT-VARS-IN-TERM-LIST-NOT-VAR-OCCURRENCE-TERM-LIST))
 (8694 7 (:DEFINITION VAR-OCCURRENCE-TERM-LIST))
 (5042 56 (:DEFINITION UNION-EQUAL))
 (4652 578 (:DEFINITION DOMAIN-TERM-LIST))
 (3832 432 (:REWRITE DOMAIN-TERM-LIST-HAS-NO-VARS))
 (2974 2974 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (2887 343 (:REWRITE SUBSET-UNION-2))
 (2566 336 (:REWRITE UNION-15))
 (2040 2039 (:REWRITE DEFAULT-CDR))
 (1848 168 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (1835 1834 (:REWRITE DEFAULT-CAR))
 (1659 133 (:DEFINITION SUBSETP-EQUAL))
 (1638 224 (:DEFINITION MEMBER-EQUAL))
 (1568 56 (:DEFINITION WF-AP-TERM-TOP))
 (1355 1355 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (1209 84 (:DEFINITION TRUE-LISTP))
 (707 273 (:REWRITE UNION-NOT-NIL-IF-EITHER-ARGUMENT-IS-A-CONS))
 (578 28 (:REWRITE UNION-NIL-RIGHT))
 (560 560 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (504 112 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (462 42 (:REWRITE VARIABLE-NOT-IN-DOMAIN-TERM-LIST-A))
 (394 2 (:DEFINITION NNF))
 (350 7 (:DEFINITION QUANTIFIED-VARS))
 (343 49 (:REWRITE SUBSET-MEMBER-SUBSET-CONS))
 (336 112 (:REWRITE NOT-DOMAIN-TERM-NOT-DOMAIN-TERM-LIST))
 (336 84 (:REWRITE UNION-NIL-LEFT))
 (322 322 (:REWRITE PERM-MEMBER))
 (322 322 (:REWRITE MEMBER-EQUAL-APPEND))
 (322 322 (:REWRITE FIRST-OF-SUBBAG-IS-MEMBER))
 (315 315 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (261 87 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (175 175 (:REWRITE SUBSETP-EQUAL-TRANSITIVE))
 (112 112 (:REWRITE SUBBAG-NOT-MEMBER))
 (112 112 (:REWRITE NOT-MEMBER-SUBSET))
 (91 91 (:TYPE-PRESCRIPTION VAR-OCCURRENCE-TERM-LIST))
 (89 1 (:DEFINITION CNF))
 (87 87 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (84 84 (:TYPE-PRESCRIPTION FREE-OCCURRENCE))
 (84 45 (:TYPE-PRESCRIPTION CNF))
 (69 7 (:DEFINITION REMOVE-EQUAL))
 (69 3 (:DEFINITION REMOVE-LEADING-ALLS))
 (59 59 (:DEFINITION FUNCTION-SYMBOL))
 (56 56 (:REWRITE WF-AP-TERM-TOP-CONSP))
 (54 3 (:DEFINITION WFT-LIST))
 (51 3 (:DEFINITION WFALL))
 (49 49 (:REWRITE CAR-CONS))
 (48 48 (:TYPE-PRESCRIPTION PULL-QUANTS))
 (41 8 (:DEFINITION BINARY-APPEND))
 (36 1 (:DEFINITION DIST-OR-AND))
 (30 3 (:DEFINITION WFAND))
 (20 1 (:DEFINITION INITIAL-PROOF))
 (18 1 (:DEFINITION DIST-OR-AND-2))
 (14 14 (:TYPE-PRESCRIPTION QUANTIFIED-VARS))
 (7 7 (:REWRITE VARS-IN-TERM-LIST-TRUE-LISTP))
 (7 7 (:REWRITE FREE-VARS-TRUE-LISTP))
 (5 5 (:REWRITE PERM-SETP-SETP))
 (1 1 (:REWRITE PERM-NOT-SETP-NOT-SETP))
 )
(MODEL-ATTEMPT-FSOUND
 (4941 21 (:DEFINITION VARS-IN-TERM-LIST))
 (4716 3 (:REWRITE FREE-OCCURRENCE-REMOVE-FREE-VARS))
 (4707 3 (:DEFINITION FREE-OCCURRENCE))
 (4068 18 (:REWRITE NOT-VARS-IN-TERM-LIST-NOT-VAR-OCCURRENCE-TERM-LIST))
 (3726 3 (:DEFINITION VAR-OCCURRENCE-TERM-LIST))
 (2106 24 (:DEFINITION UNION-EQUAL))
 (1980 246 (:DEFINITION DOMAIN-TERM-LIST))
 (1620 180 (:REWRITE DOMAIN-TERM-LIST-HAS-NO-VARS))
 (1302 1287 (:REWRITE DEFAULT-CDR))
 (1266 1266 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (1227 147 (:REWRITE SUBSET-UNION-2))
 (1098 144 (:REWRITE UNION-15))
 (1089 1083 (:REWRITE DEFAULT-CAR))
 (792 72 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (711 57 (:DEFINITION SUBSETP-EQUAL))
 (702 96 (:DEFINITION MEMBER-EQUAL))
 (672 24 (:DEFINITION WF-AP-TERM-TOP))
 (591 3 (:DEFINITION NNF))
 (579 579 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (558 558 (:TYPE-PRESCRIPTION VARS-IN-TERM-LIST))
 (513 36 (:DEFINITION TRUE-LISTP))
 (336 246 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (303 117 (:REWRITE UNION-NOT-NIL-IF-EITHER-ARGUMENT-IS-A-CONS))
 (267 3 (:DEFINITION CNF))
 (246 12 (:REWRITE UNION-NIL-RIGHT))
 (240 240 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (216 48 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (198 18 (:REWRITE VARIABLE-NOT-IN-DOMAIN-TERM-LIST-A))
 (147 21 (:REWRITE SUBSET-MEMBER-SUBSET-CONS))
 (144 48 (:REWRITE NOT-DOMAIN-TERM-NOT-DOMAIN-TERM-LIST))
 (144 36 (:REWRITE UNION-NIL-LEFT))
 (138 138 (:REWRITE PERM-MEMBER))
 (138 138 (:REWRITE MEMBER-EQUAL-APPEND))
 (138 138 (:REWRITE FIRST-OF-SUBBAG-IS-MEMBER))
 (135 135 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (117 39 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (108 3 (:DEFINITION DIST-OR-AND))
 (75 75 (:REWRITE SUBSETP-EQUAL-TRANSITIVE))
 (69 3 (:DEFINITION REMOVE-LEADING-ALLS))
 (60 3 (:DEFINITION INITIAL-PROOF))
 (54 3 (:DEFINITION WFT-LIST))
 (54 3 (:DEFINITION DIST-OR-AND-2))
 (51 3 (:DEFINITION WFALL))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 48 (:REWRITE SUBBAG-NOT-MEMBER))
 (48 48 (:REWRITE NOT-MEMBER-SUBSET))
 (48 36 (:TYPE-PRESCRIPTION CNF))
 (39 39 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (39 39 (:TYPE-PRESCRIPTION VAR-OCCURRENCE-TERM-LIST))
 (36 36 (:TYPE-PRESCRIPTION PULL-QUANTS))
 (36 36 (:TYPE-PRESCRIPTION FREE-OCCURRENCE))
 (30 3 (:DEFINITION ASSIGN-IDS-TO-PRF))
 (27 27 (:TYPE-PRESCRIPTION INITIAL-PROOF))
 (27 27 (:DEFINITION FUNCTION-SYMBOL))
 (24 24 (:REWRITE WF-AP-TERM-TOP-CONSP))
 (21 21 (:REWRITE CAR-CONS))
 (21 3 (:DEFINITION REMOVE-EQUAL))
 (18 3 (:DEFINITION BINARY-APPEND))
 (3 3 (:REWRITE VARS-IN-TERM-LIST-TRUE-LISTP))
 (3 3 (:REWRITE FREE-VARS-TRUE-LISTP))
 )
(COUNTERMODEL-ATTEMPT
 (3296 14 (:DEFINITION VARS-IN-TERM-LIST))
 (3144 2 (:REWRITE FREE-OCCURRENCE-REMOVE-FREE-VARS))
 (3138 2 (:DEFINITION FREE-OCCURRENCE))
 (2712 12 (:REWRITE NOT-VARS-IN-TERM-LIST-NOT-VAR-OCCURRENCE-TERM-LIST))
 (2484 2 (:DEFINITION VAR-OCCURRENCE-TERM-LIST))
 (1408 16 (:DEFINITION UNION-EQUAL))
 (1320 164 (:DEFINITION DOMAIN-TERM-LIST))
 (1080 120 (:REWRITE DOMAIN-TERM-LIST-HAS-NO-VARS))
 (844 844 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (818 98 (:REWRITE SUBSET-UNION-2))
 (736 96 (:REWRITE UNION-15))
 (528 48 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (504 504 (:REWRITE DEFAULT-CDR))
 (474 38 (:DEFINITION SUBSETP-EQUAL))
 (468 64 (:DEFINITION MEMBER-EQUAL))
 (463 463 (:REWRITE DEFAULT-CAR))
 (448 16 (:DEFINITION WF-AP-TERM-TOP))
 (386 386 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (374 374 (:TYPE-PRESCRIPTION VARS-IN-TERM-LIST))
 (342 24 (:DEFINITION TRUE-LISTP))
 (224 164 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (202 78 (:REWRITE UNION-NOT-NIL-IF-EITHER-ARGUMENT-IS-A-CONS))
 (168 8 (:REWRITE UNION-NIL-RIGHT))
 (160 160 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (144 32 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (132 12 (:REWRITE VARIABLE-NOT-IN-DOMAIN-TERM-LIST-A))
 (124 4 (:DEFINITION WFATOMTOP))
 (98 14 (:REWRITE SUBSET-MEMBER-SUBSET-CONS))
 (96 32 (:REWRITE NOT-DOMAIN-TERM-NOT-DOMAIN-TERM-LIST))
 (96 24 (:REWRITE UNION-NIL-LEFT))
 (92 92 (:REWRITE PERM-MEMBER))
 (92 92 (:REWRITE MEMBER-EQUAL-APPEND))
 (92 92 (:REWRITE FIRST-OF-SUBBAG-IS-MEMBER))
 (90 90 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (90 6 (:DEFINITION WFQUANT))
 (78 26 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (72 12 (:DEFINITION LIST3P))
 (66 6 (:DEFINITION WFBINARY))
 (56 56 (:DEFINITION VARIABLE-TERM))
 (50 50 (:REWRITE SUBSETP-EQUAL-TRANSITIVE))
 (36 2 (:DEFINITION WFT-LIST))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:REWRITE SUBBAG-NOT-MEMBER))
 (32 32 (:REWRITE NOT-MEMBER-SUBSET))
 (26 26 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (26 26 (:TYPE-PRESCRIPTION VAR-OCCURRENCE-TERM-LIST))
 (24 24 (:TYPE-PRESCRIPTION FREE-OCCURRENCE))
 (24 24 (:REWRITE MODEL-ATTEMPT-FSOUND))
 (18 18 (:DEFINITION FUNCTION-SYMBOL))
 (16 16 (:REWRITE WF-AP-TERM-TOP-CONSP))
 (14 2 (:DEFINITION REMOVE-EQUAL))
 (12 6 (:DEFINITION RELATION-SYMBOL))
 (6 6 (:DEFINITION LOGIC-SYMBOLP))
 (4 4 (:TYPE-PRESCRIPTION WFT-LIST))
 (2 2 (:REWRITE VARS-IN-TERM-LIST-TRUE-LISTP))
 (2 2 (:REWRITE FREE-VARS-TRUE-LISTP))
 )
(COUNTERMODEL-ATTEMPT-FSOUND
 (54045 248 (:REWRITE MODEL-ATTEMPT-FSOUND))
 (31773 133 (:DEFINITION VARS-IN-TERM-LIST))
 (29868 19 (:REWRITE FREE-OCCURRENCE-REMOVE-FREE-VARS))
 (29811 19 (:DEFINITION FREE-OCCURRENCE))
 (25764 114 (:REWRITE NOT-VARS-IN-TERM-LIST-NOT-VAR-OCCURRENCE-TERM-LIST))
 (23598 19 (:DEFINITION VAR-OCCURRENCE-TERM-LIST))
 (13850 152 (:DEFINITION UNION-EQUAL))
 (12668 1574 (:DEFINITION DOMAIN-TERM-LIST))
 (11290 11105 (:REWRITE DEFAULT-CDR))
 (10468 1188 (:REWRITE DOMAIN-TERM-LIST-HAS-NO-VARS))
 (9057 8983 (:REWRITE DEFAULT-CAR))
 (8098 8098 (:TYPE-PRESCRIPTION DOMAIN-TERM-LIST))
 (7867 931 (:REWRITE SUBSET-UNION-2))
 (7281 37 (:DEFINITION NNF))
 (6954 912 (:REWRITE UNION-15))
 (5016 456 (:REWRITE DOMAIN-TERM-LIST-TRUE-LISTP))
 (4503 361 (:DEFINITION SUBSETP-EQUAL))
 (4446 608 (:DEFINITION MEMBER-EQUAL))
 (4256 152 (:DEFINITION WF-AP-TERM-TOP))
 (3742 3742 (:TYPE-PRESCRIPTION VARS-IN-TERM-LIST))
 (3699 3699 (:TYPE-PRESCRIPTION DOMAIN-TERM))
 (3297 228 (:DEFINITION TRUE-LISTP))
 (3293 37 (:DEFINITION CNF))
 (2448 1718 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (1919 741 (:REWRITE UNION-NOT-NIL-IF-EITHER-ARGUMENT-IS-A-CONS))
 (1558 76 (:REWRITE UNION-NIL-RIGHT))
 (1520 1520 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (1368 304 (:REWRITE DOMAIN-TERM-LIST-MEMBER))
 (1332 37 (:DEFINITION DIST-OR-AND))
 (1254 114 (:REWRITE VARIABLE-NOT-IN-DOMAIN-TERM-LIST-A))
 (931 133 (:REWRITE SUBSET-MEMBER-SUBSET-CONS))
 (912 304 (:REWRITE NOT-DOMAIN-TERM-NOT-DOMAIN-TERM-LIST))
 (912 228 (:REWRITE UNION-NIL-LEFT))
 (874 874 (:REWRITE PERM-MEMBER))
 (874 874 (:REWRITE MEMBER-EQUAL-APPEND))
 (874 874 (:REWRITE FIRST-OF-SUBBAG-IS-MEMBER))
 (855 855 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (851 37 (:DEFINITION REMOVE-LEADING-ALLS))
 (741 247 (:REWRITE VARIABLE-TERM-IS-NOT-DOMAIN-TERM))
 (740 37 (:DEFINITION INITIAL-PROOF))
 (666 37 (:DEFINITION DIST-OR-AND-2))
 (629 37 (:DEFINITION WFALL))
 (592 444 (:TYPE-PRESCRIPTION CNF))
 (486 19 (:DEFINITION WFT-LIST))
 (475 475 (:REWRITE SUBSETP-EQUAL-TRANSITIVE))
 (444 444 (:TYPE-PRESCRIPTION PULL-QUANTS))
 (370 37 (:DEFINITION ASSIGN-IDS-TO-PRF))
 (368 368 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (333 333 (:TYPE-PRESCRIPTION INITIAL-PROOF))
 (304 304 (:REWRITE SUBBAG-NOT-MEMBER))
 (304 304 (:REWRITE NOT-MEMBER-SUBSET))
 (247 247 (:TYPE-PRESCRIPTION VARIABLE-TERM))
 (247 247 (:TYPE-PRESCRIPTION VAR-OCCURRENCE-TERM-LIST))
 (228 228 (:TYPE-PRESCRIPTION FREE-OCCURRENCE))
 (222 37 (:DEFINITION BINARY-APPEND))
 (213 19 (:DEFINITION REMOVE-EQUAL))
 (171 171 (:DEFINITION FUNCTION-SYMBOL))
 (152 152 (:REWRITE WF-AP-TERM-TOP-CONSP))
 (80 80 (:TYPE-PRESCRIPTION REMOVE-EQUAL))
 (62 62 (:TYPE-PRESCRIPTION FEVAL-D))
 (31 31 (:TYPE-PRESCRIPTION EVAL-ATOMIC))
 (19 19 (:REWRITE VARS-IN-TERM-LIST-TRUE-LISTP))
 (19 19 (:REWRITE FREE-VARS-TRUE-LISTP))
 )
