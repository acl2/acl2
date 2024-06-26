(POSITIVE-WHEN-NATP)
(INTEGERP-WHEN-NATP)
(ACL2-NUMBERP-WHEN-INTEGERP)
(MAX-NAT-EXEC
 (10 4 (:REWRITE NATP-RW))
 (8 2 (:REWRITE INTEGERP-WHEN-NATP))
 (5 1 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MAX-NAT
 (5 5 (:TYPE-PRESCRIPTION MAX))
 )
(NATP-OF-MAX-NAT
 (44 11 (:REWRITE INTEGERP-WHEN-NATP))
 (39 18 (:REWRITE NATP-RW))
 (20 4 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (15 3 (:REWRITE DEFAULT-<-2))
 (15 3 (:REWRITE DEFAULT-<-1))
 (10 2 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(MAX-NAT-EXEC-REMOVAL
 (269 44 (:REWRITE DEFAULT-<-1))
 (264 54 (:REWRITE INTEGERP-WHEN-NATP))
 (214 26 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (179 83 (:REWRITE NATP-RW))
 (164 44 (:REWRITE DEFAULT-<-2))
 (92 92 (:REWRITE DEFAULT-CDR))
 (84 84 (:REWRITE DEFAULT-CAR))
 (62 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (44 44 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(MAX-NAT
 (105 6 (:REWRITE DEFAULT-<-1))
 (72 6 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (60 9 (:REWRITE INTEGERP-WHEN-NATP))
 (27 12 (:REWRITE NATP-RW))
 (24 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 6 (:REWRITE DEFAULT-<-2))
 (23 5 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (18 18 (:TYPE-PRESCRIPTION NATP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(MAX-NAT-AND-LEN
 (15 6 (:REWRITE NATP-RW))
 (12 3 (:REWRITE INTEGERP-WHEN-NATP))
 (5 1 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MAX-NAT-AND-LEN-REMOVAL
 (302 75 (:REWRITE INTEGERP-WHEN-NATP))
 (256 119 (:REWRITE NATP-RW))
 (228 60 (:REWRITE DEFAULT-<-2))
 (161 145 (:REWRITE DEFAULT-CDR))
 (158 30 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (151 109 (:REWRITE DEFAULT-+-2))
 (147 131 (:REWRITE DEFAULT-CAR))
 (147 60 (:REWRITE DEFAULT-<-1))
 (109 109 (:REWRITE DEFAULT-+-1))
 (73 33 (:REWRITE FOLD-CONSTS-IN-+))
 (60 60 (:META CANCEL_PLUS-LESSP-CORRECT))
 (42 42 (:TYPE-PRESCRIPTION LEN))
 (36 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(HONS-REMOVE-DUPLICATES1-TAIL)
(HONS-REMOVE-DUPLICATES1-TAIL-REMOVAL
 (127 116 (:REWRITE DEFAULT-CAR))
 (70 59 (:REWRITE DEFAULT-CDR))
 (23 23 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (23 23 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NAT-REMOVE-DUPS-VERY-SHORT-P)
(NAT-REMOVE-DUPS-WHEN-VERY-SHORT
 (26 11 (:REWRITE NATP-RW))
 (20 5 (:REWRITE INTEGERP-WHEN-NATP))
 (14 14 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 1 (:DEFINITION MEMBER-EQUAL))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NAT-REMOVE-DUPS-WHEN-VERY-SHORT-SOLO
 (26 11 (:REWRITE NATP-RW))
 (20 5 (:REWRITE INTEGERP-WHEN-NATP))
 (14 14 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 1 (:DEFINITION MEMBER-EQUAL))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(L1
 (58 56 (:REWRITE DEFAULT-CAR))
 (47 45 (:REWRITE DEFAULT-CDR))
 (20 20 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (20 20 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 3 (:REWRITE CDR-CONS))
 (3 3 (:REWRITE CAR-CONS))
 )
(NAT-REMOVE-DUPS-WHEN-VERY-SHORT-SOLO-REMOVAL)
(DUMB-MAKE-TABLE)
(HONS-ASSOC-EQUAL-DUMB-MAKE-TABLE
 (68 61 (:REWRITE DEFAULT-CAR))
 (30 28 (:REWRITE DEFAULT-CDR))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NAT-REMOVE-DUPS-WHEN-VERY-SHORT-REMOVAL
 (121 101 (:REWRITE DEFAULT-CAR))
 (82 68 (:REWRITE DEFAULT-CDR))
 (78 3 (:DEFINITION HONS-ASSOC-EQUAL))
 (26 26 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (26 26 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (15 15 (:TYPE-PRESCRIPTION DUMB-MAKE-TABLE))
 (9 3 (:DEFINITION HONS-EQUAL))
 )
(NATP-OF-NAT-REMOVE-DUPS-ARRP
 (72 72 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (57 18 (:REWRITE NATP-RW))
 (42 12 (:REWRITE INTEGERP-WHEN-NATP))
 (27 27 (:REWRITE DEFAULT-CAR))
 (26 16 (:REWRITE DEFAULT-<-2))
 (26 15 (:REWRITE DEFAULT-+-2))
 (17 16 (:REWRITE DEFAULT-<-1))
 (16 16 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (16 16 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 16 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (15 15 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 )
(NATP-OF-NAT-REMOVE-DUPS-ARRI)
(UPPER-BOUND-OF-NAT-REMOVE-DUPS-ARRP
 (178 37 (:REWRITE DEFAULT-<-1))
 (152 26 (:REWRITE INTEGERP-WHEN-NATP))
 (132 14 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (82 82 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (68 6 (:REWRITE NATP-OF-NAT-REMOVE-DUPS-ARRP))
 (55 55 (:TYPE-PRESCRIPTION NATP))
 (53 37 (:REWRITE DEFAULT-<-2))
 (50 21 (:REWRITE NATP-RW))
 (43 43 (:REWRITE DEFAULT-CAR))
 (40 22 (:REWRITE DEFAULT-+-2))
 (37 37 (:META CANCEL_PLUS-LESSP-CORRECT))
 (29 29 (:REWRITE DEFAULT-CDR))
 (28 28 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (28 28 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (22 22 (:REWRITE DEFAULT-+-1))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE ZP-OPEN))
 )
(UPPER-BOUND-OF-NAT-REMOVE-DUPS-ARRI)
(UPDATE-NAT-REMOVE-DUPS-ARRI-PRESERVES-LEN
 (58 31 (:REWRITE DEFAULT-+-2))
 (31 31 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE DEFAULT-CAR))
 (18 6 (:REWRITE INTEGERP-WHEN-NATP))
 (16 5 (:REWRITE NATP-RW))
 (14 14 (:TYPE-PRESCRIPTION NATP))
 (14 8 (:REWRITE DEFAULT-<-1))
 (11 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NAT-REMOVE-DUPS-ARRI-OF-UPDATE-NAT-REMOVE-DUPS-ARRI-DIFF
 (10 4 (:REWRITE NATP-RW))
 (10 2 (:DEFINITION LEN))
 (9 2 (:DEFINITION UPDATE-NTH))
 (8 2 (:REWRITE INTEGERP-WHEN-NATP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NAT-REMOVE-DUPS-ARR-LENGTH-OF-RESIZE-NAT-REMOVE-DUPS-ARR
 (71 3 (:REWRITE RESIZE-LIST-OF-LEN-FREE))
 (71 1 (:DEFINITION RESIZE-LIST))
 (31 8 (:REWRITE POSITIVE-WHEN-NATP))
 (30 7 (:REWRITE NATP-RW))
 (24 8 (:REWRITE INTEGERP-WHEN-NATP))
 (21 21 (:TYPE-PRESCRIPTION NATP))
 (19 2 (:REWRITE RESIZE-LIST-WHEN-ZP))
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (12 2 (:REWRITE ZP-OPEN))
 (11 3 (:DEFINITION LEN))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE EQUAL-CONSTANT-+))
 (4 1 (:REWRITE <-0-+-NEGATIVE-1))
 (4 1 (:DEFINITION NOT))
 (3 3 (:TYPE-PRESCRIPTION ZP))
 (3 3 (:REWRITE RESIZE-LIST-WHEN-ATOM))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(NAT-REMOVE-DUPS-ARR-LENGTH-OF-CREATE-NAT-REMOVE-DUPS-STOBJ)
(NAT-REMOVE-DUPS-ARRI-OF-RESIZE-NAT-REMOVE-DUPS-ARR
 (65 1 (:DEFINITION RESIZE-LIST))
 (55 3 (:REWRITE RESIZE-LIST-OF-LEN-FREE))
 (21 5 (:DEFINITION LEN))
 (16 2 (:REWRITE RESIZE-LIST-WHEN-ZP))
 (13 3 (:REWRITE ZP-OPEN))
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (12 8 (:REWRITE DEFAULT-+-2))
 (10 4 (:REWRITE NATP-RW))
 (9 7 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 2 (:REWRITE INTEGERP-WHEN-NATP))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE EQUAL-CONSTANT-+))
 (4 1 (:REWRITE <-0-+-NEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION NFIX))
 (3 3 (:REWRITE RESIZE-LIST-WHEN-ATOM))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 )
(NAT-REMOVE-DUPS-WITH-STOBJ-AUX
 (304 90 (:REWRITE DEFAULT-<-2))
 (238 90 (:REWRITE DEFAULT-<-1))
 (90 90 (:META CANCEL_PLUS-LESSP-CORRECT))
 (75 75 (:REWRITE DEFAULT-CAR))
 (65 65 (:REWRITE DEFAULT-CDR))
 (60 60 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (52 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(NAT-LIST-REMOVE-DUPLICATES-EXEC)
(NAT-LIST-REMOVE-DUPLICATES)
(ALIST-AND-STOBJ-AGREE)
(ALIST-AND-STOBJ-AGREE-NECC)
(L0
 (95 38 (:REWRITE NATP-RW))
 (76 19 (:REWRITE INTEGERP-WHEN-NATP))
 (64 64 (:REWRITE DEFAULT-CAR))
 (29 29 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (29 29 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (24 24 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 24 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(ALIST-AND-STOBJ-STILL-AGREE-AFTER-EXTENSION
 (962 381 (:REWRITE NATP-RW))
 (780 200 (:REWRITE INTEGERP-WHEN-NATP))
 (397 397 (:REWRITE DEFAULT-CAR))
 (311 223 (:REWRITE DEFAULT-<-2))
 (244 223 (:REWRITE DEFAULT-<-1))
 (223 223 (:META CANCEL_PLUS-LESSP-CORRECT))
 (163 163 (:REWRITE DEFAULT-CDR))
 (160 160 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (160 160 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (142 142 (:REWRITE ALIST-AND-STOBJ-AGREE-NECC))
 (16 5 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALIST-AND-STOBJ-AGREE-CONSEQUENCE)
(MY-INDUCT)
(NAT-REMOVE-DUPS-WITH-STOBJ-AUX-ELIM
 (1054 56 (:DEFINITION HONS-ASSOC-EQUAL))
 (807 805 (:REWRITE DEFAULT-CAR))
 (782 178 (:REWRITE DEFAULT-<-1))
 (696 159 (:REWRITE INTEGERP-WHEN-NATP))
 (553 236 (:REWRITE NATP-RW))
 (523 521 (:REWRITE DEFAULT-CDR))
 (484 52 (:REWRITE ACL2-NUMBERP-WHEN-INTEGERP))
 (397 178 (:REWRITE DEFAULT-<-2))
 (178 178 (:META CANCEL_PLUS-LESSP-CORRECT))
 (173 173 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (173 173 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (168 56 (:DEFINITION HONS-EQUAL))
 (148 52 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (144 12 (:REWRITE NAT-REMOVE-DUPS-ARRI-OF-UPDATE-NAT-REMOVE-DUPS-ARRI-DIFF))
 (33 33 (:REWRITE ALIST-AND-STOBJ-AGREE-NECC))
 )
(NAT-REMOVE-DUPS-WITH-STOBJ-AUX-WHEN-ATOM)
(BASE-CASE
 (5 2 (:REWRITE NATP-RW))
 (4 1 (:REWRITE INTEGERP-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ALIST-AND-STOBJ-AGREE-NECC))
 (1 1 (:REWRITE ALIST-AND-STOBJ-AGREE-CONSEQUENCE))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(MY-INDUCT)
(ALIST-EQUIV-IMPLIES-EQUAL-HONS-REMOVE-DUPLICATES1-2
 (48 48 (:REWRITE DEFAULT-CAR))
 (32 4 (:REWRITE HONS-ASSOC-EQUAL-OF-CONS))
 (28 28 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (16 16 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (16 16 (:REWRITE ALIST-AND-STOBJ-AGREE-CONSEQUENCE))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE CAR-CONS))
 )
(CROCK)
(HONS-REMOVE-DUPLICATES1-ATOM-IRRELEVANCE)
(NAT-LIST-REMOVE-DUPLICATES-EXEC
 (121 121 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (108 50 (:REWRITE NATP-RW))
 (104 32 (:REWRITE INTEGERP-WHEN-NATP))
 (64 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (50 10 (:DEFINITION REVAPPEND))
 (48 28 (:REWRITE DEFAULT-<-1))
 (44 44 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (40 26 (:REWRITE DEFAULT-+-2))
 (40 8 (:DEFINITION LEN))
 (36 36 (:REWRITE DEFAULT-CDR))
 (33 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-+-1))
 (14 4 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (13 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:REWRITE HONS-REMOVE-DUPLICATES-WHEN-ATOM))
 (8 8 (:TYPE-PRESCRIPTION HONS-REMOVE-DUPLICATES1-TAIL))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE NATP-*))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE NAT-REMOVE-DUPS-WITH-STOBJ-AUX-WHEN-ATOM))
 )
(NAT-LIST-REMOVE-DUPLICATES)
