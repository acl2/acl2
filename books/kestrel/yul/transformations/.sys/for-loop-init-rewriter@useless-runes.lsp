(YUL::STATEMENT-LOOPINIT
 (48 16 (:REWRITE DEFAULT-<-2))
 (48 16 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(YUL::STATEMENTS/BLOCKS/CASES/FUNDEFS-LOOPINIT-FLAG
 (48 16 (:REWRITE DEFAULT-<-2))
 (48 16 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(YUL::STATEMENTS/BLOCKS/CASES/FUNDEFS-LOOPINIT-FLAG-EQUIVALENCES)
(YUL::FLAG-LEMMA-FOR-RETURN-TYPE-OF-STATEMENT-LOOPINIT.NEW-STMT
 (383 69 (:REWRITE YUL::BLOCKP-WHEN-BLOCK-OPTIONP))
 (308 182 (:REWRITE YUL::STATEMENTP-WHEN-MEMBER-EQUAL-OF-STATEMENT-LISTP))
 (196 14 (:DEFINITION MEMBER-EQUAL))
 (106 16 (:REWRITE YUL::SWCASEP-WHEN-MEMBER-EQUAL-OF-SWCASE-LISTP))
 (74 19 (:REWRITE YUL::STATEMENT-LISTP-WHEN-NOT-CONSP))
 (72 72 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (58 15 (:REWRITE YUL::SWCASE-LISTP-WHEN-NOT-CONSP))
 (50 5 (:REWRITE YUL::STATEMENT-FIX-WHEN-STATEMENTP))
 (46 2 (:REWRITE SUBSETP-OF-CONS))
 (28 28 (:REWRITE SUBSETP-MEMBER . 2))
 (28 28 (:REWRITE SUBSETP-MEMBER . 1))
 (25 25 (:REWRITE DEFAULT-CDR))
 (25 25 (:REWRITE DEFAULT-CAR))
 (24 6 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (24 6 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (16 16 (:REWRITE YUL::FUNDEFP-WHEN-MEMBER-EQUAL-OF-FUNDEF-LISTP))
 (12 12 (:REWRITE SUBSETP-TRANS2))
 (12 12 (:REWRITE SUBSETP-TRANS))
 (7 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:REWRITE YUL::STATEMENT-FIX-WHEN-LEAVE))
 (5 5 (:REWRITE YUL::STATEMENT-FIX-WHEN-CONTINUE))
 (5 5 (:REWRITE YUL::STATEMENT-FIX-WHEN-BREAK))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (2 2 (:REWRITE-QUOTED-CONSTANT YUL::STATEMENT-LIST-FIX-UNDER-STATEMENT-LIST-EQUIV))
 (2 2 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 )
(YUL::RETURN-TYPE-OF-STATEMENT-LOOPINIT.NEW-STMT)
(YUL::RETURN-TYPE-OF-STATEMENT-LIST-LOOPINIT.NEW-STMT)
(YUL::RETURN-TYPE-OF-BLOCK-LOOPINIT.NEW-BLOCK)
(YUL::RETURN-TYPE-OF-BLOCK-OPTION-LOOPINIT.NEW-BLOCK?)
(YUL::RETURN-TYPE-OF-SWCASE-LOOPINIT.NEW-CASE)
(YUL::RETURN-TYPE-OF-SWCASE-LIST-LOOPINIT.NEW-CASES)
(YUL::RETURN-TYPE-OF-FUNDEF-LOOPINIT.NEW-FDEF)
(YUL::STATEMENT-LOOPINIT
 (10 2 (:DEFINITION YUL::STATEMENT-LIST-LOOPINIT))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE YUL::STATEMENT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:DEFINITION YUL::BLOCK-LOOPINIT))
 (1 1 (:REWRITE-QUOTED-CONSTANT YUL::BLOCK-OPTION-FIX-UNDER-BLOCK-OPTION-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT YUL::BLOCK-FIX-UNDER-BLOCK-EQUIV))
 (1 1 (:REWRITE YUL::SWCASE-LISTP-WHEN-NOT-CONSP))
 )
(YUL::FLAG-LEMMA-FOR-STATEMENT-LOOPINIT-OF-STATEMENT-FIX-STMT
 (342 185 (:REWRITE DEFAULT-CDR))
 (342 185 (:REWRITE DEFAULT-CAR))
 (275 53 (:REWRITE YUL::STATEMENTP-WHEN-STATEMENT-OPTIONP))
 (116 53 (:REWRITE YUL::STATEMENT-OPTIONP-WHEN-STATEMENTP))
 (108 12 (:REWRITE YUL::SWCASE-FIX-WHEN-SWCASEP))
 (106 106 (:TYPE-PRESCRIPTION YUL::STATEMENT-OPTIONP))
 (96 96 (:REWRITE YUL::STATEMENTP-WHEN-MEMBER-EQUAL-OF-STATEMENT-LISTP))
 (72 72 (:REWRITE YUL::SWCASE-LISTP-WHEN-SUBSETP-EQUAL))
 (72 72 (:REWRITE YUL::STATEMENT-LISTP-WHEN-SUBSETP-EQUAL))
 (48 8 (:REWRITE YUL::SWCASEP-OF-CAR-WHEN-SWCASE-LISTP))
 (48 8 (:REWRITE YUL::SWCASE-LISTP-OF-CDR-WHEN-SWCASE-LISTP))
 (48 8 (:REWRITE YUL::STATEMENTP-OF-CAR-WHEN-STATEMENT-LISTP))
 (48 8 (:REWRITE YUL::STATEMENT-LISTP-OF-CDR-WHEN-STATEMENT-LISTP))
 (40 36 (:REWRITE YUL::SWCASE-LISTP-WHEN-NOT-CONSP))
 (40 36 (:REWRITE YUL::STATEMENT-LISTP-WHEN-NOT-CONSP))
 (28 8 (:REWRITE YUL::BLOCKP-WHEN-BLOCK-OPTIONP))
 (28 8 (:REWRITE YUL::BLOCK-OPTIONP-WHEN-BLOCKP))
 (24 24 (:TYPE-PRESCRIPTION YUL::SWCASEP))
 (24 24 (:REWRITE YUL::SWCASEP-WHEN-MEMBER-EQUAL-OF-SWCASE-LISTP))
 (14 2 (:DEFINITION BINARY-APPEND))
 (10 10 (:REWRITE YUL::FUNDEFP-WHEN-MEMBER-EQUAL-OF-FUNDEF-LISTP))
 (7 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (6 5 (:REWRITE YUL::BLOCK-OPTION-FIX-WHEN-NONE))
 (4 4 (:REWRITE-QUOTED-CONSTANT YUL::STATEMENT-LIST-FIX-UNDER-STATEMENT-LIST-EQUIV))
 (4 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (1 1 (:TYPE-PRESCRIPTION YUL::STATEMENT-SWITCH->DEFAULT$INLINE))
 )
(YUL::STATEMENT-LOOPINIT-OF-STATEMENT-FIX-STMT)
(YUL::STATEMENT-LIST-LOOPINIT-OF-STATEMENT-LIST-FIX-STMTS)
(YUL::BLOCK-LOOPINIT-OF-BLOCK-FIX-BLOCK)
(YUL::BLOCK-OPTION-LOOPINIT-OF-BLOCK-OPTION-FIX-BLOCK?)
(YUL::SWCASE-LOOPINIT-OF-SWCASE-FIX-CASE)
(YUL::SWCASE-LIST-LOOPINIT-OF-SWCASE-LIST-FIX-CASES)
(YUL::FUNDEF-LOOPINIT-OF-FUNDEF-FIX-FDEF)
(YUL::STATEMENT-LOOPINIT-STATEMENT-EQUIV-CONGRUENCE-ON-STMT)
(YUL::STATEMENT-LIST-LOOPINIT-STATEMENT-LIST-EQUIV-CONGRUENCE-ON-STMTS)
(YUL::BLOCK-LOOPINIT-BLOCK-EQUIV-CONGRUENCE-ON-BLOCK)
(YUL::BLOCK-OPTION-LOOPINIT-BLOCK-OPTION-EQUIV-CONGRUENCE-ON-BLOCK?)
(YUL::SWCASE-LOOPINIT-SWCASE-EQUIV-CONGRUENCE-ON-CASE)
(YUL::SWCASE-LIST-LOOPINIT-SWCASE-LIST-EQUIV-CONGRUENCE-ON-CASES)
(YUL::FUNDEF-LOOPINIT-FUNDEF-EQUIV-CONGRUENCE-ON-FDEF)
