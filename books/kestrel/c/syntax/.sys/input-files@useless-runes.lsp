(C$::BYTE-LISTP-BECOMES-UNSIGNED-BYTE-LISTP-8
 (66 13 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
 (46 4 (:REWRITE BYTEP-OF-CAR-WHEN-BYTE-LISTP))
 (16 16 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
 (10 10 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
 )
(C$::BYTE-LISTP-OF-READ-FILE-INTO-BYTE-LIST)
(C$::INPUT-FILES-STRINGS-TO-PATHS)
(C$::FILEPATH-SETP-OF-INPUT-FILES-STRINGS-TO-PATHS
 (5 1 (:REWRITE SET::INSERT-IDENTITY))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 3 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (3 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (3 1 (:REWRITE C$::SETP-WHEN-TYPE-SETP))
 (3 1 (:REWRITE C$::SETP-WHEN-IDENT-SETP))
 (3 1 (:REWRITE C$::SETP-WHEN-IDENT-OPTION-SETP))
 (3 1 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (2 2 (:TYPE-PRESCRIPTION C$::TYPE-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-OPTION-SETP))
 (2 1 (:REWRITE SET::IN-TAIL))
 (1 1 (:REWRITE C$::FILEPATHP-WHEN-IN-FILEPATH-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C$::FILEPATHP-WHEN-ASSOC-FILEPATH-TRANSUNIT-MAPP-BINDS-FREE-X))
 (1 1 (:REWRITE C$::FILEPATHP-WHEN-ASSOC-FILEPATH-FILEDATA-MAPP-BINDS-FREE-X))
 )
(C$::INPUT-FILES-STRINGS-TO-PATHS
 (9 1 (:DEFINITION C$::INPUT-FILES-STRINGS-TO-PATHS))
 (5 1 (:REWRITE SET::INSERT-IDENTITY))
 (3 3 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (3 1 (:REWRITE C$::SETP-WHEN-TYPE-SETP))
 (3 1 (:REWRITE C$::SETP-WHEN-IDENT-SETP))
 (3 1 (:REWRITE C$::SETP-WHEN-IDENT-OPTION-SETP))
 (3 1 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (2 2 (:TYPE-PRESCRIPTION C$::TYPE-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-OPTION-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (2 1 (:REWRITE SET::IN-TAIL))
 (1 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 )
(C$::INPUT-FILES-PREPROCESS-INPUTP)
(C$::BOOLEANP-OF-INPUT-FILES-PREPROCESS-INPUTP)
(C$::INPUT-FILES-PROCESS-INPUTP)
(C$::BOOLEANP-OF-INPUT-FILES-PROCESS-INPUTP)
(C$::INPUT-FILES-PROCESS-FILES
 (6 1 (:REWRITE STRING-LISTP-OF-CDR-WHEN-STRING-LISTP))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (2 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::FILEPATH-SETP-OF-INPUT-FILES-PROCESS-FILES.PATHS
 (14 1 (:REWRITE STRING-LISTP-OF-CDR-WHEN-STRING-LISTP))
 (10 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (8 1 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION STRING-LISTP))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::INPUT-FILES-PROCESS-PREPROCESS
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::STRING-OPTIONP-OF-INPUT-FILES-PROCESS-PREPROCESS.PREPROCESSOR
 (25 7 (:REWRITE STRINGP-WHEN-STRING-OPTIONP))
 (14 14 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 )
(C$::INPUT-FILES-PROCESS-PROCESS
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::INPUT-FILES-PROCESS-INPUTP-OF-INPUT-FILES-PROCESS-PROCESS.PROCESS)
(C$::INPUT-FILES-PROCESS-CONST-INPUTS
 (20 5 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (10 10 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (7 2 (:REWRITE STRING-OPTIONP-WHEN-STRINGP))
 (5 5 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (5 5 (:REWRITE ALISTP-WHEN-ATOM))
 (4 1 (:REWRITE STRINGP-WHEN-STRING-OPTIONP))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-CONST-INPUTS.CONST)
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-CONST-INPUTS.CONST-FILES)
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-CONST-INPUTS.CONST-PREPROC)
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-CONST-INPUTS.CONST-PARSED)
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-CONST-INPUTS.CONST-DISAMB)
(C$::INPUT-FILES-PROCESS-GCC
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::BOOLEANP-OF-INPUT-FILES-PROCESS-GCC.GCC)
(C$::INPUT-FILES-PROCESS-IENV
 (20 5 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (10 10 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (5 5 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (5 5 (:REWRITE ALISTP-WHEN-ATOM))
 )
(C$::IENVP-OF-INPUT-FILES-PROCESS-IENV.IENV)
(C$::INPUT-FILES-PROCESS-INPUTS
 (14 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (6 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (2 2 (:TYPE-PRESCRIPTION STRING-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE C$::SETP-WHEN-TYPE-SETP))
 (2 1 (:REWRITE C$::SETP-WHEN-IDENT-SETP))
 (2 1 (:REWRITE C$::SETP-WHEN-IDENT-OPTION-SETP))
 (2 1 (:REWRITE C$::SETP-WHEN-FILEPATH-SETP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1 1 (:TYPE-PRESCRIPTION C$::TYPE-SETP))
 (1 1 (:TYPE-PRESCRIPTION C$::IDENT-SETP))
 (1 1 (:TYPE-PRESCRIPTION C$::IDENT-OPTION-SETP))
 (1 1 (:TYPE-PRESCRIPTION C$::FILEPATH-SETP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SET::IN-SET))
 )
(C$::FILEPATH-SETP-OF-INPUT-FILES-PROCESS-INPUTS.PATHS
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::STRING-OPTIONP-OF-INPUT-FILES-PROCESS-INPUTS.PREPROCESSOR
 (7 2 (:REWRITE STRING-OPTIONP-WHEN-STRINGP))
 (4 1 (:REWRITE STRINGP-WHEN-STRING-OPTIONP))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::INPUT-FILES-PROCESS-INPUTP-OF-INPUT-FILES-PROCESS-INPUTS.PROCESS
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-INPUTS.CONST
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-INPUTS.CONST-FILES
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-INPUTS.CONST-PREPROC
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-INPUTS.CONST-PARSED
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::SYMBOLP-OF-INPUT-FILES-PROCESS-INPUTS.CONST-DISAMB
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::BOOLEANP-OF-INPUT-FILES-PROCESS-INPUTS.GCC
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::IENVP-OF-INPUT-FILES-PROCESS-INPUTS.IENV
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PARTITION-REST-AND-KEYWORD.REST))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(C$::INPUT-FILES-READ-FILES)
(C$::FILESETP-OF-INPUT-FILES-READ-FILES.FILESET
 (96 24 (:REWRITE STRINGP-WHEN-STRING-OPTIONP))
 (60 12 (:REWRITE STRING-OPTIONP-WHEN-STRINGP))
 (48 48 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (36 36 (:TYPE-PRESCRIPTION STRING-OPTIONP))
 (29 29 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (29 29 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (4 4 (:REWRITE-QUOTED-CONSTANT C$::FILEPATH-FILEDATA-MAP-FIX-UNDER-FILEPATH-FILEDATA-MAP-EQUIV))
 (4 4 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE OMAP::UPDATE-WHEN-EMPTYP))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTYP))
 )
(C$::INPUT-FILES-READ-FILES)
(C$::INPUT-FILES-GEN-EVENTS
 (14 4 (:REWRITE STRING-OPTIONP-WHEN-STRINGP))
 (6 6 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 )
(C$::PSEUDO-EVENT-FORM-LISTP-OF-INPUT-FILES-GEN-EVENTS.EVENTS
 (1281 61 (:DEFINITION PSEUDO-EVENT-FORM-LISTP))
 (984 984 (:REWRITE PSEUDO-EVENT-FORM-LISTP-WHEN-SUBSETP-EQUAL))
 (618 618 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 (427 61 (:REWRITE PSEUDO-EVENT-FORMP-OF-CAR-WHEN-PSEUDO-EVENT-FORM-LISTP))
 (427 61 (:REWRITE PSEUDO-EVENT-FORM-LISTP-OF-CDR-WHEN-PSEUDO-EVENT-FORM-LISTP))
 (244 244 (:REWRITE PSEUDO-EVENT-FORM-LISTP-WHEN-NOT-CONSP))
 (61 61 (:TYPE-PRESCRIPTION PSEUDO-EVENT-FORMP))
 )
(C$::INPUT-FILES-PROCESS-INPUTS-AND-GEN-EVENTS)
(C$::PSEUDO-EVENT-FORMP-OF-INPUT-FILES-PROCESS-INPUTS-AND-GEN-EVENTS.EVENT
 (28 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (12 2 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (4 4 (:TYPE-PRESCRIPTION STRING-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 (4 2 (:REWRITE C$::SETP-WHEN-TYPE-SETP))
 (4 2 (:REWRITE C$::SETP-WHEN-IDENT-SETP))
 (4 2 (:REWRITE C$::SETP-WHEN-IDENT-OPTION-SETP))
 (4 2 (:REWRITE C$::SETP-WHEN-FILEPATH-SETP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION C$::TYPE-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::IDENT-OPTION-SETP))
 (2 2 (:TYPE-PRESCRIPTION C$::FILEPATH-SETP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SET::IN-SET))
 )
(C$::INPUT-FILES-FN)
(C$::PSEUDO-EVENT-FORMP-OF-INPUT-FILES-FN.EVENT
 (2 2 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 )
