(SV::BOOTHPIPE-RUN)
(SV::SVTV-P-OF-BOOTHPIPE-RUN)
(SV::SVTV->OUTS-OF-BOOTHPIPE-RUN)
(SV::SVTV->INS-OF-BOOTHPIPE-RUN)
(SV::BOOTHPIPE-RUN-AUTOHYPS-FN)
(SV::BOOTHPIPE-RUN-ALIST-AUTOHYPS)
(SV::BOOTHPIPE-RUN-ENV-AUTOHYPS)
(SV::BOOTHPIPE-RUN-AUTOINS-FN)
(SV::BOOTHPIPE-RUN-AUTOINS-LOOKUP)
(SV::SVEX-ENV-LOOKUP-OF-BOOTHPIPE-RUN-AUTOINS)
(SV::SVEX-ENV-BOUNDP-OF-BOOTHPIPE-RUN-AUTOINS)
(SV::BOOTHPIPE-RUN-ALIST-AUTOINS)
(SV::BOOTHPIPE-RUN-ENV-AUTOINS)
(SV::SVEX-ENV-P-OF-BOOTHPIPE-RUN-ENV-AUTOINS
 (22 11 (:REWRITE DEFAULT-CDR))
 (22 11 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE-QUOTED-CONSTANT SV::SVAR-FIX-UNDER-SVAR-EQUIV))
 (11 11 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-P-FIX-UNDER-MAYBE-SVAR-P-EQUIV))
 (11 11 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-FIX-UNDER-MAYBE-SVAR-EQUIV))
 )
(SV::BOOTHPIPE-RUN-ENV-AUTOINS-IN-TERMS-OF-SVEX-ENV-EXTRACT
 (365 21 (:REWRITE SV::SVEX-ENV-EXTRACT-WHEN-ALIST-KEYS-EQUAL))
 (117 21 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (117 21 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (94 1 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (87 87 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (26 21 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (21 21 (:REWRITE-QUOTED-CONSTANT SV::SVAR-FIX-UNDER-SVAR-EQUIV))
 (21 21 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-P-FIX-UNDER-MAYBE-SVAR-P-EQUIV))
 (21 21 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-FIX-UNDER-MAYBE-SVAR-EQUIV))
 (11 11 (:REWRITE-QUOTED-CONSTANT SV::SVARLIST-FIX-UNDER-SVARLIST-EQUIV))
 (6 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (3 3 (:TYPE-PRESCRIPTION SV::SVEX-ENV-FIX$INLINE))
 (2 2 (:TYPE-PRESCRIPTION SV::SVEX-ENV-P))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 2))
 (2 2 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 )
(SV::BOOTHPIPE-RUN-ALIST-AUTOINS-IDEMPOTENT)
(SV::BOOTHPIPE-RUN-ALIST-AUTOINS-LOOKUP)
(SV::BOOTHPIPE-RUN-ALIST-AUTOHYPS-OF-AUTOINS)
(SV::BOOTHPIPE-RUN-ENV-AUTOHYPS-OF-AUTOINS)
(SV::BOOTHPIPE-DATA)
(SV::SVTV-DATA-OBJ-P-OF-BOOTHPIPE-DATA)
(SV::FLATTEN-VALIDP-OF-BOOTHPIPE-DATA)
(SV::BOOTHPIPE-DATA-CORRECT)
(SV::BOOTHPIPE-RUN-SPEC)
(SV::SVTV-SPEC-P-OF-BOOTHPIPE-RUN-SPEC)
(SV::BOOTHPIPE-RUN-SPEC-DEF)
(SV::BOOTHPIPE-RUN-SPEC-FSM-OVERRIDE-TEST-VARS)
(SV::BOOTHPIPE-RUN-SPEC-FSM-OVERRIDE-TEST-VARS-DEF)
(SV::BOOTHPIPE-RUN-TRIPLEMAPLIST)
(SV::SVTV-OVERRIDE-TRIPLEMAPLIST-P-OF-BOOTHPIPE-RUN-TRIPLEMAPLIST)
(SV::SYNTAX-CHECK-OF-BOOTHPIPE-RUN-TRIPLEMAPLIST)
(SV::BOOTHPIPE-RUN-OVERRIDEKEYS)
(SV::SVARLIST-P-OF-BOOTHPIPE-RUN-OVERRIDEKEYS)
(SV::BOOTHPIPE-RUN-INPUT-VARS)
(SV::SVARLIST-P-OF-BOOTHPIPE-RUN-INPUT-VARS)
(SV::BOOTHPIPE-DATA-FACTS)
(SV::BOOTHPIPE-RUN-IS-BOOTHPIPE-DATA-PIPELINE)
(SV::SVTV-RUN-OF-BOOTHPIPE-RUN-IS-EVAL-BOOTHPIPE-DATA-PIPELINE)
(SV::BOOTHPIPE-DATA-FACTS-FOR-SPEC)
(SV::SVTV-RUN-OF-BOOTHPIPE-RUN-IS-SVTV-SPEC-RUN-OF-BOOTHPIPE-RUN-SPEC)
(SV::BOOTHPIPE-RUN-SPEC-FSM-OVMONOTONIC)
(SV::BOOTHPIPE-RUN-SPEC-FACTS)
(SV::BOOTHPIPE-DATA-GENERALIZE-OVERRIDE-SYNTAX-CHECK)
(SV::TMP-OVERRIDE-TRANSPARENT-KEYS)
(SV::DEF-OVERRIDE-TRANSPARENT-OPEN-FSM)
(SV::TMP-DEF-OVERRIDE-TRANSPARENT-SMART-CHECK)
(SV::FSM-OVERRIDE-TRANSPARENT-P-OF-BOOTHPIPE-DATA)
(SV::BOOTHPIPE-RUN-REFINES-BOOTHPIPE-RUN)
(SV::BOOTHPIPE-PP-CORRECT-OVERRIDE-LEMMA)
(SV::BOOTHPIPE-PP-CORRECT
 (16 16 (:REWRITE SV::UNSIGNED-BYTE-P-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 )
(SV::FIND-FORM)
(SV::BOOTHPIPE-SUM-CORRECT-OVERRIDE-LEMMA)
(SV::BOOTHPIPE-SUM-CORRECT
 (112 112 (:REWRITE SV::UNSIGNED-BYTE-P-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 )
(SV::BOOTH-SUM-IMPL-REDEF
 (560 5 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (435 5 (:DEFINITION SIGNED-BYTE-P))
 (235 5 (:DEFINITION INTEGER-RANGE-P))
 (130 5 (:DEFINITION EXPT))
 (120 120 (:TYPE-PRESCRIPTION POSP-OF-POS-FIX))
 (120 60 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (110 5 (:REWRITE POS-FIX-WHEN-POSP))
 (90 5 (:REWRITE POSP-REDEFINITION))
 (79 50 (:REWRITE DEFAULT-+-2))
 (62 32 (:REWRITE DEFAULT-<-2))
 (60 60 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (60 60 (:TYPE-PRESCRIPTION SV::BOOTHPIPE-PP-SPEC))
 (59 50 (:REWRITE DEFAULT-+-1))
 (43 8 (:REWRITE ZP-OPEN))
 (42 32 (:REWRITE DEFAULT-<-1))
 (40 10 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (36 10 (:REWRITE ZP-WHEN-INTEGERP))
 (34 9 (:REWRITE FOLD-CONSTS-IN-+))
 (32 12 (:REWRITE DEFAULT-*-2))
 (30 10 (:REWRITE ZP-WHEN-GT-0))
 (25 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (25 15 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (25 5 (:REWRITE ZIP-OPEN))
 (20 10 (:DEFINITION FIX))
 (20 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-*-1))
 (12 12 (:DEFINITION NOT))
 (12 2 (:REWRITE DISTRIBUTIVITY))
 (10 10 (:REWRITE VL::POSP-WHEN-MEMBER-EQUAL-OF-POS-LISTP))
 (10 10 (:REWRITE SV::FIX-OF-NUMBER))
 (10 5 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (5 5 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 5 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 )
(SV::BOOTH-SUM-OF-PRODUCTS-CORRECT
 (40 10 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (38 9 (:REWRITE DEFAULT-+-2))
 (20 20 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (17 9 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(SV::BOOTHPIPE-PP-SPEC-BOUND
 (32 17 (:REWRITE DEFAULT-+-2))
 (25 17 (:REWRITE DEFAULT-+-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (9 1 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (8 8 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (7 7 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 1 (:DEFINITION SIGNED-BYTE-P))
 (5 5 (:REWRITE DEFAULT-*-1))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (1 1 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (1 1 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(SV::BOOTHPIPE-CORRECT-GEN
 (438 18 (:REWRITE SV::SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-RELEVANT-VARS-TEST-ONLY))
 (414 6 (:REWRITE SV::SVEX-ENV-REDUCE-WHEN-ALIST-KEYS-EQUAL))
 (194 2 (:REWRITE SV::SVEX-ENV-FIX-WHEN-SVEX-ENV-P))
 (194 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (188 2 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (150 12 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (114 10 (:DEFINITION SIGNED-BYTE-P))
 (104 10 (:DEFINITION INTEGER-RANGE-P))
 (56 56 (:TYPE-PRESCRIPTION SV::BOOTHPIPE-PP-SPEC))
 (52 52 (:REWRITE-QUOTED-CONSTANT SV::SVAR-FIX-UNDER-SVAR-EQUIV))
 (52 52 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-P-FIX-UNDER-MAYBE-SVAR-P-EQUIV))
 (52 52 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-FIX-UNDER-MAYBE-SVAR-EQUIV))
 (44 4 (:REWRITE TRUTH::UNSIGNED-BYTE-P-WHEN-TRUTH-IDX-P))
 (32 2 (:REWRITE TRUTH::TRUTH-IDX-P-WHEN-UNSIGNED-BYTE-P))
 (27 27 (:TYPE-PRESCRIPTION ASH))
 (27 6 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (22 18 (:REWRITE SV::SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-RELEVANT-VARS))
 (20 12 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV))
 (18 18 (:REWRITE-QUOTED-CONSTANT SV::SVAR-ALIST-FIX-UNDER-SVAR-ALIST-EQUIV))
 (18 18 (:REWRITE SV::SVTV-OVERRIDE-TRIPLEMAPLIST-ENVS-MATCH-SIMPLIFY))
 (18 4 (:REWRITE TRUTH::UNSIGNED-BYTE-P-WHEN-TRUTH4-P))
 (17 17 (:REWRITE SV::SVTV-RUN-NORMALIZE-IRRELEVANT-INPUTS))
 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (14 14 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (14 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (12 12 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 6 (:REWRITE DEFAULT-+-1))
 (12 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 1))
 (10 10 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (10 10 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (8 8 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (8 4 (:REWRITE SV::UNSIGNED-BYTE-P-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 (6 6 (:TYPE-PRESCRIPTION TRUTH::TRUTH-IDX-P))
 (6 6 (:TYPE-PRESCRIPTION SV::SVEX-ENV-FIX$INLINE))
 (6 6 (:REWRITE SV::SVEX-ENV-REDUCE-WHEN-NOT-CONSP))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:TYPE-PRESCRIPTION TRUTH::TRUTH4-P))
 (4 4 (:TYPE-PRESCRIPTION SV::SVEX-ENV-P))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-STRING/INT-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-PACKAGEMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-DECLS-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 2))
 (4 4 (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 2))
 (4 4 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-CLASSNAME/PARAMS-UNPARAM-MAP-P . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 2 (:REWRITE TRUTH::TRUTH4-P-WHEN-UNSIGNED-BYTE-P))
 (4 2 (:REWRITE SV::SIGNED-BYTE-P-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 (4 2 (:REWRITE SV::INTEGERP-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION SV::SVTV-OVERRIDE-TRIPLEMAPLIST-TEST-ONLY-P))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::SVARLIST-FIX-UNDER-SVARLIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::SVTV-OVERRIDE-TRIPLEMAPLIST-FIX-UNDER-SVTV-OVERRIDE-TRIPLEMAPLIST-EQUIV))
 )
(SV::BOOTHPIPE-CORRECT
 (16 4 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (16 4 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (12 4 (:REWRITE TRUTH::UNSIGNED-BYTE-P-WHEN-TRUTH4-P))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (8 2 (:DEFINITION SIGNED-BYTE-P))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::SVAR-FIX-UNDER-SVAR-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-P-FIX-UNDER-MAYBE-SVAR-P-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-FIX-UNDER-MAYBE-SVAR-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 2 (:DEFINITION INTEGER-RANGE-P))
 (4 4 (:TYPE-PRESCRIPTION TRUTH::TRUTH4-P))
 (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (4 4 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (4 4 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (4 4 (:REWRITE SV::MAYBE-4VEC-P-WHEN-MEMBER-EQUAL-OF-MAYBE-4VECLIST-P))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE TRUTH::TRUTH4-P-WHEN-UNSIGNED-BYTE-P))
 (4 2 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (2 2 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::SVAR-ALIST-FIX-UNDER-SVAR-ALIST-EQUIV))
 (1 1 (:REWRITE SV::SVTV-RUN-NORMALIZE-IRRELEVANT-INPUTS))
 )
(SV::BOOTHPIPE-SPEC)
(SV::SVTV-SPEC-P-OF-BOOTHPIPE-SPEC)
(SV::BOOTHPIPE-SPEC-DEF)
(SV::BOOTHPIPE-SPEC-FSM-OVERRIDE-TEST-VARS)
(SV::BOOTHPIPE-SPEC-FSM-OVERRIDE-TEST-VARS-DEF)
(SV::SYNTAX-CHECK-OF-BOOTHPIPE-RUN-TRIPLEMAPLIST)
(SV::BOOTHPIPE-DATA-FACTS)
(SV::BOOTHPIPE-RUN-IS-BOOTHPIPE-DATA-PIPELINE)
(SV::SVTV-RUN-OF-BOOTHPIPE-RUN-IS-EVAL-BOOTHPIPE-DATA-PIPELINE)
(SV::BOOTHPIPE-DATA-FACTS-FOR-SPEC)
(SV::SVTV-RUN-OF-BOOTHPIPE-RUN-IS-SVTV-SPEC-RUN-OF-BOOTHPIPE-SPEC)
(SV::BOOTHPIPE-SPEC-FSM-OVMONOTONIC)
(SV::BOOTHPIPE-SPEC-FACTS)
(SV::BOOTHPIPE-DATA-GENERALIZE-OVERRIDE-SYNTAX-CHECK)
(SV::BOOTHPIPE-SPEC-OVERRIDE-SYNTAX-CHECK)
(SV::TMP-OVERRIDE-TRANSPARENT-KEYS)
(SV::DEF-OVERRIDE-TRANSPARENT-OPEN-FSM)
(SV::TMP-DEF-OVERRIDE-TRANSPARENT-SMART-CHECK)
(SV::FSM-OVERRIDE-TRANSPARENT-P-OF-BOOTHPIPE-DATA)
(SV::BOOTHPIPE-SPEC-FSM-OVERRIDE-TRANSPARENT-P)
(SV::BOOTHPIPE-SPEC-REFINES-BOOTHPIPE-RUN)
(SV::BOOTHPIPE-SPEC-REFINES-BOOTHPIPE-SPEC)
(SV::NO-DUPLICATE-STATE-KEYS-OF-BOOTHPIPE-SPEC)
(SV::STATE-KEYS-INTERSECT-NONDELAY-OF-BOOTHPIPE-SPEC)
(SV::SVARLIST-DELAY-P-STATE-KEYS-OF-BOOTHPIPE-SPEC)
(SV::INITST-KEYS-OF-BOOTHPIPE-SPEC)
(SV::PROBE-KEYS-OF-BOOTHPIPE-SPEC)
(SV::CYCLE-OUTPUTS-CAPTURED-OF-BOOTHPIPE-SPEC)
(SV::NEXTSTATE-KEYS-NON-OVERRIDE-OF-BOOTHPIPE-SPEC)
(SV::FSM-OVERRIDEKEY-TRANSPARENT-P-OF-BOOTHPIPE-SPEC-CYCLE)
(SV::FSM-OVCONGRUENT-OF-BOOTHPIPE-SPEC)
(SV::FSM-OVCONGRUENT-OF-BOOTHPIPE-SPEC-CYCLE)
(SV::SVTV-SPEC-FSM-SYNTAX-CHECK-OF-BOOTHPIPE-SPEC)
(SV::BOOTHPIPE-SPEC-INITST-CHARACTERIZE)
(SV::SVARLIST-NONOVERRIDE-TEST-OF-BOOTHPIPE-SPEC-CYCLEPHASELIST-KEYS)
(SV::BOOTHPIPE-CORRECT-GEN-SPEC-OVERRIDE-LEMMA
 (16 4 (:REWRITE SV::OUR-LOGEXT-IDENTITY))
 (16 4 (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P))
 (12 4 (:REWRITE TRUTH::UNSIGNED-BYTE-P-WHEN-TRUTH4-P))
 (8 8 (:REWRITE SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P))
 (8 2 (:DEFINITION SIGNED-BYTE-P))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::SVAR-FIX-UNDER-SVAR-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-P-FIX-UNDER-MAYBE-SVAR-P-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVAR-FIX-UNDER-MAYBE-SVAR-EQUIV))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 2 (:DEFINITION INTEGER-RANGE-P))
 (4 4 (:TYPE-PRESCRIPTION TRUTH::TRUTH4-P))
 (4 4 (:TYPE-PRESCRIPTION SV::MAYBE-4VEC-P))
 (4 4 (:TYPE-PRESCRIPTION LOGEXT-TYPE))
 (4 4 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 (4 4 (:REWRITE SV::MAYBE-4VEC-P-WHEN-MEMBER-EQUAL-OF-MAYBE-4VECLIST-P))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE TRUTH::TRUTH4-P-WHEN-UNSIGNED-BYTE-P))
 (4 2 (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P))
 (4 2 (:REWRITE DEFAULT-*-2))
 (4 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (2 2 (:REWRITE SV::SVTV-RUN-NORMALIZE-IRRELEVANT-INPUTS))
 (2 2 (:REWRITE SV::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT SV::SVAR-ALIST-FIX-UNDER-SVAR-ALIST-EQUIV))
 )
(SV::BOOTHPIPE-CORRECT-GEN-SPEC
 (23 23 (:REWRITE SV::UNSIGNED-BYTE-P-BY-SVEX-ENV-VAL-WIDTHS-FROM-TYPE-ALIST))
 )
