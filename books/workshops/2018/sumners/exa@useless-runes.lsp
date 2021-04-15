(COMPUTE-VL-CONF)
(COMPUTE-VL-CONF-RETURNS-VL-LOADCONFIG)
(COMPUTE-VL-CONF-INST
     (339 1 (:DEFINITION BINARY-APPEND))
     (190 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (81 1 (:REWRITE DEFAULT-CDR))
     (81 1 (:REWRITE DEFAULT-CAR))
     (45 4 (:REWRITE STR::CONSP-OF-EXPLODE))
     (15 5
         (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P
                   . 1))
     (15 5
         (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P
                   . 1))
     (10 10
         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (10 10
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
     (10 10
         (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
     (5 5
        (:REWRITE VL::VL-LEXSCOPE-P-OF-VL-EMPTY-LEXSCOPE))
     (5 5
        (:REWRITE VL::VL-ELABSCOPES-P-OF-VL-ELABSCOPES-INIT))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-INSTKEYMAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-UNPARAM-DONELIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-TYPE-ERROR-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SVEX-KEYVALLIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDARG-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-LEXSCOPE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-INCLUDESKIPS-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFPORT-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABTRAVERSAL-STACK-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPES-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ELABSCOPE-ALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXLIST-CACHE-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRXCACHE-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRLIST-CACHE-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DIRCACHE-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DATATYPE-MAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BLAMEALIST-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDELIM-INSTTABLE-P
                  . 1))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P
                  . 2))
     (5 5
        (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-BINDDELTA-P
                  . 1))
     (5 5
        (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P
                  . 2))
     (5 5
        (:REWRITE SV::CONSP-WHEN-MEMBER-EQUAL-OF-SVAR-SIZE-ALIST-P
                  . 1))
     (5 5 (:REWRITE CONSP-BY-LEN))
     (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE VL::VL-MAYBE-STRING-LIST-P-WHEN-SUBSETP-EQUAL))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (1 1
        (:REWRITE VL::VL-MAYBE-STRING-LIST-P-WHEN-NOT-CONSP))
     (1 1 (:REWRITE VAR-LST-COMPLETE-FOR-VAR))
     (1 1 (:REWRITE SUBSETP-MEMBER . 4))
     (1 1 (:REWRITE SUBSETP-MEMBER . 3))
     (1 1 (:REWRITE SUBSETP-MEMBER . 2))
     (1 1 (:REWRITE SUBSETP-MEMBER . 1))
     (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
     (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
     (1 1
        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN)))
(VL-LOADCONFIG-P-OF-COMPUTE-VL-CONF-INST)
(LOAD-PROCESSOR-VL-DESIGN (664 332
                               (:TYPE-PRESCRIPTION LRAT::NTH-N59-LISTP))
                          (664 332
                               (:TYPE-PRESCRIPTION LRAT::NTH-I60-LISTP))
                          (332 332
                               (:TYPE-PRESCRIPTION LRAT::N59-LISTP))
                          (332 332
                               (:TYPE-PRESCRIPTION LRAT::I60-LISTP)))
(VL-DESIGN-P-OF-LOAD-PROCESSOR-VL-DESIGN.DESIGN)
(TRANS-VL-DESIGN-TO-SV-DESIGN)
(DESIGN-P-OF-TRANS-VL-DESIGN-TO-SV-DESIGN)
(VL->SV-DESIGN-FN (664 332
                       (:TYPE-PRESCRIPTION LRAT::NTH-N59-LISTP))
                  (664 332
                       (:TYPE-PRESCRIPTION LRAT::NTH-I60-LISTP))
                  (332 332
                       (:TYPE-PRESCRIPTION LRAT::N59-LISTP))
                  (332 332
                       (:TYPE-PRESCRIPTION LRAT::I60-LISTP)))
(DESIGN-P-OF-VL->SV-DESIGN.RSLT)
