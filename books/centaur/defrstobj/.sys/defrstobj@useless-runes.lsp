(RSTOBJ::EAT-TYPED-RECORD)
(RSTOBJ::EAT-TYPED-RECORDS)
(RSTOBJ::TR-ALIST)
(RSTOBJ::FIX-ALIST)
(RSTOBJ::MAKE-$C-FIELDS)
(RSTOBJ::DESTRUCTURE-DEFSTOBJ-FIELD-TEMPLATE)
(RSTOBJ::MAKE-FTA)
(RSTOBJ::MAKE-FTAS)
(RSTOBJ::ADDITIONAL-EXEC-DEFS)
(RSTOBJ::CREATOR-LOGIC-UPDATES)
(RSTOBJ::SCALAR-FIXING-FUNCTION-THMS)
(RSTOBJ::SCALAR-FIXING-FUNCTION-THM-NAMES)
(RSTOBJ::COLLECT-TYPED-REC-THEOREMS)
(RSTOBJ::LOGIC-FIELD-FUNCTIONS-ONE)
(RSTOBJ::LOGIC-FIELD-FUNCTIONS)
(RSTOBJ::MAKE-FIELDMAP-ENTRIES)
(RSTOBJ::MAKE-TR-GET-ENTRIES)
(RSTOBJ::MAKE-TR-SET-ENTRIES)
(RSTOBJ::MAKE-TR-FIX-ENTRIES)
(RSTOBJ::MAKE-TR-DEFAULT-ENTRIES)
(RSTOBJ::MAKE-TR-ELEM-P-ENTRIES)
(RSTOBJ::MAKE-SCALAR-FIX-ENTRIES)
(RSTOBJ::MAKE-SCALAR-ELEM-P-ENTRIES)
(RSTOBJ::MAKE-FIELD-CORR-OF-TR-KEY-CONCLS)
(RSTOBJ::ARRAY-TYPES-PRESERVED-THMS)
(RSTOBJ::ABSSTOBJ-EXPORTS-ONE)
(RSTOBJ::ABSSTOBJ-EXPORTS)
(RSTOBJ::DESTRUCTURE-DEFSTOBJ-TEMPLATE)
(RSTOBJ::MAKE-VAL-FIXING-FN)
(RSTOBJ::TOP-LEVEL-GETTER-FNS)
(RSTOBJ::TOP-LEVEL-SETTER-FNS)
(RSTOBJ::GUARDS-FOR-TOP-LEVEL-ACC/UPD)
(RSTOBJ::MBE-ACCESSOR/UPDATER-FUNCTIONS-AUX)
(RSTOBJ::MBE-ACCESSOR/UPDATER-FUNCTIONS)
(RSTOBJ::MAKE-ARRAY-FIELDS-KWD-LIST)
(RSTOBJ::DEFRSTOBJ-FN)
(RSTOBJ::UBP-LISTP)
(RSTOBJ::UBP-FIX)
(RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P)
(RSTOBJ::ELEM-P-OF-DEFAULT-FOR-UBP8-TR-P)
(RSTOBJ::ELEM-P-OF-ELEM-FIX-FOR-UBP8-TR-P
 (48 48 (:TYPE-PRESCRIPTION RSTOBJ::UBP-FIX))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 )
(RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-UBP8-TR-P
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(RSTOBJ::ELEM-LIST-P-OF-CONS-FOR-UBP8-TR-P
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 )
(RSTOBJ::UBP8-TR-P1)
(RSTOBJ::UBP8-TR-P)
(RSTOBJ::UBP8-TO-TR
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TO-TR))
 )
(RSTOBJ::UBP8-TR-BAD-PART)
(RSTOBJ::UBP8-TR-GET1)
(RSTOBJ::UBP8-TR-SET1)
(RSTOBJ::UBP8-TR-GET
 (22 22 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TO-TR))
 )
(RSTOBJ::UBP8-TR-SET)
(RSTOBJ::UBP8-TR-BADGUY
 (4 4 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TO-TR))
 )
(RSTOBJ::UBP8-ARRAY-TO-TR)
(RSTOBJ::UBP8-TR-TO-ARRAY
 (4 1 (:DEFINITION RSTOBJ::UBP8-TR-P))
 (3 1 (:DEFINITION RSTOBJ::UBP8-TR-GET1))
 (2 1 (:DEFINITION RSTOBJ::UBP8-TR-P1))
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 )
(RSTOBJ::UBP8-TR-DELETE-INDICES)
(RSTOBJ::UBP8-ARRAY-REC-PAIR-P)
(RSTOBJ::ELEM-P-OF-UBP8-TR-GET
 (9 9 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TO-TR))
 )
(RSTOBJ::UBP8-TR-GET-OF-UBP8-TR-SET-SAME
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TO-TR))
 )
(RSTOBJ::UBP8-TR-GET-OF-UBP8-TR-SET-DIFF)
(RSTOBJ::UBP8-TR-SET-OF-UBP8-TR-GET-SAME)
(RSTOBJ::UBP8-TR-SET-OF-UBP8-TR-SET-DIFF)
(RSTOBJ::UBP8-TR-SET-OF-UBP8-TR-SET-SAME)
(RSTOBJ::UBP8-TR-GET-OF-UBP8-TR-SET-STRONG)
(RSTOBJ::UBP8-TR-GET-OF-NIL)
(RSTOBJ::UBP8-TR-BAD-PART-OF-UBP8-TR-SET
 (12 6 (:DEFINITION RSTOBJ::UBP8-TR-P1))
 (6 6 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 )
(RSTOBJ::UBP8-TR-BADGUY-FINDS-COUNTEREXAMPLE)
(RSTOBJ::UBP8-TR-BADGUY-UNLESS-EQUAL)
(RSTOBJ::EQUAL-OF-UBP8-TR-SET)
(RSTOBJ::UBP8-ELEM-P-OF-NTH)
(RSTOBJ::UBP8-TR-GET-OF-UBP8-ARRAY-TO-TR
 (262 56 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P))
 (100 53 (:REWRITE RSTOBJ::UBP8-ELEM-P-OF-NTH))
 (47 47 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-UBP8-TR-P))
 (3 3 (:REWRITE RSTOBJ::ELEM-P-OF-ELEM-FIX-FOR-UBP8-TR-P))
 )
(RSTOBJ::LEN-OF-UBP8-TR-TO-ARRAY
 (28 14 (:DEFINITION RSTOBJ::UBP8-TR-P1))
 (14 14 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 )
(RSTOBJ::ELEM-LIST-P-OF-UBP8-TR-TO-ARRAY)
(RSTOBJ::UBP8-TR-TO-ARRAY-IDEMPOTENT)
(RSTOBJ::UBP8-TR-TO-ARRAY-OF-UBP8-TR-SET)
(RSTOBJ::UBP8-TR-TO-ARRAY-OF-UBP8-ARRAY-TO-TR
 (19 1 (:DEFINITION RSTOBJ::UBP8-TR-TO-ARRAY))
 (17 1 (:REWRITE RSTOBJ::UBP8-TR-GET-OF-UBP8-ARRAY-TO-TR))
 (17 1 (:DEFINITION RSTOBJ::UBP8-ARRAY-TO-TR))
 (15 1 (:DEFINITION RSTOBJ::UBP8-TR-SET))
 (12 2 (:DEFINITION RSTOBJ::UBP8-TO-TR))
 (10 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P))
 (10 1 (:DEFINITION RSTOBJ::UBP8-TR-GET))
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TR-P))
 (8 2 (:DEFINITION RSTOBJ::UBP8-TR-P))
 (6 6 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (4 2 (:REWRITE RSTOBJ::UBP8-ELEM-P-OF-NTH))
 (4 2 (:DEFINITION RSTOBJ::UBP8-TR-P1))
 (3 1 (:DEFINITION RSTOBJ::UBP8-TR-SET1))
 (3 1 (:DEFINITION RSTOBJ::UBP8-TR-GET1))
 (2 2 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-UBP8-TR-P))
 (2 2 (:DEFINITION ZP))
 )
(RSTOBJ::UBP8-TR-DELETE-INDICES-OF-NIL
 (129 47 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P))
 (3 3 (:REWRITE RSTOBJ::ELEM-P-OF-ELEM-FIX-FOR-UBP8-TR-P))
 )
(RSTOBJ::UBP8-TR-DELETE-INDICES-IDEMPOTENT)
(RSTOBJ::UBP8-TR-DELETE-INDICES-OF-UBP8-TR-SET)
(RSTOBJ::UBP8-TR-DELETE-INDICES-OF-UBP8-ARRAY-TO-TR)
(RSTOBJ::UBP8-ARRAY-TO-TR-INVERSE)
(RSTOBJ::EQUAL-OF-UBP8-ARRAY-TO-TR
 (30 2 (:DEFINITION RSTOBJ::UBP8-TR-DELETE-INDICES))
 (26 2 (:DEFINITION RSTOBJ::UBP8-TR-SET))
 (12 2 (:DEFINITION RSTOBJ::UBP8-TO-TR))
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::UBP8-TR-P))
 (8 2 (:DEFINITION RSTOBJ::UBP8-TR-P))
 (6 6 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (6 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P))
 (6 2 (:DEFINITION RSTOBJ::UBP8-TR-SET1))
 (4 2 (:DEFINITION RSTOBJ::UBP8-TR-P1))
 (2 2 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-UBP8-TR-P))
 (2 2 (:DEFINITION ZP))
 (2 2 (:DEFINITION LEN))
 )
(RSTOBJ::NONNEG-FIX)
(RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P)
(RSTOBJ::ELEM-P-OF-DEFAULT-FOR-NONNEG-TR-P)
(RSTOBJ::ELEM-P-OF-ELEM-FIX-FOR-NONNEG-TR-P)
(RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P
 (3 1 (:REWRITE NATP-WHEN-GTE-0))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE NATP-WHEN-INTEGERP))
 )
(RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-NONNEG-TR-P
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(RSTOBJ::ELEM-LIST-P-OF-CONS-FOR-NONNEG-TR-P
 (15 5 (:REWRITE NATP-WHEN-GTE-0))
 (5 5 (:REWRITE NATP-WHEN-INTEGERP))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 )
(RSTOBJ::NONNEG-TR-P1)
(RSTOBJ::NONNEG-TR-P)
(RSTOBJ::NONNEG-TO-TR
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TO-TR))
 )
(RSTOBJ::NONNEG-TR-BAD-PART)
(RSTOBJ::NONNEG-TR-GET1)
(RSTOBJ::NONNEG-TR-SET1)
(RSTOBJ::NONNEG-TR-GET
 (22 22 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TO-TR))
 )
(RSTOBJ::NONNEG-TR-SET)
(RSTOBJ::NONNEG-TR-BADGUY
 (4 4 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TO-TR))
 )
(RSTOBJ::NONNEG-ARRAY-TO-TR)
(RSTOBJ::NONNEG-TR-TO-ARRAY
 (4 1 (:DEFINITION RSTOBJ::NONNEG-TR-P))
 (3 1 (:DEFINITION RSTOBJ::NONNEG-TR-GET1))
 (2 1 (:DEFINITION RSTOBJ::NONNEG-TR-P1))
 )
(RSTOBJ::NONNEG-TR-DELETE-INDICES)
(RSTOBJ::NONNEG-ARRAY-REC-PAIR-P)
(RSTOBJ::ELEM-P-OF-NONNEG-TR-GET
 (9 9 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TO-TR))
 )
(RSTOBJ::NONNEG-TR-GET-OF-NONNEG-TR-SET-SAME
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TO-TR))
 )
(RSTOBJ::NONNEG-TR-GET-OF-NONNEG-TR-SET-DIFF)
(RSTOBJ::NONNEG-TR-SET-OF-NONNEG-TR-GET-SAME)
(RSTOBJ::NONNEG-TR-SET-OF-NONNEG-TR-SET-DIFF)
(RSTOBJ::NONNEG-TR-SET-OF-NONNEG-TR-SET-SAME)
(RSTOBJ::NONNEG-TR-GET-OF-NONNEG-TR-SET-STRONG)
(RSTOBJ::NONNEG-TR-GET-OF-NIL)
(RSTOBJ::NONNEG-TR-BAD-PART-OF-NONNEG-TR-SET
 (12 6 (:DEFINITION RSTOBJ::NONNEG-TR-P1))
 (6 6 (:DEFINITION NATP))
 )
(RSTOBJ::NONNEG-TR-BADGUY-FINDS-COUNTEREXAMPLE)
(RSTOBJ::NONNEG-TR-BADGUY-UNLESS-EQUAL)
(RSTOBJ::EQUAL-OF-NONNEG-TR-SET)
(RSTOBJ::NONNEG-ELEM-P-OF-NTH)
(RSTOBJ::NONNEG-TR-GET-OF-NONNEG-ARRAY-TO-TR
 (262 56 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (100 53 (:REWRITE RSTOBJ::NONNEG-ELEM-P-OF-NTH))
 (53 53 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (47 47 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-NONNEG-TR-P))
 (3 3 (:REWRITE RSTOBJ::ELEM-P-OF-ELEM-FIX-FOR-NONNEG-TR-P))
 )
(RSTOBJ::LEN-OF-NONNEG-TR-TO-ARRAY
 (28 14 (:DEFINITION RSTOBJ::NONNEG-TR-P1))
 (14 14 (:DEFINITION NATP))
 )
(RSTOBJ::ELEM-LIST-P-OF-NONNEG-TR-TO-ARRAY)
(RSTOBJ::NONNEG-TR-TO-ARRAY-IDEMPOTENT)
(RSTOBJ::NONNEG-TR-TO-ARRAY-OF-NONNEG-TR-SET)
(RSTOBJ::NONNEG-TR-TO-ARRAY-OF-NONNEG-ARRAY-TO-TR
 (19 1 (:DEFINITION RSTOBJ::NONNEG-TR-TO-ARRAY))
 (17 1 (:REWRITE RSTOBJ::NONNEG-TR-GET-OF-NONNEG-ARRAY-TO-TR))
 (17 1 (:DEFINITION RSTOBJ::NONNEG-ARRAY-TO-TR))
 (15 1 (:DEFINITION RSTOBJ::NONNEG-TR-SET))
 (12 2 (:DEFINITION RSTOBJ::NONNEG-TO-TR))
 (10 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (10 1 (:DEFINITION RSTOBJ::NONNEG-TR-GET))
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TR-P))
 (8 2 (:DEFINITION RSTOBJ::NONNEG-TR-P))
 (4 2 (:REWRITE RSTOBJ::NONNEG-ELEM-P-OF-NTH))
 (4 2 (:DEFINITION RSTOBJ::NONNEG-TR-P1))
 (3 1 (:DEFINITION RSTOBJ::NONNEG-TR-SET1))
 (3 1 (:DEFINITION RSTOBJ::NONNEG-TR-GET1))
 (2 2 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-NONNEG-TR-P))
 (2 2 (:DEFINITION ZP))
 )
(RSTOBJ::NONNEG-TR-DELETE-INDICES-OF-NIL)
(RSTOBJ::NONNEG-TR-DELETE-INDICES-IDEMPOTENT)
(RSTOBJ::NONNEG-TR-DELETE-INDICES-OF-NONNEG-TR-SET)
(RSTOBJ::NONNEG-TR-DELETE-INDICES-OF-NONNEG-ARRAY-TO-TR)
(RSTOBJ::NONNEG-ARRAY-TO-TR-INVERSE)
(RSTOBJ::EQUAL-OF-NONNEG-ARRAY-TO-TR
 (30 2 (:DEFINITION RSTOBJ::NONNEG-TR-DELETE-INDICES))
 (26 2 (:DEFINITION RSTOBJ::NONNEG-TR-SET))
 (12 2 (:DEFINITION RSTOBJ::NONNEG-TO-TR))
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::NONNEG-TR-P))
 (8 2 (:DEFINITION RSTOBJ::NONNEG-TR-P))
 (6 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (6 2 (:DEFINITION RSTOBJ::NONNEG-TR-SET1))
 (4 4 (:DEFINITION NATP))
 (4 2 (:DEFINITION RSTOBJ::NONNEG-TR-P1))
 (2 2 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (2 2 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-NONNEG-TR-P))
 (2 2 (:DEFINITION ZP))
 (2 2 (:DEFINITION LEN))
 )
(RSTOBJ::PLUS-COLLECT-CONSTS)
(RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORINTFLD
 (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 )
(RSTOBJ::RSTOBJ-FIX-ELEM-P-FORINTFLD)
(RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORNATFLD
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(RSTOBJ::RSTOBJ-FIX-ELEM-P-FORNATFLD)
(RSTOBJ::EMPTY-U8ARR$C)
(RSTOBJ::STP$A)
(RSTOBJ::CREATE-ST$A)
(RSTOBJ::NATARR-LENGTH$A)
(RSTOBJ::GET-NATARR$A)
(RSTOBJ::SET-NATARR$A)
(RSTOBJ::U8ARR-LENGTH$A)
(RSTOBJ::GET-U8ARR$A)
(RSTOBJ::SET-U8ARR$A)
(RSTOBJ::GROW-U8ARR$A)
(RSTOBJ::EMPTY-U8ARR$A)
(RSTOBJ::GET-INTFLD$A)
(RSTOBJ::SET-INTFLD$A)
(RSTOBJ::GET-NATFLD$A)
(RSTOBJ::SET-NATFLD$A)
(RSTOBJ::RSTOBJ-TMP-FIELD-MAP)
(RSTOBJ::RSTOBJ-TMP-TR-GET)
(RSTOBJ::RSTOBJ-TMP-TR-SET)
(RSTOBJ::RSTOBJ-TMP-TR-FIX)
(RSTOBJ::RSTOBJ-TMP-TR-DEFAULT)
(RSTOBJ::RSTOBJ-TMP-TR-ELEM-P)
(RSTOBJ::RSTOBJ-TMP-SCALAR-FIX)
(RSTOBJ::RSTOBJ-TMP-SCALAR-ELEM-P)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-NECC
 (42 42 (:DEFINITION MV-NTH))
 )
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY
 (18 18 (:REWRITE NTH-WHEN-ATOM))
 (15 5 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (11 11 (:REWRITE LEN-WHEN-ATOM))
 (10 10 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 )
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE
 (14 14 (:REWRITE NTH-WHEN-ATOM))
 (6 6 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (6 6 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (6 6 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-UPDATE-SCALAR)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-UPDATE-ARRAY)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-GROW-ARRAY)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-EMPTY-ARRAY)
(RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-CREATE
 (40 10 (:REWRITE LEN-WHEN-ATOM))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::RSTOBJ-TMP-CORR)
(RSTOBJ::FIELD-LOOKUP-IN-RSTOBJ-TMP-FIELD-MAP)
(RSTOBJ::INDEX-LOOKUP-IN-RSTOBJ-TMP-FIELD-MAP)
(RSTOBJ::NATARR$CP-OF-REPEAT)
(RSTOBJ::NATARR$CP-OF-UPDATE-NTH
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (7 7 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::NATARR$CP-OF-RESIZE-LIST
 (3 3 (:REWRITE RSTOBJ::PLUS-COLLECT-CONSTS))
 )
(RSTOBJ::U8ARR$CP-OF-REPEAT)
(RSTOBJ::U8ARR$CP-OF-UPDATE-NTH
 (8 8 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (7 7 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::U8ARR$CP-OF-RESIZE-LIST
 (3 3 (:REWRITE RSTOBJ::PLUS-COLLECT-CONSTS))
 )
(RSTOBJ::CREATE-ST{CORRESPONDENCE}
 (8 8 (:REWRITE NTH-WHEN-ATOM))
 (4 1 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::CREATE-ST{PRESERVED})
(RSTOBJ::NATARR-LENGTH{CORRESPONDENCE})
(RSTOBJ::GET-NATARR{CORRESPONDENCE}
 (16 16 (:REWRITE NTH-WHEN-ATOM))
 (5 5 (:REWRITE LEN-WHEN-ATOM))
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (2 1 (:DEFINITION RSTOBJ::U8ARR$CP))
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (1 1 (:DEFINITION RSTOBJ::NATARR$CP))
 )
(RSTOBJ::GET-NATARR{GUARD-THM})
(RSTOBJ::SET-NATARR{CORRESPONDENCE}
 (36 36 (:REWRITE NTH-WHEN-ATOM))
 (15 15 (:REWRITE LEN-WHEN-ATOM))
 (13 8 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (13 8 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (10 10 (:REWRITE RSTOBJ::FIELD-LOOKUP-IN-RSTOBJ-TMP-FIELD-MAP))
 (3 3 (:DEFINITION RSTOBJ::NATARR$CP))
 )
(RSTOBJ::SET-NATARR{GUARD-THM})
(RSTOBJ::SET-NATARR{PRESERVED})
(RSTOBJ::U8ARR-LENGTH{CORRESPONDENCE}
 (2 2 (:REWRITE NTH-WHEN-ATOM))
 (2 2 (:REWRITE LEN-WHEN-ATOM))
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::GET-U8ARR{CORRESPONDENCE}
 (6 6 (:REWRITE NTH-WHEN-ATOM))
 (4 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (2 2 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::GET-U8ARR{GUARD-THM}
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (1 1 (:REWRITE NTH-WHEN-ATOM))
 (1 1 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::SET-U8ARR{CORRESPONDENCE}
 (30 30 (:REWRITE NTH-WHEN-ATOM))
 (13 13 (:REWRITE LEN-WHEN-ATOM))
 (6 3 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (4 2 (:DEFINITION RSTOBJ::U8ARR$CP))
 )
(RSTOBJ::SET-U8ARR{GUARD-THM}
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (1 1 (:REWRITE NTH-WHEN-ATOM))
 (1 1 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::SET-U8ARR{PRESERVED})
(RSTOBJ::GROW-U8ARR{CORRESPONDENCE}
 (30 30 (:REWRITE NTH-WHEN-ATOM))
 (12 12 (:REWRITE LEN-WHEN-ATOM))
 (5 5 (:REWRITE RESIZE-LIST-WHEN-ZP))
 (4 2 (:DEFINITION RSTOBJ::U8ARR$CP))
 (2 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::GROW-U8ARR{PRESERVED})
(RSTOBJ::EMPTY-U8ARR{CORRESPONDENCE}
 (21 21 (:REWRITE NTH-WHEN-ATOM))
 (7 7 (:REWRITE LEN-WHEN-ATOM))
 (4 2 (:DEFINITION RSTOBJ::U8ARR$CP))
 (2 2 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 )
(RSTOBJ::EMPTY-U8ARR{PRESERVED})
(RSTOBJ::GET-INTFLD{CORRESPONDENCE}
 (13 13 (:REWRITE NTH-WHEN-ATOM))
 (2 2 (:REWRITE LEN-WHEN-ATOM))
 (2 1 (:DEFINITION RSTOBJ::U8ARR$CP))
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (1 1 (:DEFINITION RSTOBJ::NATARR$CP))
 )
(RSTOBJ::SET-INTFLD{CORRESPONDENCE}
 (20 20 (:REWRITE NTH-WHEN-ATOM))
 (7 7 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::SET-INTFLD{PRESERVED})
(RSTOBJ::GET-NATFLD{CORRESPONDENCE}
 (15 3 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (13 13 (:REWRITE NTH-WHEN-ATOM))
 (6 6 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (6 3 (:REWRITE RSTOBJ::NONNEG-ELEM-P-OF-NTH))
 (3 3 (:REWRITE RSTOBJ::ELEM-LIST-P-WHEN-ATOM-FOR-NONNEG-TR-P))
 (2 2 (:REWRITE LEN-WHEN-ATOM))
 (2 1 (:DEFINITION RSTOBJ::U8ARR$CP))
 (1 1 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (1 1 (:DEFINITION RSTOBJ::NATARR$CP))
 )
(RSTOBJ::SET-NATFLD{CORRESPONDENCE}
 (20 20 (:REWRITE NTH-WHEN-ATOM))
 (7 7 (:REWRITE LEN-WHEN-ATOM))
 )
(RSTOBJ::SET-NATFLD{PRESERVED})
(RSTOBJ::ST-VALFIX)
(RSTOBJ::READ-ST)
(RSTOBJ::WRITE-ST)
(RSTOBJ::STP-OF-WRITE-ST)
(RSTOBJ::READ-ST-WRITE-ST-INTRA-FIELD
 (27 9 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (22 22 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (22 22 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (18 18 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (9 9 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORNATFLD))
 (9 3 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-UBP8-TR-P))
 (8 8 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 (6 6 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-UBP8-TR-P))
 (6 6 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORINTFLD))
 )
(RSTOBJ::READ-ST-WRITE-ST-INTER-FIELD
 (60 60 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (60 60 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (30 10 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (20 20 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (20 20 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 (10 10 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORNATFLD))
 (10 10 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORINTFLD))
 )
(RSTOBJ::WRITE-ST-WRITE-ST-SHADOW-WRITES
 (10 10 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (10 10 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::WRITE-ST-WRITE-ST-INTRA-FIELD-ARRANGE-WRITES
 (8 8 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (8 8 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::WRITE-ST-WRITE-ST-INTER-FIELD-ARRANGE-WRITES
 (48 48 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (48 48 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::@NATARR$INLINE
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::READ-ST-NATARR-WELL-FORMED-VALUE
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::!NATARR$INLINE
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::@U8ARR$INLINE
 (3 3 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (3 3 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (3 1 (:REWRITE NFIX-WHEN-NATP))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 )
(RSTOBJ::READ-ST-U8ARR-WELL-FORMED-VALUE
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-TR-KEY-ELABORATE))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 )
(RSTOBJ::!U8ARR$INLINE
 (3 3 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (3 3 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (3 1 (:REWRITE NFIX-WHEN-NATP))
 )
(RSTOBJ::@INTFLD$INLINE
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORINTFLD))
 )
(RSTOBJ::READ-ST-INTFLD-WELL-FORMED-VALUE
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (1 1 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORINTFLD))
 )
(RSTOBJ::!INTFLD$INLINE)
(RSTOBJ::@NATFLD$INLINE
 (6 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (4 4 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORNATFLD))
 )
(RSTOBJ::READ-ST-NATFLD-WELL-FORMED-VALUE
 (6 2 (:REWRITE RSTOBJ::ELEM-FIX-IDEMPOTENT-FOR-NONNEG-TR-P))
 (4 4 (:TYPE-PRESCRIPTION RSTOBJ::BOOLEANP-OF-ELEM-P-FOR-NONNEG-TR-P))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SIZE-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-TMP-FIELD-CORR-OF-SCALAR-KEY))
 (2 2 (:REWRITE RSTOBJ::RSTOBJ-FIX-IDEMPOTENT-FORNATFLD))
 )
(RSTOBJ::!NATFLD$INLINE)
