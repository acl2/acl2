; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(ld "symbols-defpkg.lsp")

;Is there a better way to do this? -ews

(PROGN
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*0 NIL
           ''(GROUND-ZERO ACL2-WRAP FIND-POSSIBLE-PUT
                          PC-FREE-INSTR-P INSTR-NAME
                          RUN-INSTR-ON-GOALS-GUTS
                          FROMTO PC-STATE-VARS ALL-VARS-GOALS
                          TRANSLATE-GENERALIZE-ALIST
                          TRANSLATE-GENERALIZE-ALIST-2
                          FIND-DUPLICATE-GENERALIZE-ENTRIES
                          NON-GEN-VAR-MARKERS
                          TRANSLATE-GENERALIZE-ALIST-1
                          GEN-VAR-MARKER PRINT-ALL-GOALS
                          RETRIEVE-FN UNSAVE UNSAVE-FN RETRIEVE
                          ASSIGN-EVENT-NAME-AND-RULE-CLASSES
                          CHANGE-LAST UNRELIEVED-HYPS-RAW
                          REMOVE-TRIVIAL-LITS-RAW
                          PC-OPEN-FNCALL FIND-DEFINITION-RULE
                          BUILD-PC-ENABLED-STRUCTURE-FROM-WORLD
                          *DEFAULT-S-REPEAT-LIMIT*
                          MAKE-NEW-GOALS-FROM-ASSUMPTIONS
                          MAKE-GOALS-FROM-ASSUMPTIONS PC-REWRITE*
                          MAKE-REWRITE-INSTR ALIST-DIFFERENCE-EQ
                          UNTRANSLATE-SUBST-ABB
                          INTERSECTION-DOMAINS TRANSLATE-SUBST-ABB
                          CHECK-CARS-ARE-VARIABLES
                          SINGLE-VALUED-SYMBOLP-ALISTP
                          TRANSLATE-SUBST-ABB1
                          HYPS-TYPE-ALIST EXPAND-ASSUMPTIONS
                          EXPAND-ASSUMPTIONS-1 SHOW-REWRITES
                          SET-DIFFERENCE-ASSOC-EQ SHOW-REWRITE
                          UNRELIEVED-HYPS REMOVE-TRIVIAL-LITS
                          PC-RELIEVE-HYPS PC-RELIEVE-HYPS1
                          PC-RELIEVE-HYP APPLICABLE-REWRITE-RULES
                          APPLICABLE-REWRITE-RULES1
                          |Make SAR record|
                          |Change SAR record fields|
                          |Access SAR record field INDEX|
                          |Access SAR record field ALIST|
                          |Access SAR record field LEMMA|
                          FIND-EQUIVALENCE-HYP-TERM-NO-TARGET
                          DEFINE-PC-BIND
                          CHANGE-BY-POSITION EXTRACT-GOAL
                          MODIFIED-ERROR-TRIPLE-FOR-SEQUENCE
                          PRINT-ON-SEPARATE-LINES
                          FIND-EQUIVALENCE-HYP-TERM
                          EQUIV-REFINEMENTP
                          SPLIT-IMPLIES DEPOSIT-TERM-IN-GOAL
                          MAYBE-TRUNCATE-CURRENT-ADDRESS
                          GENEQV-AT-SUBTERM-TOP GENEQV-AT-SUBTERM
                          DEPOSIT-TERM-LST DEPOSIT-TERM
                          DV-ERROR EXPAND-ADDRESS AND-ADDR OR-ADDR
                          ADDR-RECUR ABBREVIATION-RAW-TERM-P
                          DIVE-ONCE-MORE-ERROR
                          EXPAND-ADDRESS-RECURSE
                          DROP-FROM-END PRINT-ABBREVIATIONS
                          NOT-IN-DOMAIN-EQ ADD-FNNAMES-TO-TAG-TREE
                          *BASH-SKIP-FORCING-ROUND-HINTS*
                          ADD-STRING-VAL-PAIR-TO-STRING-VAL-ALIST
                          REMOVE-BYES-FROM-TAG-TREE
                          SAME-GOAL MAKE-NEW-GOALS PROVER-CALL
                          UNPROVED-PC-PROVE-TERMS FIND-?-FN
                          ABBREVIATIONS-ALIST-? SUBLIS-EQUAL
                          ARRAY1P-WEAK PC-PROVE INITIAL-PSPV
                          INITIAL-RCNST NULL-POOL PAIR-KEYWORDS
                          ALL-KEYWORDS-P PAIR-INDICES
                          PRINT-GOVERNORS-TOP PRINT-HYPS-TOP
                          SOME-> PRINT-HYPS TAKE-BY-INDICES P-BODY
                          UNTRANS0-LST UNTRANS0-LST-FN UNTRANS0
                          ABBREVIATE SUBLIS-EXPR-NON-QUOTEPS-LST
                          SUBLIS-EXPR-NON-QUOTEPS
                          TRANS0 TRANSLATE-ABB REMOVE-?S
                          CHK-?S-LST CHK-?S ABBREVIATIONS-ALIST
                          ?-FN ? INVERT-ABBREVIATIONS-ALIST
                          TERM-ID-IFF GOVERNORS FETCH-TERM
                          FETCH-TERM-AND-CL BOUNDED-INTEGER-LISTP
                          REMOVE-BY-INDICES PROMOTE-GUTS
                          CONJUNCTS-OF EVISC-INDEXED-INSTRS
                          MARK-UNFINISHED-INSTRS
                          EVISC-INDEXED-INSTRS-REC
                          EVISC-INDEXED-INSTRS-1
                          DEFINE-PC-HELP RAW-INDEXED-INSTRS
                          MAKE-PRETTY-START-INSTR PRINT-COMMANDS
                          REPLAY-QUERY QUERY-ON-EXIT
                          SET-QUERY-VAL PUT-CDR-ASSOC-QUERY-ID))
 (DEFMACRO
  SYMBOLS::*ACL2-SYMBOLS*1 NIL
  ''(CHK-ASSUMPTION-FREE-TTREE-1 DELETE-BY-POSITION
                                 NON-BOUNDED-NUMS DEFINE-PC-PRIMITIVE
                                 TOGGLE-PC-MACRO DEFINE-PC-ATOMIC-MACRO
                                 DEFINE-PC-MACRO DEFINE-PC-META
                                 DEFINE-PC-META-OR-MACRO-FN
                                 INSTALL-NEW-PC-META-OR-MACRO
                                 *HOME-PAGE-REFERENCES*
                                 *HOME-PAGE* SET-GUARD-CHECKING
                                 GOOD-BYE MINI-PROVEALL
                                 PUFF* PUFF PUFF*-FN PUFF*-FN1 PUFF*-FN11
                                 PUFF-FN PUFF-FN1 PUFFED-COMMAND-SEQUENCE
                                 COMMANDS-BACK-TO PUFF-COMMAND-BLOCK
                                 PUFFABLE-COMMAND-NUMBERP
                                 PUFFABLE-COMMAND-BLOCKP
                                 SCAN-PAST-DEEPER-EVENT-LANDMARKS
                                 COMP COMP-FN
                                 COMPILE-FUNCTION CLTL-DEF-FROM-NAME
                                 SWEEP-GLOBAL-STATE-FOR-LISP-OBJECTS
                                 SWEEP-T-STACK
                                 SWEEP-T-STACK-ENTRY-FOR-BAD-SYMBOL
                                 SWEEP-GLOBAL-LST
                                 SWEEP-SYMBOL-BINDING-FOR-BAD-SYMBOL
                                 *BASIC-SWEEP-ERROR-STR* REBUILD
                                 REBUILD-FN REBUILD-FN-READ-FILTER
                                 I-AM-HERE OOPS OOPS-FN UBT-FN
                                 ROTATE-KILL-RING ROTATE-KILL-RING1
                                 STORE-IN-KILL-RING DELETE-SOMETHING
                                 MAYBE-RESET-DEFAULTS-TABLE
                                 MAYBE-RESET-DEFAULTS-TABLE2
                                 MAYBE-RESET-DEFAULTS-TABLE1
                                 RESET-LD-SPECIALS RESET-LD-SPECIALS-FN
                                 WORMHOLE-PROMPT QUICK-TEST
                                 LD *INITIAL-LD-SPECIAL-BINDINGS*
                                 LD-FN LD-FN1
                                 LD-FN-BODY LD-LOOP LD-READ-EVAL-PRINT
                                 LD-PRINT-PROMPT LD-PRINT-RESULTS
                                 LD-FILTER-COMMAND LD-PRINT-COMMAND
                                 LD-READ-COMMAND LD-READ-KEYWORD-COMMAND
                                 EXIT-LD LD-READ-KEYWORD-COMMAND1
                                 F-GET-LD-SPECIALS
                                 F-PUT-LD-SPECIALS CHK-ACCEPTABLE-LD-FN
                                 CHK-ACCEPTABLE-LD-FN1 CLOSE-CHANNELS
                                 CHK-ACCEPTABLE-LD-FN1-PAIR
                                 REPLACE-LAST-CDR
                                 MAYBE-ADD-COMMAND-LANDMARK
                                 INITIALIZE-TIMERS
                                 PRINT-PROMPT DEFAULT-PRINT-PROMPT
                                 PUT-STOBJS-IN-AND-OUTS
                                 PUT-STOBJS-IN-AND-OUTS1
                                 DEFSTOBJ-RAW-INIT
                                 DEFSTOBJ-RAW-INIT-FIELDS
                                 DEFSTOBJ-RAW-DEFS
                                 DEFSTOBJ-ACCESSOR-AND-UPDATER-RAW-DEFS
                                 DEFSTOBJ-AXIOMATIC-DEFS
                                 DEFSTOBJ-ACCESSOR-AND-UPDATER-AXIOMATIC-DEFS
                                 DEFSTOBJ-COMPONENT-RECOGNIZER-AXIOMATIC-DEFS
                                 DEFSTOBJ-COMPONENT-RECOGNIZER-CALLS
                                 DEFSTOBJ-TEMPLATE
                                 DEFSTOBJ-DOC DEFSTOBJ-FIELDS-TEMPLATE
                                 CHK-ACCEPTABLE-DEFSTOBJ
                                 REDUNDANT-DEFSTOBJP
                                 DEFSTOBJ-REDUNDANCY-BUNDLE
                                 THE-LIVE-VAR CHK-ACCEPTABLE-DEFSTOBJ1
                                 CHK-ACCEPTABLE-DEFSTOBJ-RENAMING
                                 CHK-STOBJ-FIELD-DESCRIPTOR
                                 CHK-LEGAL-DEFSTOBJ-NAME DEFSTOBJ-FNNAME
                                 DOUBLET-STYLE-SYMBOL-TO-SYMBOL-ALISTP
                                 DEFUN-SK NON-ACCEPTABLE-DEFUN-SK-P
                                 DEFCHOOSE-CONSTRAINT
                                 CHK-ARGLIST-FOR-DEFCHOOSE
                                 REDUNDANT-DEFCHOOSEP
                                 DEFSTUB PARTITION-REST-AND-KEYWORD-ARGS
                                 PARTITION-REST-AND-KEYWORD-ARGS2
                                 PARTITION-REST-AND-KEYWORD-ARGS1
                                 DEFSTUB-BODY DEFSTUB-IGNORES
                                 CHK-INPUT-OBJECT-FILE CERTIFY-BOOK!
                                 CERTIFY-BOOK CERTIFY-BOOK-FN
                                 PARSE-BOOK-NAME SET-CBD SET-CBD-FN
                                 CBD CBD-FN COLLECT-IDEAL-USER-DEFUNS
                                 COLLECT-IDEAL-USER-DEFUNS1
                                 READ-OBJECT-FILE
                                 READ-OBJECT-FILE1 OPEN-INPUT-OBJECT-FILE
                                 MAKE-CERTIFICATE-FILE PRINT-OBJECTS
                                 CHK-ACCEPTABLE-CERTIFY-BOOK
                                 CHK-ACCEPTABLE-CERTIFY-BOOK1
                                 CHK-CERTIFICATE-FILE
                                 CHK-CERTIFICATE-FILE1
                                 CHK-RAISE-PORTCULLIS
                                 UNMARK-AND-DELETE-LOCAL-INCLUDED-BOOKS
                                 MARK-LOCAL-INCLUDED-BOOKS
                                 CHK-RAISE-PORTCULLIS1
                                 CHK-RAISE-PORTCULLIS2
                                 TILDE-*-BOOK-HASH-PHRASE1
                                 TILDE-*-BOOK-HASH-PHRASE
                                 INCLUDE-BOOK-ER
                                 *ILL-FORMED-CERTIFICATE-MSG*
                                 CHK-IN-PACKAGE CERTIFICATE-FILEP
                                 COLLECT-UNCERTIFIED-BOOKS
                                 GET-PORTCULLIS-CMDS
                                 INCLUDE-BOOK-ALIST-SUBSETP))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*2 NIL
           ''(STRIP-CDDRS CONVERT-BOOK-NAME-TO-CERT-NAME
                          CHK-BOOK-NAME EXTEND-DIRECTORY
                          STRUCTURED-DIRECTORY-TO-STRING
                          RELATIVE-STRUCTURED-DIRECTORY-TO-STRING
                          CANCEL-BACKS CANCEL-BACKS1
                          ABSOLUTE-STRUCTURED-DIRECTORY-TO-STRING
                          CONCATENATE-STRINGS-WITH-SEPARATOR-STRING
                          STRUCTURED-PATH-P STRUCTURED-DIRECTORY-P
                          DIRECTORY-LIST-P REDUNDANT-ENCAPSULATEP
                          FIND-FIRST-NON-LOCAL-NAME-LST
                          FIND-FIRST-NON-LOCAL-NAME
                          REDUNDANT-EVENT-TUPLEP
                          PRINT-ENCAPSULATE-MSG3
                          PRINT-ENCAPSULATE-MSG3/CONSTRAINTS
                          PRINT-ENCAPSULATE-MSG3/EXPORTED-NAMES
                          PRINT-ENCAPSULATE-MSG2
                          PRINT-ENCAPSULATE-MSG1 ENCAPSULATE-CTX
                          TILDE-@-ABBREVIATE-OBJECT-PHRASE
                          ENCAPSULATE-PASS-2
                          ERASE-INDUCTION-PROPERTIES
                          ITERATIVELY-GROW-CONSTRAINT
                          ITERATIVELY-GROW-CONSTRAINT1
                          DEFINITIONAL-CONSTRAINTS-LIST
                          DEFINITIONAL-CONSTRAINTS
                          CONTAINS-NON-TRIVIAL-ENCAPSULATEP
                          SUBVERSIVE-CLIQUEP SUBVERSIVEP
                          COLLECT-INSTANTIABLES COLLECT-T-MACHINES
                          GET-UNNORMALIZED-BODIES
                          EXPORTED-FUNCTION-NAMES
                          COLLECT-LOGICALS CONSTRAINED-FUNCTIONS
                          PROCESS-EMBEDDED-EVENTS IN-ENCAPSULATEP
                          MAYBE-INSTALL-ACL2-DEFAULTS-TABLE
                          PUTPROP-CONSTRAINTS
                          CONSTRAINTS-INTRODUCED NEW-TRIPS
                          CONSTRAINTS-INTRODUCED1 CLASSES-THEOREMS
                          CONJOIN-INTO-ALIST INTRO-UDF-LST
                          INTRO-UDF-LST2 INTRO-UDF-LST1
                          INTRO-UDF CHK-ACCEPTABLE-ENCAPSULATE2
                          UNION-EQ-CARS TILDE-*-BAD-INSIGS-PHRASE
                          TILDE-*-BAD-INSIGS-PHRASE1
                          BAD-SIGNATURE-ALIST
                          EQUAL-INSIG EVAL-EVENT-LST
                          CHK-EMBEDDED-EVENT-FORM-LST
                          CHK-EMBEDDED-EVENT-FORM
                          *CHK-EMBEDDED-EVENT-FORM-IN-ENCAPSULATE-STRING*
                          ABSOLUTE-PATHNAME-STRING-P
                          DIRECTORY-SEPARATOR OS-ER
                          *CHK-EMBEDDED-EVENT-FORM-IN-LOCAL-STRING*
                          *CHK-EMBEDDED-EVENT-FORM-NORMAL-STRING*
                          *CHK-EMBEDDED-EVENT-FORM-PORTCULLISP-STRING*
                          NAME-INTRODUCED *PRIMITIVE-EVENT-MACROS*
                          CHK-ACCEPTABLE-ENCAPSULATE1
                          CHK-SIGNATURES CHK-SIGNATURE
                          GEN-FORMALS-FROM-PRETTY-FLAGS
                          GEN-FORMALS-FROM-PRETTY-FLAGS1
                          INCOMPATIBLE THEORY-INVARIANT
                          TABLE-FN1 CHK-TABLE-GUARDS
                          CHK-TABLE-GUARD CHK-TABLE-NIL-ARGS
                          ENABLE DISABLE THEORY THEORY-FN
                          THEORY-NAMEP END-PREHISTORIC-WORLD
                          CURRENT-THEORY-FN CURRENT-THEORY1
                          EXECUTABLE-COUNTERPART-THEORY
                          EXECUTABLE-COUNTERPART-THEORY-FN
                          FUNCTION-THEORY FUNCTION-THEORY-FN
                          FUNCTION-THEORY-FN1 UNIVERSAL-THEORY
                          UNIVERSAL-THEORY-FN UNIVERSAL-THEORY-FN1
                          REVAPPEND-DELETE-RUNES-BASED-ON-SYMBOLS
                          APPEND-STRIP-CDRS
                          SET-DIFFERENCE-THEORIES
                          SET-DIFFERENCE-THEORIES-FN
                          SET-DIFFERENCE-AUGMENTED-THEORIES-FN1
                          REV-STRIP-CDRS
                          UNION-THEORIES UNION-THEORIES-FN
                          UNION-AUGMENTED-THEORIES-FN1
                          INTERSECTION-THEORIES
                          INTERSECTION-THEORIES-FN
                          INTERSECTION-AUGMENTED-THEORIES-FN1
                          CHK-ACCEPTABLE-DEFPKG
                          CHK-PACKAGE-REINCARNATION-IMPORT-RESTRICTIONS
                          CHK-NEW-STRINGP-NAME CONFLICTING-IMPORTS
                          SAME-NAME-TWICE PRIMORDIAL-WORLD
                          PRIMORDIAL-WORLD-GLOBALS
                          COLLECT-WORLD-GLOBALS STRIP-CADDRS
                          *INITIAL-TYPE-PRESCRIPTIONS*
                          PRIMORDIAL-EVENT-MACROS-AND-FNS
                          PRIMORDIAL-EVENT-MACRO-AND-FN
                          PRIMORDIAL-EVENT-MACRO-AND-FN1
                          BOOT-TRANSLATE *INITIAL-EVENT-DEFMACROS*
                          REDUNDANT-DEFMACROP CHK-DEFMACRO-WIDTH
                          DEFMACRO-FN1 CHK-MACRO-ARGLIST
                          COLLECT-LAMBDA-KEYWORDPS
                          SUBSEQUENCEP CHK-MACRO-ARGLIST1
                          CHK-MACRO-ARGLIST-OPTIONAL
                          CHK-MACRO-ARGLIST-AFTER-REST
                          CHK-MACRO-ARGLIST-KEYS CHK-LEGAL-INIT
                          DEFCONST-FN1 CHK-LEGAL-DEFCONST-NAME
                          MACRO-VARS MACRO-VARS-OPTIONAL
                          MACRO-VARS-AFTER-REST MACRO-VARS-KEY
                          PL PL-FN DEFCONG DEFREFINEMENT DEFEQUIV
                          GEN-NEW-NAME-IN-PACKAGE-OF-SYMBOL
                          GEN-NEW-NAME-IN-PACKAGE-OF-SYMBOL1
                          EXTEND-RULE-CLASSES
                          CHK-EXTENSIBLE-RULE-CLASSES))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*3 NIL
           ''(THM-FN THM DEFTHM-FN1
                     WARN-ON-INAPPROPRIATE-DEFUN-MODE
                     PRINT-RULE-STORAGE-DEPENDENCIES OK-IF
                     OK-IF-FN EXIT-BRR PROCEED-FROM-BRKPT1
                     MONITORED-RUNES UNMONITOR MONITOR
                     BRR@ BRR BRR-FN MONITORED-RUNES-FN
                     UNMONITOR-FN MONITOR-FN UNMONITOR1
                     MONITOR1 CHK-ACCEPTABLE-MONITORS
                     CHK-ACCEPTABLE-MONITOR
                     COLLECT-NON-BACKCHAIN-SUBCLASS
                     FIND-RULES-OF-RUNE
                     FIND-RULES-OF-RUNE1 FIND-RULES-OF-RUNE2
                     COLLECT-CONGRUENCE-RULES-OF-RUNE
                     COLLECT-CONGRUENCE-RULES-OF-RUNE-IN-GENEQV-LST
                     COLLECT-X-RULES-OF-RUNE
                     ACCESS-X-RULE-RUNE DISABLEDP
                     DISABLEDP-FN DISABLEDP-FN-LST PR! PR
                     PR!-FN WORLD-TO-NEXT-COMMAND NEW-NUMES
                     PR-FN PRINT-RULES1 PRINT-X-RULES
                     PRINT-TYPE-SET-INVERTER-RULES
                     PRINT-INDUCTION-RULES
                     PRINT-TYPE-PRESCRIPTIONS
                     DECODE-TYPE-SET-LST
                     PRINT-FORWARD-CHAINING-RULES
                     PRINT-COARSENINGS PRINT-CONGRUENCES
                     PRINT-ELIMINATE-DESTRUCTORS-RULE
                     PRINT-LINEAR-LEMMAS
                     PRINT-GENERALIZE-RULES
                     PRINT-COMPOUND-RECOGNIZER-RULES
                     PRINT-BUILT-IN-CLAUSE-RULES
                     PRINT-WELL-FOUNDED-RELATION-RULES
                     PRINT-LINEAR-ALIAS-RULES ACTUAL-PROPS
                     ASSOC-EQ-EQ WORLD-TO-NEXT-EVENT
                     PRINT-LEMMAS ENABLED-RUNEP-STRING
                     PROVE-COROLLARIES PROVE-COROLLARIES1
                     NON-TAUTOLOGICAL-CLASSES
                     REDUNDANT-THEOREMP
                     ADD-RULES MAKE-RUNIC-MAPPING-PAIRS
                     MAKE-RUNES MAKE-RUNES1 TRUNCATE-CLASSES
                     TRUNCATE-CLASS-ALIST ADD-RULES1
                     ADD-X-RULE CHK-ACCEPTABLE-RULES
                     CHK-ACCEPTABLE-X-RULES
                     CHK-ACCEPTABLE-X-RULE
                     TRANSLATE-RULE-CLASSES
                     TRANSLATE-RULE-CLASSES1
                     TRANSLATE-RULE-CLASS
                     REASON-FOR-NON-KEYWORD-VALUE-LISTP
                     TRANSLATE-RULE-CLASS1
                     TRANSLATE-RULE-CLASS-ALIST
                     CHK-LEGAL-LINEAR-TRIGGER-TERMS
                     CHK-LEGAL-LINEAR-TRIGGER-TERMS1
                     GUESS-CONTROLLER-ALIST-FOR-DEFINITION-RULE
                     LOOP-STOPPER-ALIST-P
                     ALIST-TO-KEYWORD-ALIST
                     CONTROLLER-ALISTP TRANSLATE-INSTRUCTIONS
                     ADD-TYPE-SET-INVERTER-RULE
                     CHK-ACCEPTABLE-TYPE-SET-INVERTER-RULE
                     ADD-INDUCTION-RULE
                     CHK-ACCEPTABLE-INDUCTION-RULE
                     CHK-ACCEPTABLE-DEFINITION-RULE
                     CHK-DESTRUCTURE-DEFINITION
                     ADD-CONGRUENCE-RULE
                     ADD-CONGRUENCE-RULE-TO-CONGRUENCE
                     PUTNTH CHK-ACCEPTABLE-CONGRUENCE-RULE
                     SOME-CONGRUENCE-RULE-HAS-REFINEMENT
                     SOME-CONGRUENCE-RULE-SAME
                     INTERPRET-TERM-AS-CONGRUENCE-RULE
                     CORRESPONDING-ARGS-EQ-EXCEPT
                     ADD-REFINEMENT-RULE
                     CLOSE-VALUE-SETS EXTEND-EACH-VALUE-SET
                     EXTEND-VALUE-SET UNION-VALUES
                     PUTPROP-COARSENINGS COLLECT-COARSENINGS
                     CHK-ACCEPTABLE-REFINEMENT-RULE
                     ADD-EQUIVALENCE-RULE
                     CHK-ACCEPTABLE-EQUIVALENCE-RULE
                     COLLECT-PROBLEMATIC-PRE-EQUIVALENCE-RULE-NAMES
                     FIND-CANDIDATE-EQUIVALENCE-RELATION
                     EQUIVALENCE-RELATION-CONDITION
                     TRANSITIVITY SYMMETRY REFLEXIVITY
                     BOOLEAN-FN ADD-TYPE-PRESCRIPTION-RULE
                     CHK-ACCEPTABLE-TYPE-PRESCRIPTION-RULE
                     DESTRUCTURE-TYPE-PRESCRIPTION
                     SUBST-NIL-INTO-TYPE-PRESCRIPTION-CONCL
                     SUBST-NIL-INTO-TYPE-PRESCRIPTION-DISJUNCT
                     TYPE-PRESCRIPTION-CONCLP
                     TYPE-PRESCRIPTION-DISJUNCTP
                     FIND-TYPE-PRESCRIPTION-PAT
                     ADD-GENERALIZE-RULE
                     CHK-ACCEPTABLE-GENERALIZE-RULE
                     ADD-ELIM-RULE
                     ADD-ELIM-RULE1 CHK-ACCEPTABLE-ELIM-RULE
                     CHK-ACCEPTABLE-ELIM-RULE1
                     STRIP-FFN-SYMBS DESTRUCTORS-LST
                     DESTRUCTORS ADD-META-RULE
                     ADD-META-RULE1 CHK-ACCEPTABLE-META-RULE
                     CHK-META-FUNCTION
                     META-RULE-HYPOTHESIS-FUNCTION
                     DEFEVALUATOR DEFEVALUATOR-FORM
                     *DEFEVALUATOR-FORM-BASE-THEORY*
                     *S-PROP-THEORY*
                     DEFEVALUATOR-FORM/FNS-CLAUSES
                     DEFEVALUATOR-FORM/DEFTHMS
                     CHK-EVALUATOR GUESS-FN-ARGS-LST-FOR-EVFN
                     FIND-FN-IN-CLAUSE))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*4 NIL
      ''(GUESS-EVFN-LST-FOR-EVFN FIND-EVFN-LST-IN-CLAUSE
                                 SHALLOW-CLAUSIFY SHALLOW-CLAUSIFY1
                                 NORMALIZE-ALLEGED-EVALUATOR-CLAUSE-SET
                                 NORMALIZE-ALLEGED-EVALUATOR-CLAUSE
                                 EXPAND-EQ-AND-ATOM-TERM-LST
                                 CDRP EVALUATOR-CLAUSES
                                 EVALUATOR-CLAUSES1 EVALUATOR-CLAUSE
                                 EVALUATOR-CLAUSE/ARGLIST
                                 ADD-FORWARD-CHAINING-RULE
                                 PUTPROP-FORWARD-CHAINING-RULES-LST
                                 CHK-ACCEPTABLE-FORWARD-CHAINING-RULE
                                 DESTRUCTURE-FORWARD-CHAINING-TERM
                                 CHK-TRIGGERS
                                 ADD-COMPOUND-RECOGNIZER-RULE
                                 CHK-ACCEPTABLE-COMPOUND-RECOGNIZER-RULE
                                 COMMENT-ON-NEW-RECOG-TUPLE
                                 COMMENT-ON-NEW-RECOG-TUPLE1
                                 MAKE-RECOGNIZER-TUPLE
                                 DESTRUCTURE-COMPOUND-RECOGNIZER
                                 ADD-BUILT-IN-CLAUSE-RULE
                                 CLASSIFY-AND-STORE-BUILT-IN-CLAUSE-RULES
                                 MAKE-BUILT-IN-CLAUSE-RULES
                                 CHK-INITIAL-BUILT-IN-CLAUSES
                                 MAKE-BUILT-IN-CLAUSE-RULES1
                                 ALL-FNNAMES-SUBSUMER
                                 BUILT-IN-CLAUSE-DISCRIMINATOR-FN
                                 FN-AND-MAXIMAL-LEVEL-NO-LST
                                 FN-AND-MAXIMAL-LEVEL-NO
                                 CHK-ACCEPTABLE-BUILT-IN-CLAUSE-RULE
                                 CHK-ACCEPTABLE-BUILT-IN-CLAUSE-RULE1
                                 CHK-ACCEPTABLE-BUILT-IN-CLAUSE-RULE2
                                 ADD-WELL-FOUNDED-RELATION-RULE
                                 CHK-ACCEPTABLE-WELL-FOUNDED-RELATION-RULE
                                 DESTRUCTURE-WELL-FOUNDED-RELATION-RULE
                                 ADD-LINEAR-ALIAS-RULE
                                 ADD-LINEAR-ALIAS-RULE1
                                 CHK-ACCEPTABLE-LINEAR-ALIAS-RULE
                                 CHK-ACCEPTABLE-LINEAR-ALIAS-RULE1
                                 CHK-ACCEPTABLE-LINEAR-ALIAS-RULE2
                                 ADD-LINEAR-RULE ADD-LINEAR-RULE1
                                 ADD-LINEAR-RULE2 ADD-LINEAR-RULE3
                                 CHK-ACCEPTABLE-LINEAR-RULE
                                 CHK-ACCEPTABLE-LINEAR-RULE1
                                 CHK-ACCEPTABLE-LINEAR-RULE2
                                 EXTERNAL-LINEARIZE
                                 MAKE-FREE-MAX-TERMS-MSG
                                 MAKE-FREE-MAX-TERMS-MSG1
                                 COLLECT-WHEN-FFNNAMESP MAXIMAL-TERMS
                                 MAXIMAL-TERMS1 NO-ELEMENT-ALWAYS-BIGGERP
                                 ALWAYS-BIGGERP ALWAYS-BIGGERP-DATA-LST
                                 ALWAYS-BIGGERP-DATA
                                 SUBBAGP-EQ ALL-VARS-IN-POLY-LST
                                 EXPAND-INEQUALITY-FNCALL
                                 EXPAND-INEQUALITY-FNCALL1
                                 ADD-REWRITE-RULE
                                 ADD-REWRITE-RULE1 ADD-REWRITE-RULE2
                                 CHK-ACCEPTABLE-REWRITE-RULE
                                 CHK-ACCEPTABLE-REWRITE-RULE1
                                 CHK-ACCEPTABLE-REWRITE-RULE2
                                 BAD-SYNTAXP-HYPS GOOD-SYNTAXP-HYP
                                 CHK-REWRITE-RULE-WARNINGS
                                 STRIP-TOP-LEVEL-NOTS-AND-FORCES
                                 FORCED-HYPS FIND-SUBSUMING-RULE-NAMES
                                 FIND-SUBSUMED-RULE-NAMES
                                 SUBSUMES-REWRITE-RULE MAYBE-SUBSUMES
                                 MAYBE-ONE-WAY-UNIFY-WITH-SOME
                                 MAYBE-ONE-WAY-UNIFY-LST
                                 MAYBE-ONE-WAY-UNIFY
                                 HYPS-THAT-INSTANTIATE-FREE-VARS
                                 FREE-VARS-IN-HYPS CREATE-REWRITE-RULE
                                 REMOVE-IRRELEVANT-LOOP-STOPPER-PAIRS
                                 LOOP-STOPPER LOOP-STOPPER1
                                 SURROUNDING-FNS SURROUNDING-FNS-LST
                                 SURROUNDING-FNS1 VARIANTP HIDE-LAMBDAS
                                 HIDE-LAMBDAS1 NON-RECURSIVE-FNNAMES-LST
                                 NON-RECURSIVE-FNNAMES
                                 INTERPRET-TERM-AS-REWRITE-RULE
                                 REMOVE-LAMBDAS-LST
                                 REMOVE-LAMBDAS UNPRETTYIFY
                                 UNPRETTYIFY/ADD-HYPS-TO-PAIRS VERIFY
                                 PROOF-BUILDER PRINT-PC-STATE PRINT-GOAL
                                 PRINT-DEFTHM STATE-FROM-INSTRUCTIONS
                                 STATE-STACK-FROM-INSTRUCTIONS
                                 PRINT-UNPROVED-GOALS-MESSAGE VERIFY-FN
                                 PC-TOP INSTALL-INITIAL-STATE-STACK
                                 EVENT-NAME-AND-TYPES-AND-RAW-TERM
                                 INITIAL-STATE-STACK MAKE-INITIAL-GOAL
                                 PC-MAIN-LOOP *PC-COMPLETE-SIGNAL*
                                 PC-SINGLE-STEP PC-SINGLE-STEP-1
                                 MAYBE-PRINT-MACROEXPANSION
                                 PC-SINGLE-STEP-PRIMITIVE
                                 MAKE-NEW-GOALS-FIXED-HYPS
                                 INITIAL-RCNST-FROM-ENS
                                 MAKE-PC-ENS UNPROVED-GOALS
                                 ADD-ASSUMPTIONS-TO-TOP-GOAL
                                 KNOWN-ASSUMPTIONS CL-SET-TO-IMPLICATIONS
                                 MAKE-IMPLICATION PC-PROCESS-ASSUMPTIONS
                                 ACCUMULATE-TTREE-IN-PC-STATE
                                 MAYBE-PRINT-PROVED-GOAL-MESSAGE
                                 CURRENT-ALL-DEPS
                                 GOAL-DEPENDENT-P CURRENT-IMMEDIATE-DEPS
                                 PRINT-ALL-GOALS-PROVED-MESSAGE FIND-GOAL
                                 PC-MACROEXPAND PRINT-PC-PROMPT FMS0
                                 INSTRUCTIONS-OF-STATE-STACK GOAL-NAMES
                                 MY-TRANS-EVAL PC-META-OR-MACRO-DEFUN
                                 TOGGLE-PC-MACRO-FN ADD-PC-COMMAND-1
                                 PRINT-NO-CHANGE3 PC-COMMAND-TYPE
                                 TABLE-GET ADD-PC-COMMAND))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*5 NIL
      ''(PC-PRIMITIVE-DEFUN-FORM MAYBE-UPDATE-INSTRUCTION
                                 PRINT-NO-CHANGE-FN
                                 FMT1-PC PRINT-NO-CHANGE2
                                 PRINT-NO-CHANGE CHECK-FIELD-NAMES
                                 LET-FORM-FOR-PC-STATE-VARS
                                 MAKE-ACCESS-BINDINGS ALL-SYMBOLS-LIST
                                 ALL-SYMBOLS MAKE-LET-PAIRS-FROM-FORMALS
                                 CHECK-&OPTIONAL-AND-&REST
                                 CHECK-FORMALS-LENGTH
                                 MAKE-OFFICIAL-PC-INSTR
                                 CHANGE-PC-STATE MAKE-PRETTY-PC-INSTR
                                 MAKE-PRETTY-PC-COMMAND
                                 INTERN-IN-KEYWORD-PACKAGE
                                 MAKE-OFFICIAL-PC-COMMAND
                                 DEPENDS-ON GOAL-NAME CURRENT-ADDR HYPS
                                 CONC *GOAL-FIELDS* |Make GOAL record|
                                 |Change GOAL record fields|
                                 |Access GOAL record field DEPENDS-ON|
                                 |Access GOAL record field GOAL-NAME|
                                 |Access GOAL record field CURRENT-ADDR|
                                 |Access GOAL record field HYPS|
                                 |Access GOAL record field CONC| PC-ENS
                                 TAG-TREE ABBREVIATIONS GOALS INSTRUCTION
                                 *PC-STATE-FIELDS-FOR-PRIMITIVES*
                                 |Make PC-STATE record|
                                 |Change PC-STATE record fields|
                                 |Access PC-STATE record field PC-ENS|
                                 |Access PC-STATE record field TAG-TREE|
                                 |Access PC-STATE record field ABBREVIATIONS|
                                 |Access PC-STATE record field GOALS|
                                 |Access PC-STATE record field INSTRUCTION|
                                 PRINT-PROMPT-AND-INSTR-FLG
                                 PRINT-PROMPT-AND-INSTR-FLG-FN
                                 PRINT-MACROEXPANSION-FLG
                                 PRINT-MACROEXPANSION-FLG-FN
                                 PC-PROMPT-DEPTH-PREFIX
                                 PC-PROMPT-DEPTH-PREFIX-FN
                                 PC-PROMPT PC-PROMPT-FN
                                 DEFINE-GLOBAL SS-ALIST OLD-SS
                                 STATE-STACK INITIALIZE-PC-ACL2 PC-ASSIGN
                                 PC-VALUE CHECK-OUT-INSTANTIABLEP
                                 CHECK-OUT-INSTANTIABLEP1
                                 FNS-USED-IN-AXIOMS
                                 CHK-ACCEPTABLE-VERIFY-TERMINATION
                                 GET-CLIQUE
                                 RECOVER-DEFS-LST UNIFORM-DEFUN-MODES
                                 CHK-ACCEPTABLE-VERIFY-TERMINATION1
                                 MAKE-VERIFY-TERMINATION-DEFS-LST
                                 MAKE-VERIFY-TERMINATION-DEF
                                 ARGS ARGS-FN DEFSTOBJ-FUNCTIONSP
                                 DEFUNS-FN0 CHK-ACCEPTABLE-DEFUNS
                                 CHK-LOGIC-SUBFUNCTIONS
                                 CHK-IRRELEVANT-FORMALS
                                 TILDE-*-IRRELEVANT-FORMALS-MSG
                                 TILDE-*-IRRELEVANT-FORMALS-MSG1
                                 IRRELEVANT-NON-LAMBDA-SLOTS-CLIQUE
                                 IGNORED-SLOTS
                                 ALL-NON-LAMBDA-SLOTS-CLIQUE
                                 RELEVANT-SLOTS-CLIQUE
                                 RELEVANT-SLOTS-CLIQUE1
                                 RELEVANT-SLOTS-DEF RELEVANT-SLOTS-CALL
                                 RELEVANT-SLOTS-TERM-LST
                                 RELEVANT-SLOTS-TERM
                                 MAKE-CLIQUE-ALIST MAKE-CLIQUE-ALIST1
                                 EXPAND-CLIQUE-ALIST EXPAND-CLIQUE-ALIST1
                                 EXPAND-CLIQUE-ALIST-TERM-LST
                                 EXPAND-CLIQUE-ALIST-TERM SLOT-MEMBER
                                 MAKE-SLOTS MAKE-SLOT FORMAL-POSITION
                                 ALL-PROGRAMP COLLECT-WHEN-CADR-EQ
                                 REDUNDANT-OR-RECLASSIFYING-DEFUNSP
                                 REDUNDANT-OR-RECLASSIFYING-DEFUNSP1
                                 REDUNDANT-OR-RECLASSIFYING-DEFUNP
                                 IDENTICAL-DEFP
                                 SET-EQUALP-EQUAL FETCH-DCL-FIELD
                                 FETCH-DCL-FIELD1 STRIP-DCLS
                                 STRIP-DCLS1 STRIP-KEYWORD-LIST
                                 DCL-FIELDS DCL-FIELDS1
                                 PLAUSIBLE-DCLSP PLAUSIBLE-DCLSP1
                                 SCAN-TO-CLTL-COMMAND CHK-DEFUN-MODE
                                 UNPARSE-SIGNATURE STORE-STOBJS-OUT
                                 CHK-STOBJS-OUT-BOUND GET-STOBJS-IN-LST
                                 GET-DECLARED-STOBJ-NAMES
                                 CHK-ALL-STOBJ-NAMES
                                 GET-IGNORES PRINT-DEFUN-MSG
                                 PRINT-DEFUN-MSG/SIGNATURES
                                 PRINT-DEFUN-MSG/SIGNATURES1
                                 ALL-SIMPLE-SIGNATURESP SIMPLE-SIGNATUREP
                                 PRINT-DEFUN-MSG/TYPE-PRESCRIPTIONS
                                 PRINT-DEFUN-MSG/TYPE-PRESCRIPTIONS1
                                 PRINT-DEFUN-MSG/COLLECT-TYPE-PRESCRIPTIONS
                                 DEFUNS-FN-SHORT-CUT COLLECT-OLD-NAMEPS
                                 STORE-SUPER-DEFUN-WARTS-STOBJS-IN
                                 STORE-STOBJS-INS
                                 SUPER-DEFUN-WART-BINDINGS
                                 *SUPER-DEFUN-WART-STOBJS-IN-ALIST*
                                 *SUPER-DEFUN-WART-BINDING-ALIST*
                                 PROJECT-OUT-COLUMNS-I-AND-J
                                 *SUPER-DEFUN-WART-TABLE* APPEND-LST
                                 VERIFY-GUARDS-FN1 PROVE-GUARD-CLAUSES
                                 CHK-ACCEPTABLE-VERIFY-GUARDS
                                 CHK-COMMON-LISP-COMPLIANT-SUBFUNCTIONS
                                 COLLECT-NON-COMMON-LISP-COMPLIANTS
                                 COLLECT-NON-IDEALS))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*6 NIL
           ''(PRINT-VERIFY-GUARDS-MSG
                  GUARD-CLAUSES-FOR-CLIQUE
                  GUARD-CLAUSES-FOR-FN
                  GUARD-CLAUSES-FOR-BODY
                  ALL-SUBROUTINES ALL-SUBROUTINES1
                  PUTPROP-DEFUN-RUNIC-MAPPING-PAIRS
                  PUTPROP-DEFUN-RUNIC-MAPPING-PAIRS1
                  PUTPROP-CONTROLLER-ALISTS
                  MAKE-CONTROLLER-ALIST
                  MAKE-CONTROLLER-POCKET
                  PUTPROP-PRIMITIVE-RECURSIVE-DEFUNP-LST
                  PRIMITIVE-RECURSIVE-MACHINEP
                  PRIMITIVE-RECURSIVE-CALLSP
                  PRIMITIVE-RECURSIVE-CALLP
                  PRIMITIVE-RECURSIVE-ARGP
                  PUTPROP-LEVEL-NO-LST
                  PUTPROP-TYPE-PRESCRIPTION-LST
                  GUESS-AND-PUTPROP-TYPE-PRESCRIPTION-LST-FOR-CLIQUE
                  CLEANSE-TYPE-PRESCRIPTIONS
                  GUESS-AND-PUTPROP-TYPE-PRESCRIPTION-LST-FOR-CLIQUE-STEP
                  GUESS-TYPE-PRESCRIPTION-FOR-FN-STEP
                  TYPE-SET-AND-RETURNED-FORMALS-LST
                  TYPE-SET-AND-RETURNED-FORMALS
                  TYPE-SET-AND-RETURNED-FORMALS-WITH-RULES
                  TYPE-SET-AND-RETURNED-FORMALS-WITH-RULE
                  TYPE-SET-AND-RETURNED-FORMALS-WITH-RULE1
                  MAP-CONS-TAG-TREES VECTOR-TS-UNION
                  MAP-TYPE-SETS-VIA-FORMALS
                  MAP-RETURNED-FORMALS-VIA-FORMALS
                  PUTPROP-INITIAL-TYPE-PRESCRIPTIONS
                  TYPE-SET-IMPLIED-BY-TERM
                  TYPE-SET-IMPLIED-BY-TERM1
                  PUTPROP-BODY-LST
                  ADD-DEFINITION-RULE PREPROCESS-HYPS
                  PREPROCESS-HYP REPLACE-REWRITE-RULE-RUNE
                  MEMBER-REWRITE-RULE-RUNE
                  DESTRUCTURE-DEFINITION
                  PUT-INDUCTION-INFO
                  PUTPROP-QUICK-BLOCK-INFO-LST
                  QUICK-BLOCK-INFO
                  QUICK-BLOCK-DOWN-T-MACHINE
                  QUICK-BLOCK-SETTINGS
                  QUICK-BLOCK-INFO2 QUICK-BLOCK-INFO1
                  QUICK-BLOCK-INITIAL-SETTINGS
                  PUTPROP-INDUCTION-MACHINE-LST
                  INDUCTION-MACHINES
                  INDUCTION-MACHINE-FOR-FN
                  INDUCTION-MACHINE-FOR-FN1
                  PUTPROP-JUSTIFICATION-LST
                  PROVE-TERMINATION TILDE-*-MEASURE-PHRASE
                  TILDE-*-MEASURE-PHRASE1
                  MEASURE-CLAUSES-FOR-CLIQUE
                  MEASURE-CLAUSES-FOR-FN
                  MEASURE-CLAUSES-FOR-FN1
                  MEASURE-CLAUSE-FOR-BRANCH
                  CLEAN-UP-CLAUSE-SET
                  LENGTH-EXCEEDSP REMOVE-BUILT-IN-CLAUSES
                  ADD-LITERAL-TO-CLAUSE-SEGMENTS
                  GUESS-MEASURE-ALIST
                  GUESS-MEASURE ALWAYS-TESTED-AND-CHANGEDP
                  PROPER-DUMB-OCCUR-AS-OUTPUT
                  TERMINATION-MACHINES
                  TERMINATION-MACHINE TERMINATION-MACHINE1
                  ALL-CALLS-ALIST ALL-CALLS-LST
                  ALL-CALLS |Make TESTS-AND-CALL record|
                  |Change TESTS-AND-CALL record fields|
                  |Access TESTS-AND-CALL record field CALL|
                  |Access TESTS-AND-CALL record field TESTS|
                  PUTPROP-RECURSIVEP-LST
                  CHK-MUTUAL-RECURSION
                  CHK-MUTUAL-RECURSION1
                  TRANSLATE-BODIES TRANSLATE-BODIES1
                  PROVE CHK-ASSUMPTION-FREE-TTREE
                  MAKE-PSPV MAKE-RCNST PROVE-LOOP
                  PROVE-LOOP1 PROCESS-ASSUMPTIONS
                  QUICKLY-COUNT-ASSUMPTIONS
                  PROCESS-ASSUMPTIONS-MSG
                  PROCESS-ASSUMPTIONS-MSG1
                  TILDE-*-ASSUMNOTES-COLUMN-PHRASE
                  TILDE-@-ASSUMNOTES-PHRASE-LST
                  SILENT-ERROR POP-CLAUSE
                  POP-CLAUSE-MSG POP-CLAUSE-MSG1
                  MAKE-DEFTHM-FORMS-FOR-BYES
                  POP-CLAUSE1 ADD-TO-POP-HISTORY
                  SOME-POOL-MEMBER-SUBSUMES
                  WATERFALL WATERFALL1-LST WATERFALL0
                  WATERFALL1 MAYBE-WARN-FOR-USE-HINT
                  ENABLED-LMI-NAMES ENABLED-LMI-NAMES1
                  LMI-NAME-OR-RUNE THANKS-FOR-THE-HINT
                  FIND-APPLICABLE-HINT-SETTINGS
                  WATERFALL-STEP
                  EXTRACT-AND-CLAUSIFY-ASSUMPTIONS
                  STRIP-ASSUMPTION-TERMS
                  CLAUSIFY-ASSUMPTIONS
                  CLAUSIFY-ASSUMPTION CLAUSIFY-TYPE-ALIST
                  DUMB-ASSUMPTION-SUBSUMPTION
                  DUMB-ASSUMPTION-SUBSUMPTION1
                  DUMB-KEEP-ASSUMPTIONS-WITH-WEAKEST-TYPE-ALISTS
                  ADD-ASSUMPTION-WITH-WEAK-TYPE-ALIST
                  EXISTS-ASSUMPTION-WITH-WEAKER-TYPE-ALIST
                  PARTITION-ACCORDING-TO-ASSUMPTION-TERM
                  DUMB-TYPE-ALIST-IMPLICATIONP
                  DUMB-TYPE-ALIST-IMPLICATIONP2
                  DUMB-TYPE-ALIST-IMPLICATIONP1
                  UNENCUMBER-ASSUMPTIONS
                  UNENCUMBER-ASSUMPTION
                  UNENCUMBER-TYPE-ALIST
                  DISVAR-TYPE-ALIST COLLECT-ALL-VARS
                  DISVAR-TYPE-ALIST1 LINKED-VARIABLES
                  LINKED-VARIABLES1 DISGUARD-TYPE-ALIST
                  DISGUARD-TYPE-ALIST1 GUARD-CLAUSES-LST
                  GUARD-CLAUSES MAKE-LAMBDA-APPLICATION
                  COLLECT-BY-POSITION
                  ADD-SEGMENTS-TO-CLAUSE
                  SUBLIS-VAR-LST-LST
                  DELETE-ASSUMPTIONS COLLECT-ASSUMPTIONS
                  SET-CL-IDS-OF-ASSUMPTIONS
                  PUT-TTREE-INTO-PSPV WATERFALL-MSG))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*7 NIL
           ''(*PREPROCESS-CLAUSE-LEDGE*
                  INCREMENT-PROOF-TREE
                  REVERT-GOAL-TREE-LST REVERT-GOAL-TREE
                  *STAR-1-CLAUSE-ID* INITIALIZE-PROOF-TREE
                  PREVIOUS-PROCESS-WAS-SPECIOUSP
                  EXTEND-PROOF-TREE-FOR-FORCING-ROUND
                  ASSUMNOTE-LIST-LIST-TO-CLAUSE-ID-LIST-LIST
                  ASSUMNOTE-LIST-TO-CLAUSE-ID-LIST
                  DECORATE-FORCED-GOALS-IN-PROOF-TREE
                  DECORATE-FORCED-GOALS
                  DECORATE-FORCED-GOALS-1-LST
                  DECORATE-FORCED-GOALS-1
                  APPLY-TOP-HINTS-CLAUSE-MSG1
                  TILDE-@-LMI-PHRASE FILTER-ATOMS
                  LMI-TECHS-LST LMI-SEED-LST LMI-TECHS
                  LMI-SEED APPLY-TOP-HINTS-CLAUSE
                  CLAUSE-SET-SUBSUMES
                  PUSH-CLAUSE-MSG1 POOL-LST POOL-LST1
                  PUSH-CLAUSE DELETE-ASSOC-EQ-LST
                  |Make POOL-ELEMENT record|
                  |Change POOL-ELEMENT record fields|
                  |Access POOL-ELEMENT record field HINT-SETTINGS|
                  |Access POOL-ELEMENT record field CLAUSE-SET|
                  |Access POOL-ELEMENT record field TAG|
                  MORE-THAN-SIMPLIFIEDP
                  PREPROCESS-CLAUSE-MSG1
                  TILDE-*-PREPROCESS-PHRASE
                  PREPROCESS-CLAUSE NO-OP-HISTP
                  EXPAND-SOME-NON-REC-FNS-IN-CLAUSES
                  CLAUSIFY-CLAUSE-SET CLAUSIFY-INPUT
                  CLAUSIFY-INPUT1-LST CLAUSIFY-INPUT1
                  EXPAND-AND-OR FIND-AND-OR-LEMMA
                  AND-ORP EXPAND-ABBREVIATIONS-LST
                  EXPAND-ABBREVIATIONS
                  FIND-ABBREVIATION-LEMMA ALL-VARS-BAG-LST
                  ALL-VARS-BAG ABBREVIATIONP
                  ABBREVIATIONP1-LST ABBREVIATIONP1
                  EVAL-AND-TRANSLATE-HINT-EXPRESSION
                  TRANSLATE-HINTS
                  TRANSLATE-HINT TRANSLATE-HINT-EXPRESSION
                  TRANSLATE-HINT-SETTINGS
                  TRANSLATE-X-HINT-VALUE *HINT-KEYWORDS*
                  TRANSLATE-BDD-HINT TRANSLATE-BDD-HINT1
                  COLLECT-NON-FUNCTION-SYMBOLS
                  ALL-FUNCTION-SYMBOLPS
                  TRANSLATE-IN-THEORY-HINT
                  *BUILT-IN-EXECUTABLE-COUNTERPARTS*
                  CHK-THEORY-EXPR-VALUE
                  CHK-THEORY-EXPR-VALUE1
                  CHK-THEORY-INVARIANT
                  CHK-THEORY-INVARIANT1
                  TRANSLATE-INDUCT-HINT
                  TRANSLATE-CASES-HINT TRANSLATE-BY-HINT
                  CONVERT-NAME-TREE-TO-NEW-NAME
                  CONVERT-NAME-TREE-TO-NEW-NAME1
                  TRANSLATE-USE-HINT
                  TRANSLATE-USE-HINT1 TRANSLATE-LMI
                  TRANSLATE-LMI/FUNCTIONAL-INSTANCE
                  TRANSLATE-LMI/INSTANCE
                  FREE-OR-BOUND-VARS-LST
                  FREE-OR-BOUND-VARS RELEVANT-CONSTRAINTS
                  RELEVANT-CONSTRAINTS1-AXIOMS
                  RELEVANT-CONSTRAINTS1
                  ADD-TO-SET FILTER-HITPS GETPROP-X-LST
                  EVENT-RESPONSIBLE-FOR-PROVED-CONSTRAINT
                  RESTRICT-ALIST
                  HITP-LST HITP INSTANTIABLE-ANCESTORS
                  IMMEDIATE-INSTANTIABLE-ANCESTORS
                  INSTANTIABLE-FFN-SYMBS-LST
                  INSTANTIABLE-FFN-SYMBS
                  LAMBDA-FREE-VARS SUBLIS-FN-LST SUBLIS-FN
                  TRANSLATE-FUNCTIONAL-SUBSTITUTION
                  EXTEND-SORTED-SYMBOL-ALIST
                  CHK-EQUAL-ARITIES CONSTRAINT
                  CONSTRAINT-INFO ALL-FFN-SYMBS-LST
                  ALL-FFN-SYMBS INSTANTIABLEP
                  *NON-INSTANTIABLE-PRIMITIVES*
                  MERGE-SORT-SYMBOL-<
                  MERGE-SYMBOL-< PF PF-FN FORMULA
                  COROLLARY TESTS-AND-ALISTS-LST-FROM-FN
                  TRUNCATED-CLASS
                  CONVERT-TYPE-PRESCRIPTION-TO-TERM
                  IMPLICATE
                  CONVERT-RETURNED-VARS-TO-TERM-LST
                  TRANSLATE-HANDS-OFF-HINT
                  TRANSLATE-HANDS-OFF-HINT1
                  TRANSLATE-DO-NOT-INDUCT-HINT
                  TRANSLATE-DO-NOT-HINT
                  CHK-DO-NOT-EXPR-VALUE
                  COERCE-TO-ACL2-PACKAGE-LST
                  COERCE-TO-PROCESS-NAME-LST
                  *DO-NOT-PROCESSES*
                  TRANSLATE-RESTRICT-HINT
                  TRANSLATE-SUBSTITUTION-LST
                  TRANSLATE-SUBSTITUTION CONS-ALL-TO-LST
                  GET-REWRITE-RUNES-FROM-RUNIC-MAPPING-PAIRS
                  TRANSLATE-EXPAND-HINT
                  TRANSLATE-EXPAND-HINT1
                  TRANSLATE-FREE-TERM
                  TRANSLATE-TERM-LST PUTPROP-X-LST2-UNLESS
                  PUTPROP-X-LST2 PUTPROP-X-LST1
                  CHK-FREE-AND-IGNORED-VARS-LSTS
                  SYMBOL-LIST-LISTP
                  CHK-FREE-AND-IGNORED-VARS
                  CHK-DECLARED-IGNORES
                  CHK-FREE-VARS GET-BODIES
                  GET-NAMES GET-DECLARED-IGNORED-VARIABLES
                  CHK-XARGS-KEYWORDS CHK-XARGS-KEYWORDS1))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*8 NIL
      ''(GET-UNAMBIGUOUS-XARGS-FLG GET-UNAMBIGUOUS-XARGS-FLG1
                                   GET-UNAMBIGUOUS-XARGS-FLG1/EDCLS
                                   GET-GUARD-HINTS
                                   GET-GUARD-HINTS1 GET-HINTS GET-HINTS1
                                   GET-MEASURES GET-MEASURES2 GET-MEASURES1
                                   GET-GUARDSP GET-GUARDS GET-GUARDS1
                                   GET-DOCS CHK-DEFUNS-TUPLES CHK-ARGLIST
                                   REMOVE-ALL-EQ CHK-NO-DUPLICATE-DEFUNS
                                   SHOW-BDD-FN SHOW-BDD-BACKTRACE
                                   TILDE-*-SUBSTITUTION-PHRASE
                                   TILDE-*-SUBSTITUTION-PHRASE1
                                   SHOW-BDD-TERM
                                   SHOW-FALSIFYING-ASSIGNMENT SHOW-BDD-GOAL
                                   SHOW-BDD UPDATE-BDDNOTE-WITH-TERM
                                   LOOKUP-BDDNOTE WALKABOUT=
                                   WALKABOUT=-FN WALKABOUT WALKABOUT1
                                   WALKABOUT-HUH WALKABOUT-IP WALKABOUT-NTH
                                   PROPS PROPS-FN TILDE-*-PROPS-FN-PHRASE
                                   TILDE-*-PROPS-FN-PHRASE1 TRANS1
                                   TRANS1-FN TRANS TRANS-FN
                                   DOC
                                   DOC-FN
                                   PRINT-DOC-DWIM FIND-LIKELY-NEAR-MISSES
                                   DEGREE-OF-MATCH DEGREE-OF-MATCH1
                                   DEGREE-OF-MATCH2
                                   REDUNDANT-LABELP
                                   GET-EVENT REDEFINED-WARNING
                                   PUTPROP-UNLESS
                                   MERGE-SORT-ALPHA-< MERGE-ALPHA-<
                                   ALPHA-<
                                   CHK-JUST-NEW-NAMES NO-NEW-NAMESP
                                   CHK-JUST-NEW-NAME CHK-REDEFINEABLE-NAMEP
                                   REDEFINED-NAMES REDEFINED-NAMES1
                                   REDEFINITION-RENEWAL-MODE
                                   ACL2-SYSTEM-NAMEP
                                   MAYBE-COERCE-OVERWRITE-TO-ERASE
                                   CHK-BOOT-STRAP-REDEFINEABLE-NAMEP
                                   CHK-ALL-BUT-NEW-NAME
                                   CHK-VIRGIN U UBT! UBT
                                   UBT-QUERY COLLECT-NAMES-IN-DEFUN-MODES
                                   ACL2-QUERY ACL2-QUERY1
                                   ACL2-QUERY-SIMULATE-INTERACTION
                                   SYMBOL-NAME-LST COMMAND-BLOCK-NAMES))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*9 NIL
      ''(COMMAND-BLOCK-NAMES1 REVERT-WORLD-ON-ERROR
                              SET-W! FIND-LONGEST-COMMON-RETRACTION
                              FIND-LONGEST-COMMON-RETRACTION1 PE!
                              PE!-FN PE!-FN1 PE PE-FN PE-FN1 PCB PBT
                              PCS PCS-FN PC PC-FN PCB! PCB-FN PCB!-FN
                              PCB-PCB!-FN MAKE-LDDS-COMMAND-BLOCK
                              MAKE-LDDS-COMMAND-BLOCK1
                              MAKE-LDDS-COMMAND-SEQUENCE
                              MAKE-EVENT-LDD
                              MAKE-COMMAND-LDD PRINT-LDDS
                              PRINT-LDD PRINT-LDD-FULL-OR-SKETCH
                              STRING-MATCHP NORMALIZE-STRING
                              NORMALIZE-STRING1 NORMALIZE-CHAR
                              PRINT-LDD-FULL-OR-SKETCH/ENCAPSULATE
                              PRINT-LDD-FULL-OR-SKETCH/MUTUAL-RECURSION
                              BIG-C-LITTLE-C-COMMAND-BLOCK
                              BIG-C-LITTLE-C-EVENT
                              DEFUN-MODE-STRING SYMBOL-CLASS-CHAR
                              BIG-D-LITTLE-D-COMMAND-BLOCK
                              BIG-D-LITTLE-D-EVENT
                              BIG-D-LITTLE-D-CLIQUE
                              BIG-D-LITTLE-D-CLIQUE1
                              BIG-D-LITTLE-D-NAME
                              BIG-D-LITTLE-D-NAME1 ACCESS-LDD-FORM
                              ACCESS-LDD-N ACCESS-LDD-FULLP
                              ACCESS-LDD-CDPAIR ACCESS-LDD-MARKP
                              ACCESS-LDD-CLASS MAKE-LDD MAKE-LDD-FLAGS
                              ER-DECODE-CD SUPERIOR-COMMAND-WORLD
                              CD-SEARCH CD-SOME-EVENT-MATCHP
                              CD-FORM-MATCHP TREE-OCCUR
                              NORMALIZE-ABSOLUTE-COMMAND-NUMBER
                              RELATIVE-TO-ABSOLUTE-COMMAND-NUMBER
                              ABSOLUTE-TO-RELATIVE-COMMAND-NUMBER
                              STOP-REDUNDANT-EVENT
                              INSTALL-EVENT ADD-COMMAND-LANDMARK
                              PROVED-FUNCTIONAL-INSTANCES-FROM-TAGGED-OBJECTS
                              SUPPLY-CDDR-FOR-LST
                              WITH-CTX-SUMMARIZED PRINT-SUMMARY
                              PRINT-RULES-SUMMARY ALL-RUNES-IN-TTREE
                              ALL-RUNES-IN-ELIM-SEQUENCE
                              ALL-RUNES-IN-VAR-TO-RUNES-ALIST
                              ALL-RUNES-IN-LMI-LST
                              ALL-RUNES-IN-LMI PRINT-TIME-SUMMARY
                              PRINT-WARNINGS-SUMMARY
                              INITIALIZE-SUMMARY-ACCUMULATORS
                              PRINT-REDEFINITION-WARNING SCRUNCH-EQ
                              COLLECT-REDEFINED-ALIST RENEW-NAMES
                              RENEW-NAME DEFSTOBJ-SUPPORTERP
                              RENEW-NAME/OVERWRITE RENEW-NAME/ERASE
                              RENEW-LEMMAS ER-DECODE-LOGICAL-NAME
                              DECODE-LOGICAL-NAME
                              POSSIBLY-ADD-LISP-EXTENSION
                              MULTIPLE-ASSOC-TERMINAL-SUBSTRINGP
                              MULTIPLE-ASSOC-TERMINAL-SUBSTRINGP1
                              ASSOC-EQUAL-CADR SCAN-TO-INCLUDE-BOOK
                              SCAN-TO-DEFPKG ADD-EVENT-LANDMARK
                              THE-NAMEX-SYMBOL-CLASS
                              THE-NAMEX-SYMBOL-CLASS1
                              STORE-ABSOLUTE-EVENT-NUMBER
                              LOOKUP-WORLD-INDEX
                              LOOKUP-WORLD-INDEX1 UPDATE-WORLD-INDEX
                              *COMMAND-INDEX-INTERVAL*
                              *EVENT-INDEX-INTERVAL*
                              FETCH-FROM-ZAP-TABLE
                              ADD-TO-ZAP-TABLE SCAN-TO-LANDMARK-NUMBER
                              SCAN-TO-COMMAND SCAN-TO-EVENT
                              NEXT-ABSOLUTE-COMMAND-NUMBER
                              MAX-ABSOLUTE-COMMAND-NUMBER
                              NEXT-ABSOLUTE-EVENT-NUMBER
                              MAX-ABSOLUTE-EVENT-NUMBER
                              ACCESS-EVENT-TUPLE-NUMBER
                              ACCESS-COMMAND-TUPLE-FORM
                              ACCESS-COMMAND-TUPLE-DEFUN-MODE
                              ACCESS-COMMAND-TUPLE-NUMBER
                              MAKE-COMMAND-TUPLE *EVISCERATED-COMMAND*
                              ACCESS-EVENT-TUPLE-SYMBOL-CLASS
                              ACCESS-EVENT-TUPLE-FORM
                              ACCESS-EVENT-TUPLE-NAMEX
                              ACCESS-EVENT-TUPLE-TYPE
                              ACCESS-EVENT-TUPLE-DEPTH
                              MAKE-EVENT-TUPLE
                              SIGNATURE-FNS *EVISCERATED-EVENT*
                              LOGICAL-NAME-TYPE-STRING
                              LOGICAL-NAME-TYPE
                              LOGICAL-NAMEP PRINT-PROOF-TREE
                              *PROOF-TREE-END-DELIMITER*
                              *PROOF-TREE-START-DELIMITER*
                              PRINT-PROOF-TREE-CTX
                              *PROOF-FAILURE-STRING* PRINT-PROOF-TREE1
                              FORMAT-PROOF-TREE FORMAT-GOAL-TREE
                              FORMAT-GOAL-TREE-LST FORMAT-PROCESSOR))
 (DEFMACRO
     SYMBOLS::*ACL2-SYMBOLS*10 NIL
     ''(FORMAT-FORCED-SUBGOALS *FORMAT-PROC-ALIST*
                               PRINT-STRING-REPEAT PRUNE-PROOF-TREE
                               PRUNE-GOAL-TREE-LST PRUNE-GOAL-TREE
                               SET-DIFFERENCE-EQUAL-CHANGEDP
                               INSERT-INTO-GOAL-TREE-LST
                               INSERT-INTO-GOAL-TREE
                               STOP-PROOF-TREE STOP-PROOF-TREE-FN
                               CHECKPOINT-FORCED-GOALS
                               START-PROOF-TREE START-PROOF-TREE-FN
                               INITIALIZE-FROM-ALIST
                               |Make GOAL-TREE record|
                               |Change GOAL-TREE record fields|
                               |Access GOAL-TREE record field FANOUT|
                               |Access GOAL-TREE record field CL-ID|
                               |Access GOAL-TREE record field PROCESSOR|
                               |Access GOAL-TREE record field CHILDREN|
                               ELIMINATE-IRRELEVANCE-CLAUSE-MSG1
                               ELIMINATE-IRRELEVANCE-CLAUSE
                               IRRELEVANT-LITS PROBABLY-NOT-VALIDP
                               FFNNAMES-SUBSETP-LISTP
                               FFNNAMES-SUBSETP PAIR-VARS-WITH-LITS
                               INDUCT REMOVE-TRIVIAL-CLAUSES
                               RESTORE-HINT-SETTINGS-IN-PSPV
                               LOAD-HINT-SETTINGS-INTO-PSPV
                               UPDATE-HINT-SETTINGS DELETE-ASSOC-EQ
                               LOAD-HINT-SETTINGS-INTO-RCNST
                               INDUCT-MSG/LOSE INDUCT-MSG/CONTINUE
                               TILDE-@-WELL-FOUNDED-RELATION-PHRASE
                               UNMEASURED-VARIABLES
                               UNMEASURED-VARIABLES1
                               UNMEASURED-VARIABLES2
                               UNMEASURED-VARIABLES3
                               INDUCTION-MEASURE GEN-NEW-NAME
                               GEN-NEW-NAME1 MERGE-SORT-TERM-ORDER
                               MERGE-TERM-ORDER ALL-VARS1-LST-LST
                               INFORM-SIMPLIFY INFORM-SIMPLIFY1
                               INFORM-SIMPLIFY2 INFORM-SIMPLIFY3
                               TERMIFY-CLAUSE-SET *MAXIMUM-INDUCT-SIZE*
                               INDUCTION-FORMULA-SIZE
                               INDUCTION-FORMULA-SIZE1 ALL-PICKS-SIZE
                               INDUCTION-FORMULA INDUCTION-FORMULA1
                               INDUCTION-FORMULA2 INDUCTION-FORMULA3
                               INDUCTION-HYP-CLAUSE-SEGMENTS
                               INDUCTION-HYP-CLAUSE-SEGMENTS1
                               INDUCTION-HYP-CLAUSE-SEGMENTS2
                               DUMB-NEGATE-LIT-LST-LST ALL-PICKS
                               ALL-PICKS1 ALL-PICKS2R ALL-PICKS2
                               M&M-OVER-POWERSET M&M-OVER-POWERSET1
                               OR-SUBSET-TREES CDR-SUBSET-TREE
                               CAR-SUBSET-TREE CONS-SUBSET-TREE
                               M&M M&M1 M&M-SEARCH COUNT-OFF M&M-APPLY
                               SUBSETP-EQUAL/SMALLER EQUAL/UNION-EQUAL
                               INTERSECTP-EQ/UNION-EQUAL
                               MAXIMAL-ELEMENTS
                               MAXIMAL-ELEMENTS1 MAXIMAL-ELEMENTS-APPLY
                               INDUCTION-COMPLEXITY1
                               COMPUTE-VETOES COMPUTE-VETOES2
                               COMPUTE-VETOES1 VETOEDP INDUCT-VARS
                               INDUCT-VARS1 CONTROLLER-VARIABLES
                               CONTROLLER-VARIABLES1
                               MERGE-CANDIDATES MERGE-CAND1-INTO-CAND2
                               MERGE-TESTS-AND-ALISTS-LSTS
                               MERGE-LST1-INTO-LST2
                               MERGE-LST1-INTO-ALIST2-LST
                               MERGE-LST1-INTO-ALIST2
                               MERGE-ALIST1-LST-INTO-ALIST2
                               MERGE-ALIST1-INTO-ALIST2
                               EVERY-ALIST1-MATEDP
                               ANTAGONISTIC-TESTS-AND-ALISTS-LSTSP
                               ANTAGONISTIC-TESTS-AND-ALISTS-LSTP
                               CONTAINS-AFFINITY
                               ALL-OCCUR-AFFINITY SOME-OCCUR-AFFINITY
                               OCCUR-AFFINITY MEMBER-AFFINITY
                               AFFINITY IRRECONCILABLE-ALISTSP
                               ALISTS-AGREEP FLUSH-CANDIDATES
                               FLUSH-CAND1-DOWN-CAND2 PIGEON-HOLEP1
                               PIGEON-HOLEP PIGEON-HOLEP-APPLY
                               REMOVE-CANDIDATES-THAT-CHANGE-UDF-VARS
                               REMOVE-CANDIDATES-THAT-CHANGE-UDF-VARS1
                               UDF-VARS-FROM-CL-SET
                               UDF-VARS-LST UDF-VARS UDF-VARS1
                               GET-INDUCTION-CANDS-FROM-CL-SET
                               GET-INDUCTION-CANDS-FROM-CL-SET1
                               GET-INDUCTION-CANDS-LST
                               GET-INDUCTION-CANDS
                               SUGGESTED-INDUCTION-CANDS
                               SUGGESTED-INDUCTION-CANDS1
                               APPLY-INDUCTION-RULE
                               |Make INDUCTION-RULE record|
                               |Change INDUCTION-RULE record fields|
                               |Access INDUCTION-RULE record field RUNE|
                               |Access INDUCTION-RULE record field SCHEME|
                               |Access INDUCTION-RULE record field CONDITION|
                               |Access INDUCTION-RULE record field PATTERN|
                               |Access INDUCTION-RULE record field NUME|
                               INTRINSIC-SUGGESTED-INDUCTION-CAND
                               FLESH-OUT-INDUCTION-PRINCIPLE
                               TESTS-AND-ALISTS-LST TESTS-AND-ALISTS
                               |Make JUSTIFICATION record|
                               |Change JUSTIFICATION record fields|
                               |Access JUSTIFICATION record field MEASURE|
                               |Access JUSTIFICATION record field REL|
                               |Access JUSTIFICATION record field MP|
                               |Access JUSTIFICATION record field SUBSET|
                               |Make TESTS-AND-CALLS record|))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*11 NIL
           ''(|Change TESTS-AND-CALLS record fields|
                  |Access TESTS-AND-CALLS record field CALLS|
                  |Access TESTS-AND-CALLS record field TESTS|
                  TESTS-AND-ALISTS/ALISTS
                  TESTS-AND-ALISTS/ALIST
                  |Make TESTS-AND-ALISTS record|
                  |Change TESTS-AND-ALISTS record fields|
                  |Access TESTS-AND-ALISTS record field ALISTS|
                  |Access TESTS-AND-ALISTS record field TESTS|
                  CHANGED/UNCHANGED-VARS CONTROLLERS
                  COUNT-NON-NILS |Make CANDIDATE record|
                  |Change CANDIDATE record fields|
                  |Access CANDIDATE record field TTREE|
                  |Access CANDIDATE record field XANCESTRY|
                  |Access CANDIDATE record field XOTHER-TERMS|
                  |Access CANDIDATE record field XINDUCTION-TERM|
                  |Access CANDIDATE record field OTHER-TERMS|
                  |Access CANDIDATE record field INDUCTION-TERM|
                  |Access CANDIDATE record field JUSTIFICATION|
                  |Access CANDIDATE record field TESTS-AND-ALISTS-LST|
                  |Access CANDIDATE record field UNCHANGEABLE-VARS|
                  |Access CANDIDATE record field CHANGED-VARS|
                  |Access CANDIDATE record field CONTROLLERS|
                  |Access CANDIDATE record field SCORE|
                  SOUND-INDUCTION-PRINCIPLE-MASK
                  SOUND-INDUCTION-PRINCIPLE-MASK1
                  CHANGEABLES UNCHANGEABLES
                  SELECT-X-CL-SET GENERALIZE-CLAUSE-MSG1
                  TILDE-*-GEN-PHRASE
                  TILDE-*-GEN-PHRASE/ALIST
                  TILDE-*-GEN-PHRASE/ALIST1
                  GENERALIZE-CLAUSE GENERALIZABLE-TERMS
                  GENERALIZABLE-TERMS-ACROSS-LITERALS
                  GENERALIZABLE-TERMS-ACROSS-LITERALS1
                  GENERALIZABLE-TERMS-ACROSS-RELATIONS
                  GENERALIZING-RELATIONP
                  SMALLEST-COMMON-SUBTERMS
                  SMALLEST-COMMON-SUBTERMS1-LST
                  SMALLEST-COMMON-SUBTERMS1
                  COLLECTABLE-FNP
                  FERTILIZE-CLAUSE-MSG1 FERTILIZE-CLAUSE
                  TILDE-@-HYP-PHRASE FERTILIZE-CLAUSE1
                  CROSS-FERTILIZEP CROSS-FERTILIZEP/D
                  CROSS-FERTILIZEP/C FIRST-FERTILIZE-LIT
                  MAXIMIZE-FERTILIZE-COMPLEXITY
                  FERTILIZE-COMPLEXITY FERTILIZE-FEASIBLE
                  ALREADY-USED-BY-FERTILIZE-CLAUSEP
                  DUMB-OCCUR-LST-EXCEPT
                  DESTRUCTOR-APPLIED-TO-VARSP
                  ALMOST-QUOTEP
                  ALMOST-QUOTEP1-LISTP ALMOST-QUOTEP1
                  ELIMINATE-DESTRUCTORS-CLAUSE-MSG1
                  TILDE-*-UNTRANSLATE-LST-PHRASE
                  TILDE-*-ELIM-PHRASE TILDE-*-ELIM-PHRASE1
                  TILDE-*-ELIM-PHRASE2
                  TILDE-*-ELIM-PHRASE3
                  TILDE-*-ELIM-PHRASE/ALIST
                  TILDE-*-ELIM-PHRASE/ALIST1
                  PRETTYIFY-CLAUSE-SET
                  PRETTYIFY-CLAUSE-LST
                  PRETTYIFY-CLAUSE PRETTYIFY-CLAUSE1
                  ELIMINATE-DESTRUCTORS-CLAUSE
                  OWNED-VARS ELIMINATE-DESTRUCTORS-CLAUSE1
                  APPLY-INSTANTIATED-ELIM-RULE
                  GENERALIZE1 GENERALIZE-RULE-SEGMENT
                  GENERALIZE-RULE-SEGMENT1
                  APPLY-GENERALIZE-RULE
                  |Make GENERALIZE-RULE record|
                  |Change GENERALIZE-RULE record fields|
                  |Access GENERALIZE-RULE record field RUNE|
                  |Access GENERALIZE-RULE record field FORMULA|
                  |Access GENERALIZE-RULE record field NUME|
                  SUBTERM-ONE-WAY-UNIFY-LST
                  SUBTERM-ONE-WAY-UNIFY
                  TYPE-RESTRICTION-SEGMENT
                  CONVERT-TYPE-SET-TO-TERM
                  CONVERT-TYPE-SET-TO-TERM-LST
                  *INITIAL-TYPE-SET-INVERTER-RULES*
                  |Make TYPE-SET-INVERTER-RULE record|
                  |Change TYPE-SET-INVERTER-RULE record fields|
                  |Access TYPE-SET-INVERTER-RULE record field RUNE|
                  |Access TYPE-SET-INVERTER-RULE record field TERMS|
                  |Access TYPE-SET-INVERTER-RULE record field TS|
                  |Access TYPE-SET-INVERTER-RULE record field NUME|
                  SUBLIS-EXPR-LST SUBLIS-EXPR
                  SELECT-INSTANTIATED-ELIM-RULE
                  PICK-HIGHEST-SUM-LEVEL-NOS SUM-LEVEL-NOS
                  NOMINATE-DESTRUCTOR-CANDIDATES-LST
                  NOMINATE-DESTRUCTOR-CANDIDATES
                  NOMINATE-DESTRUCTOR-CANDIDATE
                  SOME-HYP-PROBABLY-NILP SECOND-NOMINATION
                  FIRST-NOMINATION OCCURS-NOWHERE-ELSE
                  |Make ELIM-RULE record|
                  |Change ELIM-RULE record fields|
                  |Access ELIM-RULE record field RUNE|
                  |Access ELIM-RULE record field RHS|
                  |Access ELIM-RULE record field LHS|
                  |Access ELIM-RULE record field HYPS|
                  |Access ELIM-RULE record field DESTRUCTOR-TERMS|
                  |Access ELIM-RULE record field DESTRUCTOR-TERM|
                  |Access ELIM-RULE record field CRUCIAL-POSITION|
                  |Access ELIM-RULE record field NUME|
                  GENERATE-VARIABLE-LST
                  GENERATE-VARIABLE GENERATE-VARIABLE-ROOT
                  GENERATE-VARIABLE-ROOT1
                  ABBREVIATE-HYPHENATED-STRING
                  ABBREVIATE-HYPHENATED-STRING1
                  FIRST-NON-MEMBER-EQ
                  ASSOC-TS-SUBSETP *VAR-FAMILIES-BY-TYPE*
                  STRIP-FINAL-DIGITS
                  STRIP-FINAL-DIGITS1 IF* BDD-CLAUSE
                  EXPAND-CLAUSE EXPAND-AND-OR-SIMPLE
                  EXPAND-AND-OR-SIMPLE+ BDD-CLAUSE1
                  GET-BOOL-VARS BDD-TOP REMOVE1-EQ
                  LEAF-CST-LIST-TO-ALIST OP-HT-MAX-LENGTH
                  IF-HT-MAX-LENGTH BDD-LIST
                  BDD-ALIST BDD COMBINE-OP-CSTS-GUTS
                  COMBINE-OP-CSTS-COMM COMBINE-OP-CSTS))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*12 NIL
      ''(MAKE-IF-FOR-OP COMBINE-OP-CSTS+
                        BDD-EV-FNCALL |Make BDDSPV record|
                        |Change BDDSPV record fields|
                        |Access BDDSPV record field BDD-CONSTRUCTORS|
                        |Access BDDSPV record field BDD-RULES-ALIST|
                        |Access BDDSPV record field OP-ALIST|
                        CST-QUOTE-LISTP
                        CST-LIST-TO-EVG-LIST COMBINE-IF-CSTS
                        COMBINE-IF-CSTS1 COMBINE-IF-CSTS+
                        MV-LET? COMBINE-OP-CSTS-SIMPLE
                        SOME-BDD-CONSTRUCTORP
                        BOOL-FLG COMBINE-OP-CSTS1
                        MIN-VAR SPLIT-VAR MAKE-IF-NO-MEMO
                        MAKE-IF FALSIFYING-ASSIGNMENT
                        FALSIFYING-ASSIGNMENT1
                        LEAF-CST-LIST-ARRAY
                        DECODE-CST-ALIST DECODE-CST-ALIST1
                        DECODE-CST-LST DECODE-CST
                        LEAF-CST-LIST SOME-ONE-WAY-UNIFY-CST-LST
                        ONE-WAY-UNIFY1-CST-EQUAL
                        ONE-WAY-UNIFY1-CST-LST
                        ONE-WAY-UNIFY1-CST ONE-WAY-UNIFY1-CST-3
                        ONE-WAY-UNIFY1-CST-2 BDD-RULES-ALIST
                        EXTRA-RULES-FOR-BDDS BDD-RULES-ALIST1
                        REWRITE-RULE-TO-BDD-RULE
                        |Make BDD-RULE record|
                        |Change BDD-RULE record fields|
                        |Access BDD-RULE record field RUNE|
                        |Access BDD-RULE record field RHS|
                        |Access BDD-RULE record field LHS|
                        BDD-QUOTEP+ BDD-QUOTEP CHK-MEMO-QUOTEP
                        OP-SEARCH-BUCKET-QUOTE OP-HASH-INDEX-EVG
                        OP-HASH-INDEX-STRING FOURTH-HASH-SIZE
                        HALF-HASH-SIZE CHK-MEMO-IF
                        CHK-MEMO-2 CHK-MEMO OP-SEARCH-BUCKET-IF
                        OP-SEARCH-BUCKET-2 OP-SEARCH-BUCKET
                        EQ-OP CST=-LST IF-SEARCH-BUCKET
                        OP-HASH-INDEX-IF OP-HASH-INDEX-2
                        OP-HASH-INDEX OP-HASH-INDEX1
                        *F IF-HASH-INDEX HASH-SIZE IF-OP-CODE
                        OP-ALIST-INFO OP-ALIST COMMUTATIVE-P
                        EQUIVALENCE-RUNE EQUIVALENCE-RUNE1
                        COMMUTATIVE-P1 BOOL-MASK RECOGNIZER-RUNE
                        FIRST-BOOLEAN-TYPE-PRESCRIPTION
                        BOOL-MASK1 CST-NONNILP
                        CST-VARP CST-NILP CST-TP CST=
                        *CST-NIL* *CST-T* MAKE-IF-CST EVG-TYPE
                        BDD-CONSTRUCTOR-TRM-P EVG-FN-SYMB
                        MAKE-LEAF-CST BDD-CONSTRUCTORS TRM
                        LEAFP FBR TBR CST-BOOLP TST UNIQUE-ID
                        BDD-ERROR |1+MX-ID| MX-ID-BOUND
                        LOGANDF MVF SETTLED-DOWN-CLAUSE-MSG1
                        SIMPLIFY-CLAUSE-MSG1
                        PARSE-CLAUSE-ID PARSE-CLAUSE-ID1
                        PARSE-CLAUSE-ID2 PARSE-PRIMES
                        PARSE-MATCH PARSE-DOTTED-NATURALS
                        PARSE-NATURAL TILDE-@-BDDNOTE-PHRASE
                        |Make BDDNOTE record|
                        |Change BDDNOTE record fields|
                        |Access BDDNOTE record field TTREE|
                        |Access BDDNOTE record field BDD-CALL-STACK|
                        |Access BDDNOTE record field TERM|
                        |Access BDDNOTE record field CST|
                        |Access BDDNOTE record field FMT-ALIST|
                        |Access BDDNOTE record field ERR-STRING|
                        |Access BDDNOTE record field MX-ID|
                        |Access BDDNOTE record field GOAL-TERM|
                        |Access BDDNOTE record field CL-ID|
                        STRING-FOR-TILDE-@-CLAUSE-ID-PHRASE
                        STRING-FOR-TILDE-@-CLAUSE-ID-PHRASE/PRIMES
                        STRING-FOR-TILDE-@-CLAUSE-ID-PHRASE/PERIODS
                        TILDE-@-CLAUSE-ID-PHRASE
                        TILDE-@-POOL-NAME-PHRASE-LST
                        TILDE-@-POOL-NAME-PHRASE
                        *INITIAL-CLAUSE-ID*
                        |Make CLAUSE-ID record|
                        |Change CLAUSE-ID record fields|
                        |Access CLAUSE-ID record field PRIMES|
                        |Access CLAUSE-ID record field CASE-LST|
                        |Access CLAUSE-ID record field POOL-LST|
                        |Access CLAUSE-ID record field FORCING-ROUND|
                        TILDE-*-SIMP-PHRASE RECOVER-FORCED-RUNES
                        TILDE-*-SIMP-PHRASE1
                        TILDE-*-CONJUNCTION-OF-POSSIBLY-FORCED-NAMES-PHRASE
                        TILDE-*-CONJUNCTION-OF-POSSIBLY-FORCED-NAMES-PHRASE1
                        EXTRACT-AND-CLASSIFY-LEMMAS
                        SETTLED-DOWN-CLAUSE SIMPLIFY-CLAUSE
                        FILTER-DISABLED-EXPAND-TERMS
                        *EMPTY-PROVE-SPEC-VAR*
                        |Make PROVE-SPEC-VAR record|))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*13 NIL
           ''(|Change PROVE-SPEC-VAR record fields|
                  |Access PROVE-SPEC-VAR record field OTF-FLG|
                  |Access PROVE-SPEC-VAR record field ORIG-HINTS|
                  |Access PROVE-SPEC-VAR record field DISPLAYED-GOAL|
                  |Access PROVE-SPEC-VAR record field USER-SUPPLIED-TERM|
                  |Access PROVE-SPEC-VAR record field POOL|
                  |Access PROVE-SPEC-VAR record field HINT-SETTINGS|
                  |Access PROVE-SPEC-VAR record field TAG-TREE|
                  |Access PROVE-SPEC-VAR record field INDUCTION-CONCL-TERMS|
                  |Access PROVE-SPEC-VAR record field INDUCTION-HYP-TERMS|
                  |Access PROVE-SPEC-VAR record field REWRITE-CONSTANT|
                  SOME-ELEMENT-DUMB-OCCUR-LST
                  SIMPLIFY-CLAUSE1 ENUMERATE-ELEMENTS
                  PROCESS-EQUATIONAL-POLYS
                  FIND-EQUATIONAL-POLY
                  FIND-EQUATIONAL-POLY1
                  FIND-EQUATIONAL-POLY2
                  FIND-EQUATIONAL-POLY3
                  FIND-EQUATIONAL-POLY-RHS
                  FIND-EQUATIONAL-POLY-RHS1
                  CONS-TERM-BINARY-*-CONSTANT
                  CONS-TERM-UNARY--
                  CONS-TERM-BINARY-+-CONSTANT
                  ALREADY-USED-BY-FIND-EQUATIONAL-POLYP
                  ALREADY-USED-BY-FIND-EQUATIONAL-POLYP1
                  DESCENDS-FROM-NOT-EQUALITYP
                  DESCENDS-FROM-NOT-EQUALITYP1
                  FCOMPLEMENTARY-MULTIPLEP
                  FCOMPLEMENTARY-MULTIPLEP1
                  SETUP-SIMPLIFY-CLAUSE-POT-LST
                  REWRITE-CLAUSE-LST
                  REWRITE-CLAUSE CONS-INTO-TTREE
                  RESUME-SUSPENDED-ASSUMPTION-REWRITING
                  RESUME-SUSPENDED-ASSUMPTION-REWRITING1
                  STRIP-NON-REWRITTENP-ASSUMPTIONS
                  CRUNCH-CLAUSE-SEGMENTS
                  CRUNCH-CLAUSE-SEGMENTS2
                  CRUNCH-CLAUSE-SEGMENTS1 BUILT-IN-CLAUSEP
                  TRIVIAL-CLAUSE-P DISJOIN
                  DISJOIN2 POSSIBLE-TRIVIAL-CLAUSE-P
                  BUILT-IN-CLAUSEP1 BUILT-IN-CLAUSEP2
                  *INITIAL-BUILT-IN-CLAUSES*
                  |Make BUILT-IN-CLAUSE record|
                  |Change BUILT-IN-CLAUSE record fields|
                  |Access BUILT-IN-CLAUSE record field RUNE|
                  |Access BUILT-IN-CLAUSE record field CLAUSE|
                  |Access BUILT-IN-CLAUSE record field ALL-FNNAMES|
                  |Access BUILT-IN-CLAUSE record field NUME|
                  REMOVE-TRIVIAL-EQUIVALENCES
                  SUBST-EQUIV-AND-MAYBE-DELETE-LIT
                  ADD-LITERAL-AND-PT ADD-LITERAL-AND-PT1
                  FIND-TRIVIAL-EQUIVALENCE
                  FIND-TRIVIAL-EQUIVALENCE1
                  EQUIV-HITTABLE-IN-SOME-OTHER-LIT
                  SOME-OCCURRENCE-EQUIV-HITTABLEP
                  SOME-OCCURRENCE-EQUIV-HITTABLEP1-LISTP
                  SOME-OCCURRENCE-EQUIV-HITTABLEP1
                  EVERY-OCCURRENCE-EQUIV-HITTABLEP-IN-CLAUSEP
                  EVERY-OCCURRENCE-EQUIV-HITTABLEP
                  EVERY-OCCURRENCE-EQUIV-HITTABLEP1-LISTP
                  EVERY-OCCURRENCE-EQUIV-HITTABLEP1
                  REWRITE-ATM REWRITE-CLAUSE-TYPE-ALIST
                  SELECT-FORWARD-CHAINED-CONCLS-AND-TTREES
                  FORWARD-CHAIN
                  PTS-TO-TTREE-LST FC-PAIR-LST-TYPE-ALIST
                  FC-PAIR-LST FORWARD-CHAIN1
                  STRIP-FCD-CONCLS SORT-APPROVED
                  SORT-APPROVED1 SORT-APPROVED1-RATING
                  SORT-APPROVED1-RATING1-LST
                  SORT-APPROVED1-RATING1
                  GET-LEVEL-NO MAX-LEVEL-NO-LST
                  MAX-LEVEL-NO APPROVE-FC-DERIVATIONS
                  APPROVED-FC-DERIVATIONP
                  EXISTS-FCD-WORSE-THAN-OR-EQUAL
                  EXISTS-LIT-WORSE-THAN-OR-EQUAL
                  FCD-WORSE-THAN-OR-EQUAL FCD-RUNEP
                  TYPE-ALIST-FCD-LST ADVANCE-FC-POT-LST
                  ADVANCE-FC-ACTIVATIONS
                  ADVANCE-FC-ACTIVATION
                  ADVANCE-FC-ACTIVATION1
                  SCONS-TAG-TREES ADD-FC-DERIVATIONS
                  EXPUNGE-FC-DERIVATIONS
                  MAKE-TTREES-FROM-FC-DERIVATIONS
                  RELIEVE-FC-HYPS SUSPEND-FC-ACTIVATION
                  ADD-NEW-FC-POTS-LST-LST
                  ADD-NEW-FC-POTS-LST ADD-NEW-FC-POTS
                  FC-ACTIVATION-LST FC-ACTIVATION
                  |Make FC-ACTIVATION record|
                  |Change FC-ACTIVATION record fields|
                  |Access FC-ACTIVATION record field RULE|
                  |Access FC-ACTIVATION record field INST-TRIGGER|
                  |Access FC-ACTIVATION record field UNIFY-SUBST|
                  |Access FC-ACTIVATION record field TTREE|
                  |Access FC-ACTIVATION record field HYPS|
                  |Access FC-ACTIVATION record field INST-HYP|
                  |Make FORWARD-CHAINING-RULE record|
                  |Change FORWARD-CHAINING-RULE record fields|
                  |Access FORWARD-CHAINING-RULE record field CONCLS|
                  |Access FORWARD-CHAINING-RULE record field HYPS|
                  |Access FORWARD-CHAINING-RULE record field TRIGGER|
                  |Access FORWARD-CHAINING-RULE record field NUME|
                  |Access FORWARD-CHAINING-RULE record field RUNE|
                  REWRITE-CLAUSE-ACTION
                  SPLIT-ON-ASSUMPTIONS
                  DISJOIN-CLAUSE-SEGMENT-TO-CLAUSE-SET
                  DISJOIN-CLAUSE-SEGMENTS-TO-CLAUSE
                  DISJOIN-CLAUSES
                  SOME-ELEMENT-MEMBER-COMPLEMENT-TERM
                  CONJOIN-CLAUSE-SETS ADD-EACH-LITERAL-LST
                  CONJOIN-CLAUSE-TO-CLAUSE-SET
                  DELETE-SUBSUMED-MEMBERS
                  SOME-MEMBER-SUBSUMES SUBSUMES1 SUBSUMES
                  ADD-EACH-LITERAL ADD-LITERAL PEGATE-LIT
                  NEGATE-LIT DUMB-NEGATE-LIT-LST
                  |Make HISTORY-ENTRY record|
                  |Change HISTORY-ENTRY record fields|
                  |Access HISTORY-ENTRY record field TTREE|
                  |Access HISTORY-ENTRY record field CLAUSE|
                  |Access HISTORY-ENTRY record field PROCESSOR|
                  REWRITE-WITH-LINEAR
                  ADD-TERM-AND-LEMMAS ADD-TERMS-AND-LEMMAS
                  ADD-DISJUNCTS-POLYS-AND-LEMMAS
                  ADD-DISJUNCT-POLYS-AND-LEMMAS))
 (DEFMACRO
  SYMBOLS::*ACL2-SYMBOLS*14 NIL
  ''(ADD-POLYS-AND-LEMMAS
        ADD-POLYS-AND-LEMMAS1
        ADD-LINEAR-LEMMAS ADD-LINEAR-LEMMA
        REWRITE-LINEAR-CONCL REWRITE-WITH-LEMMAS
        REWRITE-FNCALL REWRITE-WITH-LEMMAS1
        REWRITE-WITH-LEMMA RELIEVE-HYPS
        RELIEVE-HYPS1 RELIEVE-HYP REWRITE-EQUAL
        REWRITE-PRIMITIVE REWRITE-ARGS
        REWRITE-IF REWRITE EVGS-OR-T
        FLATTEN-ANDS-IN-LIT EV-FNCALL-META
        EV-FNCALL! ONE-WAY-UNIFY-RESTRICTIONS
        ONE-WAY-UNIFY-RESTRICTIONS1
        EXPAND-PERMISSION-P FREE-P BRKPT2 BRKPT1
        BRR-PROMPT DEFUN-MODE-PROMPT-STRING
        STUFF-STANDARD-OI
        TILDE-@-FAILURE-REASON-PHRASE
        EVAL-BREAK-CONDITION
        TRANSLATE-BREAK-CONDITION
        DECODE-TYPE-ALIST
        POP-BRR-STACK-FRAME PUSH-BRR-STACK-FRAME
        SOME-CDR-EQUALP PUT-BRR-LOCAL-LST
        PUT-BRR-LOCAL PUT-BRR-LOCAL1
        GET-BRR-LOCAL CLEAN-BRR-STACK
        LOOKUP-BRR-STACK INITIALIZE-BRR-STACK
        BRR-WORMHOLE EXIT-BRR-WORMHOLE
        GET-BRR-GLOBAL SAVE-BRR-GLOBALS
        RESTORE-BRR-GLOBALS RESTORE-BRR-GLOBALS1
        CW-GSTACK CW-GSTACK1 CW-GFRAME
        TILDE-@-BKPTR-PHRASE INITIAL-GSTACK
        PUSH-GFRAME |Make GFRAME record|
        |Change GFRAME record fields|
        |Access GFRAME record field ARGS|
        |Access GFRAME record field BKPTR|
        |Access GFRAME record field SYS-FN|
        *FAKE-RUNE-FOR-LINEAR*
        REWRITE-ENTRY ADD-REWRITE-ARGS
        PLIST-TO-ALIST BACKCHAIN-LIMIT-REACHEDP
        BACKCHAIN-LIMIT-REACHEDP1
        OK-TO-FORCE *EMPTY-REWRITE-CONSTANT*
        |Make REWRITE-CONSTANT record|
        |Change REWRITE-CONSTANT record fields|
        |Access REWRITE-CONSTANT record field CURRENT-LITERAL|
        |Access REWRITE-CONSTANT record field CURRENT-CLAUSE|
        |Access REWRITE-CONSTANT record field TOP-CLAUSE|
        |Access REWRITE-CONSTANT record field TERMS-TO-BE-IGNORED-BY-REWRITE|
        |Access REWRITE-CONSTANT record field FNS-TO-BE-IGNORED-BY-REWRITE|
        |Access REWRITE-CONSTANT record field FORCE-INFO|
        |Access REWRITE-CONSTANT record field EXPAND-LST|
        |Access REWRITE-CONSTANT record field RESTRICTIONS-ALIST|
        |Access REWRITE-CONSTANT record field PT|
        |Access REWRITE-CONSTANT record field BACKCHAIN-LIMIT|
        |Access REWRITE-CONSTANT record field CURRENT-ENABLED-STRUCTURE|
        |Make CURRENT-LITERAL record|
        |Change CURRENT-LITERAL record fields|
        |Access CURRENT-LITERAL record field ATM|
        |Access CURRENT-LITERAL record field NOT-FLG|
        INFECT-NEW-POLYS
        INFECT-FIRST-N-POLYS INFECT-POLYS
        NO-NEW-AND-UGLY-LINEAR-VARSP
        ALIST-CONTAINS-A-NEW-AND-UGLY-LINEAR-VARP
        NEW-AND-UGLY-LINEAR-VARP
        |Make LINEAR-LEMMA record|
        |Change LINEAR-LEMMA record fields|
        |Access LINEAR-LEMMA record field RUNE|
        |Access LINEAR-LEMMA record field CONCL|
        |Access LINEAR-LEMMA record field MAX-TERM|
        |Access LINEAR-LEMMA record field FIXER|
        |Access LINEAR-LEMMA record field HYPS|
        |Access LINEAR-LEMMA record field NUME|
        NEW-VARS-IN-POT-LST
        ADD-POLYS ADD-POLYS1 FILTER-POLYS
        ADD-POLY ADD-POLY1 MODIFY-LINEAR-POT
        CANCEL-POLY-AGAINST-ALL-POLYS
        CANCEL-POLY-AGAINST-TYPE-SET
        CANCEL CANCEL1 CANCEL2 TO-BE-IGNOREDP
        POLY-MEMBER FIRST-COEFFICIENT FIRST-VAR
        SHOW-POT-LST |Make LINEAR-POT record|
        |Change LINEAR-POT record fields|
        |Access LINEAR-POT record field POSITIVES|
        |Access LINEAR-POT record field VAR|
        |Access LINEAR-POT record field NEGATIVES|
        LINEARIZE-LST
        LINEARIZE EVAL-GROUND-SUBEXPRESSIONS-LST
        EVAL-GROUND-SUBEXPRESSIONS
        REWRITE-WITH-LINEAR-ALIASES-LST
        REWRITE-WITH-LINEAR-ALIASES
        FIND-LINEAR-ALIAS FIND-LINEAR-ALIAS1
        FIND-LINEAR-ALIAS-RELIEVE-HYPS
        PAIRLIS-X2 PAIRLIS-X1
        |Make LINEAR-ALIAS-RULE record|
        |Change LINEAR-ALIAS-RULE record fields|
        |Access LINEAR-ALIAS-RULE record field RUNE|
        |Access LINEAR-ALIAS-RULE record field HYPS|
        |Access LINEAR-ALIAS-RULE record field RHS|
        |Access LINEAR-ALIAS-RULE record field LHS|
        |Access LINEAR-ALIAS-RULE record field NUME|
        POLY-SET SILLY-POLYP
        COLLAPSE-IMPOSSIBLE-POLY-DISJUNCT
        ADD-LINEAR-TERM
        ADD-LINEAR-VARIABLE ADD-LINEAR-VARIABLE1
        ADD-LINEAR-VARIABLE-TO-ALIST TRUE-POLYP
        IMPOSSIBLE-POLYP EVALUATE-GROUND-POLY))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*15 NIL
           ''(SHOW-POLY-LST
                  SHOW-POLY SHOW-POLY1 SHOW-POLY2
                  LOGICAL-<= LOGICAL-< |Make POLY record|
                  |Change POLY record fields|
                  |Access POLY record field RELATION|
                  |Access POLY record field CONSTANT|
                  |Access POLY record field TTREE|
                  |Access POLY record field ALIST|
                  TS-INTEGERP
                  TS-RATIONALP TS-ACL2-NUMBERP INEQUALITYP
                  CONTAINS-REWRITEABLE-CALLP-LST
                  CONTAINS-REWRITEABLE-CALLP
                  REWRITE-FNCALLP-LISTP REWRITE-FNCALLP
                  SOME-CONTROLLER-POCKET-CONSTANT-AND-NON-CONTROLLER-SIMPLERP
                  CONSTANT-CONTROLLER-POCKETP
                  CONSTANT-CONTROLLER-POCKETP1
                  SOME-CONTROLLER-POCKET-SIMPLERP
                  CONTROLLER-COMPLEXITY
                  CONTROLLER-COMPLEXITY1
                  MAX-FORM-COUNT-LST MAX-FORM-COUNT
                  ALL-ARGS-OCCUR-IN-TOP-CLAUSEP
                  TOO-MANY-IFS TOO-MANY-IFS1
                  COUNT-IFS-LST COUNT-IFS OCCUR-CNT-LST
                  OCCUR-CNT RECURSIVE-FN-ON-FNSTACKP
                  BEING-OPENEDP MAKE-TRUE-LIST-CONS-NEST
                  TAUTOLOGYP EXPAND-SOME-NON-REC-FNS-LST
                  EXPAND-SOME-NON-REC-FNS IF-TAUTOLOGYP
                  SEARCH-GROUND-UNITS SEARCH-GROUND-UNITS1
                  |Make REWRITE-RULE record|
                  |Change REWRITE-RULE record fields|
                  |Access REWRITE-RULE record field HEURISTIC-INFO|
                  |Access REWRITE-RULE record field SUBCLASS|
                  |Access REWRITE-RULE record field OUTSIDE-IN|
                  |Access REWRITE-RULE record field RHS|
                  |Access REWRITE-RULE record field LHS|
                  |Access REWRITE-RULE record field EQUIV|
                  |Access REWRITE-RULE record field HYPS|
                  |Access REWRITE-RULE record field NUME|
                  |Access REWRITE-RULE record field RUNE|
                  COMMUTE-EQUALITIES-LST
                  COMMUTE-EQUALITIES LOOP-STOPPERP
                  LOOP-STOPPERP-REC INVISIBLE-FNS
                  TERM-ORDER+ REMOVE-INVISIBLE-FNS
                  REWRITE-RECOGNIZER NOT-TO-BE-REWRITTENP
                  NOT-TO-BE-REWRITTENP1
                  REWRITE-IF1 REWRITE-SOLIDIFY
                  OBJ-TABLE FIND-REWRITING-EQUIVALENCE
                  CLAUSIFY SUBSUMPTION-REPLACEMENT-LOOP
                  STORE-CLAUSE STORE-CLAUSE1
                  REMOVE-ONE-+- FIND-CLAUSES FIND-CLAUSES1
                  DISC-TREE FILTER-WITH-AND-WITHOUT
                  SWEEP-CLAUSES SWEEP-CLAUSES1
                  WEAK-DISC-TREE REMOVE-ONE-COMPLEMENT
                  FIND-SUBSUMER-REPLACEMENT
                  PSEUDO-TERM-LIST-LISTP
                  ARG1-ALMOST-SUBSUMES-ARG2
                  MEMBER-EQUAL-+- MERGE-SORT-LENGTH
                  MERGE-LENGTH STRIP-BRANCHES
                  SPLICE-INSTRS SPLICE-INSTRS1
                  IF-INTERP IF-INTERP-ADD-CLAUSE
                  QUICK-AND-DIRTY-SUBSUMPTION-REPLACEMENT-STEP
                  QUICK-AND-DIRTY-SUBSUMPTION-REPLACEMENT-STEP1
                  RET-STACK CALL-STACK
                  SIMPLIFIABLE-MV-NTHP SYMBOLIC-MV-NTH
                  CONVERT-CLAUSE-TO-ASSUMPTIONS
                  CONVERT-ASSUMPTIONS-TO-CLAUSE-SEGMENT
                  IF-INTERP-ASSUMED-VALUE
                  IF-INTERP-ASSUMED-VALUE-X
                  IF-INTERP-ASSUMED-VALUE2
                  IF-INTERP-ASSUMED-VALUE1
                  IF-INTERP-ASSUMED-VALUE0
                  IF-INTERP-SWITCH
                  IF-INTERP-ASSUME-TRUE IF-COMPILE-LST
                  IF-COMPILE FFNNAMEP-HIDE-LST
                  FFNNAMEP-HIDE IF-COMPILE-FORMAL
                  NEXT-TAG SPLICED-INSTR-LISTP
                  INSTR-LISTP MEMBER-COMPLEMENT-TERM
                  MEMBER-TERM MEMBER-COMPLEMENT-TERM1
                  MEMBER-COMPLEMENT-TERM2
                  MEMBER-TERM2 COMPLEMENTARYP
                  COMM-EQUAL COLLECT-FFNNAMES-LST
                  COLLECT-FFNNAMES FFNNAMESP-LST FFNNAMESP
                  FFNNAMEP-LST FFNNAMEP SUBST-EQUIV-EXPR
                  SUBST-EQUIV-EXPR1-LST SUBST-EQUIV-EXPR1
                  SCONS-TERM ALL-QUOTEPS SUBST-EXPR
                  SUBST-EXPR-ERROR SUBST-EXPR1-LST
                  SUBST-EXPR1 SUBST-VAR-LST
                  SUBST-VAR GENEQV-LST GENEQV-LST1
                  PAIRWISE-UNION-GENEQV UNION-GENEQV
                  UNION-GENEQV1 FILTER-GENEQV-LST
                  FILTER-GENEQV-LST1 SOME-GENEQV-DISABLEDP
                  FILTER-GENEQV FILTER-GENEQV1))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*16 NIL
           ''(SOME-CONGRUENCE-RULE-DISABLEDP
                  GENEQV-REFINEMENTP GENEQV-REFINEMENTP1
                  REFINEMENTP *GENEQV-IFF*
                  |Make CONGRUENCE-RULE record|
                  |Change CONGRUENCE-RULE record fields|
                  |Access CONGRUENCE-RULE record field RUNE|
                  |Access CONGRUENCE-RULE record field EQUIV|
                  |Access CONGRUENCE-RULE record field NUME|
                  PT-INTERSECTP
                  PT-OCCUR GIT ENS DTS DECODE-TYPE-SET
                  DECODE-TYPE-SET1 DISTRIBUTE-FIRST-IF
                  NORMALIZE-OR-DISTRIBUTE-FIRST-IF
                  NORMALIZE-LST NORMALIZE
                  NORMALIZE-WITH-TYPE-SET ALL-VARIABLEP
                  FIRST-IF NOT-IDENT EQUAL-X-CONS-X-YP
                  WEAK-CONS-OCCUR TS-BOOLEANP
                  KNOWN-WHETHER-NIL TYPE-ALIST-CLAUSE
                  TYPE-ALIST-CLAUSE-FINISH
                  TYPE-ALIST-CLAUSE-FINISH1
                  RECONSIDER-TYPE-ALIST
                  TYPE-ALIST-EQUALITY-LOOP
                  *TYPE-ALIST-EQUALITY-LOOP-MAX-DEPTH*
                  TYPE-ALIST-EQUALITY-LOOP-EXIT
                  CLEAN-TYPE-ALIST DUPLICATE-KEYSP
                  CLEAN-UP-ALIST TYPE-ALIST-EQUALITY-LOOP1
                  RETURN-TYPE-ALIST ASSUMPTION-FREE-TTREEP
                  TAG-TREE-OCCUR-ASSUMPTION-NIL
                  ADD-ASSUMPTION
                  *IMPOSSIBLE-ASSUMPTION* OK-TO-FORCE-ENS
                  EXTEND-WITH-PROPER/IMPROPER-CONS-TS-TUPLE
                  PROPER/IMPROPER-CONS-TS-TUPLE
                  ASSUME-TRUE-FALSE1 ASSUME-TRUE-FALSE
                  TYPE-SET-PRIMITIVE TYPE-SET-WITH-RULES
                  TYPE-SET-WITH-RULE1 TYPE-SET-WITH-RULE
                  EXTEND-TYPE-ALIST-WITH-BINDINGS
                  TYPE-SET-RELIEVE-HYPS TYPE-SET-LST
                  TYPE-SET ASSUME-TRUE-FALSE-<
                  WITH-ACCUMULATED-PERSISTENCE POP-ACCP
                  PUSH-ACCP SHOW-ACCUMULATED-PERSISTENCE
                  SHOW-ACCUMULATED-PERSISTENCE-PHRASE
                  SHOW-ACCUMULATED-PERSISTENCE-PHRASE2
                  SHOW-ACCUMULATED-PERSISTENCE-PHRASE1
                  MERGE-SORT-CAR->
                  MERGE-CAR-> ACCUMULATED-PERSISTENCE
                  ADD-ACCUMULATED-PERSISTENCE
                  DELETE1-EQUAL
                  SUBLIS-VAR-AND-MARK-FREE-LST
                  SUBLIS-VAR-AND-MARK-FREE FREE-VARSP-LST
                  FREE-VARSP LOOKUP-HYP SEARCH-TYPE-ALIST
                  TYPE-SET-FINISH ANCESTORS-CHECK
                  ANCESTORS-CHECK1 WORSE-THAN-LST
                  SOME-SUBTERM-WORSE-THAN-OR-EQUAL-LST
                  SOME-SUBTERM-WORSE-THAN-OR-EQUAL
                  QUICK-WORSE-THAN QUICK-WORSE-THAN-LST2
                  QUICK-WORSE-THAN-LST1
                  WORSE-THAN-OR-EQUAL WORSE-THAN OCCUR-LST
                  OCCUR EVG-OCCUR TERMINAL-SUBSTRINGP
                  TERMINAL-SUBSTRINGP1 MEMBER-CHAR-STRINGP
                  ASSOC-TYPE-ALIST ASSOC-EQUIV+
                  ASSOC-EQUIV ZIP-VARIABLE-TYPE-ALIST
                  EXTEND-TYPE-ALIST EXTEND-TYPE-ALIST1
                  EXTEND-TYPE-ALIST-SIMPLE
                  SUBST-TYPE-ALIST SUBST-TYPE-ALIST1
                  CANONICAL-REPRESENTATIVE
                  ONE-WAY-UNIFY ONE-WAY-UNIFY1-EQUAL
                  ONE-WAY-UNIFY1-EQUAL1
                  ONE-WAY-UNIFY1-LST ONE-WAY-UNIFY1
                  *ONE-WAY-UNIFY1-IMPLICIT-FNS*
                  NON-CONS-CDR
                  ASSUME-TRUE-FALSE-ERROR MV-ATF
                  *EXPANDABLE-BOOT-STRAP-NON-REC-FNS*
                  FIND-RUNED-TYPE-PRESCRIPTION
                  |Make TYPE-PRESCRIPTION record|
                  |Change TYPE-PRESCRIPTION record fields|
                  |Access TYPE-PRESCRIPTION record field COROLLARY|
                  |Access TYPE-PRESCRIPTION record field RUNE|
                  |Access TYPE-PRESCRIPTION record field VARS|
                  |Access TYPE-PRESCRIPTION record field HYPS|
                  |Access TYPE-PRESCRIPTION record field TERM|
                  |Access TYPE-PRESCRIPTION record field NUME|
                  |Access TYPE-PRESCRIPTION record field BASIC-TS|
                  TERM-ORDER
                  LEXORDER ALPHORDER FN-VAR-COUNT-LST
                  FN-VAR-COUNT FN-COUNT-EVG
                  TYPE-SET-CHAR-CODE TYPE-SET-QUOTE
                  TYPE-SET-EQUAL *SINGLETON-TYPE-SETS*
                  TYPE-SET-CONS TYPE-SET-LENGTH
                  TYPE-SET-INTERN-IN-PACKAGE-OF-SYMBOL
                  TYPE-SET-COERCE TYPE-SET-CDR
                  TYPE-SET-CAR TYPE-SET-RECOGNIZER
                  MOST-RECENT-ENABLED-RECOG-TUPLE
                  *INITIAL-RECOGNIZER-ALIST*
                  |Make RECOGNIZER-TUPLE record|
                  |Change RECOGNIZER-TUPLE record fields|
                  |Access RECOGNIZER-TUPLE record field RUNE|
                  |Access RECOGNIZER-TUPLE record field STRONGP|
                  |Access RECOGNIZER-TUPLE record field FALSE-TS|
                  |Access RECOGNIZER-TUPLE record field TRUE-TS|
                  |Access RECOGNIZER-TUPLE record field NUME|))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*17 NIL
      ''(|Access RECOGNIZER-TUPLE record field FN|
             TYPE-SET-COMPLEX
             TYPE-SET-IMAGPART TYPE-SET-REALPART
             TYPE-SET-NUMERATOR TYPE-SET-UNARY-/
             TYPE-SET-UNARY-- TYPE-SET-<
             TYPE-SET-NOT TYPE-SET-BINARY-*
             TYPE-SET-BINARY-+ RATIONAL-TYPE-SET
             NUMERIC-TYPE-SET IMMEDIATE-FORCEP
             PUFFERT *FAKE-RUNE-FOR-TYPE-SET*
             FORCE-ASSUMPTION
             ALL-DUMB-OCCUR-IN-TYPE-ALIST
             DUMB-OCCUR-IN-TYPE-ALIST DUMB-OCCUR-LST
             DUMB-OCCUR FORCE-ASSUMPTION1
             REMOVE-TTREES-FROM-TYPE-ALIST
             CONTAINS-ASSUMPTIONP
             |Make FC-DERIVATION record|
             |Change FC-DERIVATION record fields|
             |Access FC-DERIVATION record field TTREE|
             |Access FC-DERIVATION record field INST-TRIGGER|
             |Access FC-DERIVATION record field FN-CNT|
             |Access FC-DERIVATION record field CONCL|
             |Access FC-DERIVATION record field RUNE|
             |Make ASSUMNOTE record|
             |Change ASSUMNOTE record fields|
             |Access ASSUMNOTE record field TARGET|
             |Access ASSUMNOTE record field RUNE|
             |Access ASSUMNOTE record field CL-ID|
             |Make ASSUMPTION record|
             |Change ASSUMPTION record fields|
             |Access ASSUMPTION record field ASSUMNOTES|
             |Access ASSUMPTION record field REWRITTENP|
             |Access ASSUMPTION record field IMMEDIATEP|
             |Access ASSUMPTION record field TERM|
             |Access ASSUMPTION record field TYPE-ALIST|
             RECOMPRESS-GLOBAL-ENABLED-STRUCTURE
             INITIAL-GLOBAL-ENABLED-STRUCTURE
             LOAD-THEORY-INTO-ENABLED-STRUCTURE
             ENABLED-FNP ENABLED-RUNEP ENABLED-NUMEP
             |Make ENABLED-STRUCTURE record|
             |Change ENABLED-STRUCTURE record fields|
             |Access ENABLED-STRUCTURE record field ARRAY-NAME-SUFFIX|
             |Access ENABLED-STRUCTURE record field ARRAY-NAME-ROOT|
             |Access ENABLED-STRUCTURE record field ARRAY-LENGTH|
             |Access ENABLED-STRUCTURE record field ARRAY-NAME|
             |Access ENABLED-STRUCTURE record field THEORY-ARRAY|
             |Access ENABLED-STRUCTURE record field INDEX-OF-LAST-ENABLING|
             RUNIC-THEORY
             AUGMENT-THEORY DUPLICITOUS-SORT-CAR
             DUPLICITOUS-MERGE-CAR
             DUPLICITOUS-REVAPPEND-CAR
             DUPLICITOUS-CONS-CAR
             CONVERT-THEORY-TO-UNORDERED-MAPPING-PAIRS
             CONVERT-THEORY-TO-UNORDERED-MAPPING-PAIRS1
             AUGMENT-RUNIC-THEORY
             AUGMENT-RUNIC-THEORY1
             FIND-MAPPING-PAIRS-TAIL
             FIND-MAPPING-PAIRS-TAIL1
             RUNIC-THEORYP RUNIC-THEORYP1
             THEORYP! THEORYP!1 THEORYP THEORYP1
             RULE-NAME-DESIGNATORP DEREF-MACRO-NAME
             GET-NEXT-NUME DEFINITION-RUNES
             FN-RUNE-NUME FRUNIC-MAPPING-PAIR
             FNUME STRIP-BASE-SYMBOLS
             BASE-SYMBOL RUNEP ASSOC-EQUAL-CDR
             ACCUMULATE-TTREE-INTO-STATE
             MOVE-UNMARKED-SUBBTREES TAGGED-OBJECT
             TAGGED-OBJECTS *TAG-TREE-T-ERROR-MSG*
             ADD-TO-SET-EQ-IN-ALIST
             ADD-TO-SET-EQUAL-IN-ALIST
             CONS-TAG-TREES PUSH-LEMMAS PUSH-LEMMA
             *FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE*
             ADD-TO-TAG-TREE
             TAG-TREE-OCCUR *TYPE-SET-<-TABLE*
             *TYPE-SET-BINARY-*-TABLE*
             *TYPE-SET-BINARY-+-TABLE*
             *NUMBER-OF-NUMERIC-TYPE-SET-BITS*
             TYPE-SET-<-ALIST
             TYPE-SET-<-ALIST1 TYPE-SET-<-ALIST-ENTRY
             TYPE-SET-BINARY-*-ALIST
             TYPE-SET-BINARY-*-ALIST1
             TYPE-SET-BINARY-*-ALIST-ENTRY
             TYPE-SET-BINARY-+-ALIST
             TYPE-SET-BINARY-+-ALIST1
             TYPE-SET-BINARY-+-ALIST-ENTRY
             TS-SUBSETP TS-UNION TS-INTERSECTION
             TS-COMPLEMENT EVAL-TYPE-SET-LST
             EVAL-TYPE-SET TS-INTERSECTION-FN
             TS-UNION-FN TS-COMPLEMENT-FN LOGAND-LST
             LOGIOR-LST *CODE-TYPE-SET-ALIST*
             ONE-BIT-TYPE-SETP *TS-UNKNOWN*
             *TS-EMPTY* *TS-TRUE-LIST-OR-STRING*
             *TS-SYMBOL* *TS-NON-NIL*
             *TS-TRUE-LIST* *TS-BOOLEAN* *TS-CONS*
             *TS-RATIO* *TS-NON-NEGATIVE-RATIONAL*
             *TS-NON-POSITIVE-RATIONAL*
             *TS-POSITIVE-RATIONAL*
             *TS-NEGATIVE-RATIONAL*
             *TS-ACL2-NUMBER* *TS-RATIONAL*
             *TS-INTEGER* *TS-NON-POSITIVE-INTEGER*
             *TS-NON-NEGATIVE-INTEGER*
             *TS-CHARACTER* *TS-STRING*
             *TS-IMPROPER-CONS* *TS-PROPER-CONS*
             *TS-NON-T-NON-NIL-SYMBOL*
             *TS-T* *TS-NIL*))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*18 NIL
           ''(*TS-COMPLEX-RATIONAL* *TS-NEGATIVE-RATIO*
                                    *TS-NEGATIVE-INTEGER*
                                    *TS-POSITIVE-RATIO*
                                    *TS-POSITIVE-INTEGER*
                                    *TS-ZERO* THE-TYPE-SET
                                    *MAX-TYPE-SET* *MIN-TYPE-SET*
                                    *ACTUAL-PRIMITIVE-TYPES* THEREIS ALWAYS
                                    MAPDO MAPCAR$ TILDE-*-ALIST-PHRASE
                                    TILDE-*-ALIST-PHRASE1
                                    SIMPLE-TRANSLATE-AND-EVAL
                                    SUBSETP-EQ TRANS-EVAL PUT-ASSOC-EQ-ALIST
                                    USER-STOBJSP NON-STOBJPS
                                    REPLACE-STOBJS REPLACE-STOBJS1
                                    REPLACED-STOBJ TRANSLATE ALL-FNNAMES-LST
                                    ALL-FNNAMES COLLECT-PROGRAMS
                                    TRANSLATE1 TRANSLATE11-LST
                                    TRANSLATE11 PRETTYIFY-STOBJS-OUT
                                    UNPRETTYIFY-STOBJ-FLAGS
                                    PRETTYIFY-STOBJ-FLAGS COMPUTE-INCLP-LST
                                    COMPUTE-INCLP-LST1 ALL-NILS
                                    COLLECT-NON-X COMPUTE-STOBJ-FLAGS
                                    TRANSLATE11-ERROR HIDE-IGNORED-ACTUALS
                                    TRANS-ER-LET* TRANS-VALUE TRANS-ER
                                    FIND-FIRST-BAD-ARG FIND-PKG-WITNESS
                                    FIND-FIRST-FNSYMB-LST FIND-FIRST-FNSYMB
                                    FIND-FIRST-VAR-LST FIND-FIRST-VAR
                                    GENVAR GENVAR1 LEGAL-INTERN-PACKAGE
                                    LISTLIS PACK2 PACKN-POS PACKN
                                    PACKN1 TRANSLATE-UNBOUND TRANSLATE-DEREF
                                    TRANSLATE-BIND MV-NTH-LIST IGNORE-VARS
                                    DCL-GUARDIAN TRANSLATE-DCL-LST
                                    TRANSLATE-DECLARATION-TO-GUARD-VAR-LST
                                    LISTIFY COLLECT-DECLARATIONS GET-STRING
                                    REMOVE-STRINGS NUMBER-OF-STRINGS
                                    CHK-DCL-LST OPTIMIZE-ALISTP
                                    COLLECT-NON-LEGAL-VARIABLEPS
                                    DUPLICATES TILDE-*-CONJUNCTION-PHRASE
                                    TILDE-*-CONJUNCTION-PHRASE1
                                    *DCL-EXPLANATION-ALIST*
                                    *DOCUMENTATION-STRINGS-PERMITTED*
                                    *ACCEPTABLE-DCLS-ALIST*
                                    COLLECT-DCLS CHK-DECLARE
                                    MACROEXPAND1 EV-ACL2-UNWIND-PROTECT
                                    EV-LST EV EV-FNCALL
                                    STOBJP TRANSLATED-ACL2-UNWIND-PROTECTP
                                    TRANSLATED-ACL2-UNWIND-PROTECTP4
                                    LATCH-STOBJS LATCH-STOBJS1 EV-FNCALL-MSG
                                    FIND-FIRST-NON-NIL EV-FNCALL-GUARD-ER
                                    EV-FNCALL-NULL-BODY-ER
                                    BIND-MACRO-ARGS BIND-MACRO-ARGS1
                                    BIND-MACRO-ARGS-OPTIONAL
                                    BIND-MACRO-ARGS-AFTER-REST
                                    BIND-MACRO-ARGS-KEYS
                                    BIND-MACRO-ARGS-KEYS1
                                    REMOVE-KEYWORD CHK-LENGTH-AND-KEYS
                                    *MACRO-EXPANSION-CTX*
                                    MACRO-ARGS KWOTE-LST TERM-LISTP
                                    TERMP NQTHM-TO-ACL2 NQTHM-TO-ACL2-FN
                                    *NQTHM-TO-ACL2-COMMANDS*
                                    *NQTHM-TO-ACL2-PRIMITIVES*
                                    SET-LD-VERBOSE CHK-LD-VERBOSE
                                    LD-VERBOSE SET-LD-QUERY-CONTROL-ALIST
                                    CHK-LD-QUERY-CONTROL-ALIST
                                    CDR-ASSOC-QUERY-ID
                                    LD-QUERY-CONTROL-ALISTP
                                    LD-QUERY-CONTROL-ALIST
                                    SET-LD-ERROR-ACTION CHK-LD-ERROR-ACTION
                                    LD-ERROR-ACTION SET-LD-ERROR-TRIPLES
                                    CHK-LD-ERROR-TRIPLES LD-ERROR-TRIPLES
                                    SET-LD-EVISC-TUPLE CHK-LD-EVISC-TUPLE
                                    LD-EVISC-TUPLE SET-LD-POST-EVAL-PRINT
                                    CHK-LD-POST-EVAL-PRINT
                                    LD-POST-EVAL-PRINT SET-LD-PRE-EVAL-PRINT
                                    CHK-LD-PRE-EVAL-PRINT
                                    LD-PRE-EVAL-PRINT SET-LD-PRE-EVAL-FILTER
                                    CHK-LD-PRE-EVAL-FILTER
                                    NEW-NAMEP LD-PRE-EVAL-FILTER
                                    SET-LD-KEYWORD-ALIASES
                                    CHK-LD-KEYWORD-ALIASES
                                    LD-KEYWORD-ALIASESP LD-KEYWORD-ALIASES
                                    SET-LD-PROMPT CHK-LD-PROMPT
                                    LD-PROMPT SET-PROOFS-CO CHK-PROOFS-CO))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*19 NIL
           ''(PROOFS-CO SET-STANDARD-CO
                        CHK-STANDARD-CO STANDARD-CO
                        SET-STANDARD-OI CHK-STANDARD-OI
                        READ-STANDARD-OI STANDARD-OI
                        SET-CURRENT-PACKAGE CHK-CURRENT-PACKAGE
                        REDEF! REDEF SET-LD-REDEFINITION-ACTION
                        CHK-LD-REDEFINITION-ACTION
                        LD-REDEFINITION-ACTION
                        SET-LD-SKIP-PROOFSP CHK-LD-SKIP-PROOFSP
                        *LD-SPECIAL-ERROR* UNTRANSLATE-LST
                        UNTRANSLATE-INTO-COND-CLAUSES
                        UNTRANSLATE-INTO-CASE-CLAUSES
                        UNTRANSLATE-IF UNTRANSLATE-CONS
                        UNTRANSLATE-CONS1 UNTRANSLATE
                        DUMB-NEGATE-LIT RIGHT-ASSOCIATED-ARGS
                        *UNTRANSLATE-BOOLEAN-PRIMITIVES*
                        COND-LENGTH CASE-LENGTH
                        UNTRANSLATE-OR UNTRANSLATE-AND
                        COLLECT-NON-TRIVIAL-BINDINGS
                        CAR-CDR-NEST CAR-CDR-NEST1
                        CONS-COUNT CONS-COUNT-AC CONJOIN
                        CONJOIN2 SUBCOR-VAR-LST SUBCOR-VAR
                        SUBCOR-VAR1 SUBLIS-VAR-LST SUBLIS-VAR
                        ARGLISTP ARGLISTP1 NO-LAMBDA-KEYWORDSP
                        LAMBDA-KEYWORDP CONS-TERM
                        QUOTE-LISTP CONS-TERM1 GLOBAL-SET-LST
                        DOUBLETON-LIST-P LEGAL-VARIABLEP
                        DEFINED-CONSTANT LEGAL-CONSTANTP
                        TILDE-@-ILLEGAL-VARIABLE-OR-CONSTANT-NAME-PHRASE
                        LEGAL-CONSTANTP1
                        LEGAL-VARIABLE-OR-CONSTANT-NAMEP
                        STRIP-CADRS
                        ALL->=-LEN >=-LEN EQUIVALENCE-RELATIONP
                        GUARD-LST GUARD DEFUN-MODE
                        LOGIC-TERM-LIST-LISTP LOGIC-TERM-LISTP LOGIC-TERMP
                        LOGIC-FNS-LIST-LISTP LOGIC-FNS-LISTP LOGIC-FNSP
                        LOGICP PROGRAMP FDEFUN-MODE
                        SYMBOL-CLASS BODY STOBJS-OUT STOBJS-IN
                        ARITY FORMALS READ-FILE
                        READ-FILE-ITERATE GET-CHECK-SUMS-LST
                        CHECK-SUM-OBJ
                        CHECK-SUM-OBJ1 CHECK-SUM-STRING
                        CHECK-SUM-STRING2 CHECK-SUM-STRING1
                        CHECK-SUM-NATURAL CHECK-SUM-INC
                        CHECK-SUM CHECK-SUM1 ASCII-CODE!
                        *1-CHECK-LENGTH-EXCLUSIVE-MAXIMUM*
                        *-CHECK-SUM-EXCLUSIVE-MAXIMUM*
                        *CHECK-LENGTH-EXCLUSIVE-MAXIMUM*
                        *CHECK-SUM-EXCLUSIVE-MAXIMUM*
                        OBSERVATION OBSERVATION1
                        WARNING$ WARNING1 ERROR1 IO? DELETE1-EQ
                        IO?-NIL-OUTPUT *WINDOW-DESCRIPTIONS*
                        PRINT-CURRENT-IDATE
                        PRINT-IDATE PCD2 DECODE-IDATE
                        POWER-REP INTERSECTION-EQ CONSITYP
                        EQUALITYP SET-DIFFERENCE-EQ DEFREC
                        RECORD-MACROS MAKE-RECORD-FIELD-LST
                        MAKE-RECORD-MAKER MAKE-RECORD-MAKER-LET
                        MAKE-RECORD-MAKER-CONS
                        MAKE-RECORD-CHANGER
                        MAKE-RECORD-CHANGER-LET
                        MAKE-RECORD-CHANGER-LET-BINDINGS
                        MAKE-RECORD-CHANGER-CONS
                        SOME-SYMBOL-NAME-TREE-OCCUR
                        SYMBOL-NAME-TREE-OCCUR
                        MAKE-RECORD-ACCESSORS
                        MAKE-RECORD-CAR-CDRS
                        MAKE-RECORD-CAR-CDRS1
                        RECORD-ERROR CHANGE ACCESS MAKE
                        ODDS EVENS RECORD-CHANGER-FUNCTION-NAME
                        RECORD-ACCESSOR-FUNCTION-NAME
                        RECORD-MAKER-FUNCTION-NAME
                        STRIP-NOT *-1* *1* *0* *NIL*
                        *TRUE-CLAUSE* *T* STD STANDARD-GUARD-LST
                        STANDARD-GUARD QUOTEP))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*20 NIL
           ''(TS-BUILDER TS-BUILDER-MACRO TS-BUILDER-MACRO1
                         TS-BUILDER-CASE-LISTP TS-SUBSETP0
                         TS-INTERSECTP TS-INTERSECTION0
                         TS-UNION0 TS-UNION0-FN TS-COMPLEMENTP
                         TS-COMPLEMENT0 TS= LIST-OF-THE-TYPE-SET
                         DEF-BASIC-TYPE-SETS DEF-BASIC-TYPE-SETS1
                         *PRIMITIVE-FORMALS-AND-GUARDS* MATCH!
                         MATCH ER-LET* VALUE MAKE-LET MAKE-LAMBDA
                         LAMBDA-BODY LAMBDA-FORMALS FLAMBDAP
                         LAMBDA-APPLICATIONP FLAMBDA-APPLICATIONP
                         CW PAIRLIS2 FMT-TO-COMMENT-WINDOW
                         MEMBER-STRING-EQUAL
                         PUSH-WARNING POP-WARNING-FRAME
                         PUSH-WARNING-FRAME ADD-TO-SET-EQUAL
                         ERROR-FMS FMT-IN-CTX FMT-CTX
                         *FMT-CTX-SPACERS* FMT-DOC-EXAMPLE
                         FMT-DOC-EXAMPLE1 FMX FMS FMT FMT1
                         TILDE-*-&V-STRINGS FMT0 FMT-SYMBOL-NAME
                         SPELL-NUMBER FMT0&V FMT0* FMT-PPR
                         TERM-EVISC-TUPLE DEFAULT-EVISC-TUPLE
                         STANDARD-EVISC-TUPLEP EVISC-TUPLE
                         MAYBE-NEWLINE LEFT-PAD-WITH-BLANKS
                         NUMBER-OF-DIGITS SPLAT1 SPLAT
                         SPLAT-ATOM FMT-VAR FMT-SYMBOL-NAME1
                         PUNCTP FIND-ALTERNATIVE-STOP
                         FIND-ALTERNATIVE-START
                         FMT-CHAR FIND-ALTERNATIVE-START1
                         FIND-ALTERNATIVE-SKIP
                         ZERO-ONE-OR-MORE SCAN-PAST-WHITESPACE
                         PPR *FMT-PPR-INDENTATION* PPR2
                         PPR2-COLUMN PPR2-FLAT FLPR FLPR11 FLPR1
                         SPACES SPACES1 SET-FMT-SOFT-RIGHT-MARGIN
                         SET-FMT-HARD-RIGHT-MARGIN
                         FMT-SOFT-RIGHT-MARGIN
                         FMT-HARD-RIGHT-MARGIN
                         NEWLINE PPR1-LST PPR1 MAX-WIDTH
                         FLSZ OUTPUT-IN-INFIXP FLSZ1 FLSZ-ATOM
                         CONS-PPR1 CHARF |1+F| |1-F| |-F| |+F|
                         THE-STRING! THE-HALF-FIXNUM! THE-FIXNUM!
                         FIXNUM-BOUND THE-FIXNUM MV-LETC
                         ER EVISCERATE-STOBJS EVISCERATE-STOBJS1
                         EVISCERATION-STOBJ-MARKS
                         EVISCERATION-STOBJ-MARKS1
                         EVISCERATION-STOBJ-MARK
                         WORLD-EVISCERATION-ALIST
                         EVISCERATE EVISCERATE1P-LST
                         EVISCERATE1P EVISCERATE1-LST
                         EVISCERATE1 *ANTI-EVISCERATION-MARK*
                         *EVISCERATION-HIDING-MARK*
                         *EVISCERATION-ERROR-TRIPLE-MARKS*
                         *EVISCERATION-STATE-MARK*
                         *EVISCERATION-WORLD-MARK*
                         *EVISCERATION-ELLIPSIS-MARK*
                         *EVISCERATION-HASH-MARK*
                         *EVISCERATION-MARK*
                         CASE-MATCH MATCH-CLAUSE-LIST
                         MATCH-CLAUSE MATCH-TESTS-AND-BINDINGS
                         EQUAL-X-CONSTANT
                         ALL-BUT-LAST CDR-NEST FARGN
                         FARGN1 FCONS-TERM FCONS-TERM* NVARIABLEP
                         DEFABBREV DEFABBREV1 KWOTE GLOBAL-SET
                         ASSIGN-WORMHOLE-OUTPUT WORMHOLE ABORT!
                         WORMHOLE1 BOOLEAN-LISTP FIX-TRUE-LIST
                         REMOVE-MACRO-ALIAS ADD-MACRO-ALIAS))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*21 NIL
           ''(MACRO-ALIASES SET-STATE-OK SET-INHIBIT-OUTPUT-LST
                            SET-INHIBIT-WARNINGS
                            SET-IGNORE-OK SET-IRRELEVANT-FORMALS-OK
                            SET-INVISIBLE-FNS-ALIST
                            INVISIBLE-FNS-ALIST PROGRAM LOGIC
                            DEFAULT-DEFUN-MODE GOOD-DEFUN-MODE-P
                            SET-WELL-FOUNDED-RELATION
                            DEFAULT-WELL-FOUNDED-RELATION
                            SET-MEASURE-FUNCTION
                            DEFAULT-MEASURE-FUNCTION
                            SET-COMPILE-FNS DEFAULT-COMPILE-FNS
                            SET-VERIFY-GUARDS-EAGERNESS
                            DEFAULT-VERIFY-GUARDS-EAGERNESS
                            TABLE-ALIST INVISIBLE-FNS-ALISTP
                            UNARY-FUNCTION-SYMBOL-LISTP THE2S THE-MV
                            SUBST-FOR-NTH-ARG INT= MAKE-VAR-LST
                            MAKE-VAR-LST1 @ ASSIGN UNION-EQ
                            *ACL2-EXPORTS* *INITIAL-UNTOUCHABLES*
                            SET-W CURRENT-PACKAGE W PRIN1$
                            PRINT-TIMER PRINT-RATIONAL-AS-DECIMAL
                            INCREMENT-TIMER ADD-TIMERS
                            POP-TIMER PUSH-TIMER GET-TIMER
                            SET-TIMER PUT-ASSOC-EQUAL PUT-ASSOC-EQ
                            MAIN-TIMER READ-RUN-TIME READ-IDATE
                            POWER-EVAL UPDATE-USER-STOBJ-ALIST
                            USER-STOBJ-ALIST LIST-ALL-PACKAGE-NAMES
                            DECREMENT-BIG-CLOCK BIG-CLOCK-NEGATIVE-P
                            F-DECREMENT-BIG-CLOCK
                            F-BIG-CLOCK-NEGATIVE-P
                            ASET-32-BIT-INTEGER-STACK
                            AREF-32-BIT-INTEGER-STACK
                            SHRINK-32-BIT-INTEGER-STACK
                            EXTEND-32-BIT-INTEGER-STACK
                            |32-BIT-INTEGER-STACK-LENGTH|
                            |32-BIT-INTEGER-STACK-LENGTH1|
                            ASET-T-STACK
                            AREF-T-STACK SHRINK-T-STACK SUBSEQ-LIST
                            TAKE FIRST-N-AC EXTEND-T-STACK
                            MAKE-LIST-AC T-STACK-LENGTH
                            T-STACK-LENGTH1 MAY-NEED-SLASHES
                            PRIN1-WITH-SLASHES PRIN1-WITH-SLASHES1
                            SOME-SLASHABLE *SLASHABLE-CHARS*
                            *SUSPICIOUSLY-FIRST-NUMERIC-CHARS*
                            READ-OBJECT
                            READ-BYTE$ PEEK-CHAR$ READ-CHAR$
                            CLOSE-OUTPUT-CHANNEL OPEN-OUTPUT-CHANNEL
                            CLOSE-INPUT-CHANNEL OPEN-INPUT-CHANNEL
                            MAKE-OUTPUT-CHANNEL MAKE-INPUT-CHANNEL
                            PRINT-OBJECT$ WRITE-BYTE$
                            PRINC$ OPEN-INPUT-CHANNEL-ANY-P
                            OPEN-INPUT-CHANNEL-ANY-P1
                            OPEN-OUTPUT-CHANNEL-ANY-P
                            OPEN-OUTPUT-CHANNEL-ANY-P1
                            OPEN-OUTPUT-CHANNEL-P
                            OPEN-INPUT-CHANNEL-P
                            OPEN-OUTPUT-CHANNEL-P1
                            OPEN-INPUT-CHANNEL-P1
                            EXPLODE-ATOM EXPLODE-NONNEGATIVE-INTEGER
                            DIGIT-TO-CHAR STATE-GLOBAL-LET*
                            STATE-GLOBAL-LET*-CLEANUP
                            STATE-GLOBAL-LET*-PUT-GLOBALS
                            STATE-GLOBAL-LET*-GET-GLOBALS
                            SYMBOL-DOUBLET-LISTP
                            F-PUT-GLOBAL PUT-GLOBAL F-GET-GLOBAL
                            GET-GLOBAL MAKUNBOUND-GLOBAL
                            DELETE-PAIR F-BOUNDP-GLOBAL
                            BOUNDP-GLOBAL BOUNDP-GLOBAL1
                            GLOBAL-TABLE-CARS GLOBAL-TABLE-CARS1
                            COERCE-OBJECT-TO-STATE
                            COERCE-STATE-TO-OBJECT
                            BUILD-STATE1 *DEFAULT-STATE*
                            BUILD-STATE STATE-P STATE-P1
                            WRITEABLE-FILES-P WRITABLE-FILE-LISTP
                            WRITABLE-FILE-LISTP1 READ-FILES-P
                            READ-FILE-LISTP READ-FILE-LISTP1
                            WRITTEN-FILES-P WRITTEN-FILE-LISTP
                            WRITTEN-FILE READABLE-FILES-P
                            READABLE-FILES-LISTP READABLE-FILE
                            FILE-CLOCK-P OPEN-CHANNELS-P
                            OPEN-CHANNEL-LISTP OPEN-CHANNEL1
                            *FILE-TYPES* TYPED-IO-LISTP
                            TIMER-ALISTP KNOWN-PACKAGE-ALISTP
                            ALL-BOUNDP *INITIAL-GLOBAL-TABLE*))
 (DEFMACRO
      SYMBOLS::*ACL2-SYMBOLS*22 NIL
      ''(UPDATE-USER-STOBJ-ALIST1 USER-STOBJ-ALIST1
                                  UPDATE-LIST-ALL-PACKAGE-NAMES-LST
                                  LIST-ALL-PACKAGE-NAMES-LST
                                  WRITEABLE-FILES
                                  UPDATE-READ-FILES READ-FILES
                                  UPDATE-WRITTEN-FILES WRITTEN-FILES
                                  READABLE-FILES UPDATE-FILE-CLOCK
                                  FILE-CLOCK UPDATE-RUN-TIMES
                                  RUN-TIMES UPDATE-IDATES IDATES
                                  UPDATE-BIG-CLOCK-ENTRY BIG-CLOCK-ENTRY
                                  UPDATE-32-BIT-INTEGER-STACK
                                  |32-BIT-INTEGER-STACK| UPDATE-T-STACK
                                  T-STACK UPDATE-GLOBAL-TABLE
                                  GLOBAL-TABLE UPDATE-OPEN-OUTPUT-CHANNELS
                                  OPEN-OUTPUT-CHANNELS
                                  UPDATE-OPEN-INPUT-CHANNELS
                                  OPEN-INPUT-CHANNELS
                                  |32-BIT-INTEGER-LISTP|
                                  INTEGER-LISTP RATIONAL-LISTP
                                  |32-BIT-INTEGERP| UPDATE-NTH UPDATE-NTH-ARRAY
                                  MV-LET MV MAKE-MV-NTHS MV-NTH CDRN ASET2
                                  COMPRESS2 COMPRESS21 COMPRESS211 AREF2
                                  ASET1 COMPRESS1 COMPRESS11 AREF1 DEFAULT
                                  MAXIMUM-LENGTH DIMENSIONS HEADER ARRAY2P
                                  ASSOC2 BOUNDED-INTEGER-ALISTP2 ARRAY1P
                                  ASSOC-KEYWORD KEYWORD-VALUE-LISTP
                                  BOUNDED-INTEGER-ALISTP
                                  *MAXIMUM-POSITIVE-32-BIT-INTEGER*
                                  SET-DIFFERENCE-EQUAL
                                  FUNCTION-SYMBOLP GLOBAL-VAL
                                  RETRACT-WORLD EXTEND-WORLD HAS-PROPSP
                                  HAS-PROPSP1 GETPROPS GETPROPS1
                                  TRUE-LIST-LISTP REMOVE-FIRST-PAIR
                                  ADD-PAIR ORDERED-SYMBOL-ALISTP
                                  GETPROP SGETPROP FGETPROP
                                  GETPROP-DEFAULT *ACL2-PROPERTY-UNBOUND*
                                  PUTPROP WORLDP SKIP-PROOFS
                                  WHEN-LOGIC ACL2-UNWIND-PROTECT PPROGN
                                  SYMBOL-< STRING<-L THE-FN THE-ERROR
                                  TRANSLATE-DECLARATION-TO-GUARD-LST
                                  TRANSLATE-DECLARATION-TO-GUARD
                                  TRANSLATE-DECLARATION-TO-GUARD1
                                  TRANSLATE-DECLARATION-TO-GUARD/INTEGER
                                  LIST*-MACRO NONNEGATIVE-INTEGER-QUOTIENT
                                  POSITION-AC POSITION-EQ
                                  POSITION-EQ-AC POSITION-EQUAL
                                  POSITION-EQUAL-AC CASE-LIST-CHECK
                                  CASE-LIST CASE-TEST LEGAL-CASE-CLAUSESP
                                  ER-PROGN ER-PROGN-FN CHECK-VARS-NOT-FREE
                                  MSG MAKE-FMT-BINDINGS INTERSECTP-EQUAL
                                  INTERSECTP-EQ TRANSLATE-AND-TEST
                                  ALL-VARS ALL-VARS1-LST ALL-VARS1 FARGS
                                  FFN-SYMB FQUOTEP VARIABLEP ADD-TO-SET-EQ
                                  PSEUDO-TERM-LISTP PSEUDO-TERMP
                                  MUTUAL-RECURSION MUTUAL-RECURSION-GUARDP
                                  STRIP-CDRS REMOVE-DUPLICATES-EQUAL
                                  REMOVE-DUPLICATES-EQL
                                  PAIRLIS$ STRING-APPEND-LST
                                  STRING-LISTP STRING-APPEND
                                  BINARY-APPEND MEMBER-SYMBOL-NAME ILLEGAL
                                  HARD-ERROR *INITIAL-KNOWN-PACKAGE-ALIST*
                                  *MAIN-LISP-PACKAGE-NAME*
                                  ASSOC-STRING-EQUAL STRING-ALISTP
                                  STRING-EQUAL1 NFIX RFIX IFIX ATOM-LISTP
                                  OUR-DIGIT-CHAR-P STRING-UPCASE1
                                  STRING-DOWNCASE1 CHARACTER-LISTP
                                  STANDARD-CHAR-LISTP *STANDARD-CHARS*
                                  R-EQLABLE-ALISTP NO-DUPLICATESP))
 (DEFMACRO SYMBOLS::*ACL2-SYMBOLS*23 NIL
           ''(SYNTAXP ENABLE-FORCING DISABLE-FORCING
                      CASE-SPLIT *IMMEDIATE-FORCE-MODEP-XNUME*
                      IMMEDIATE-FORCE-MODEP *FORCE-XNUME*
                      FORCE FIX PROG2$ IMPROPER-CONSP
                      PROPER-CONSP ZIP ZP STRIP-CARS
                      NO-DUPLICATESP-EQUAL ASSOC-EQ-EQUAL
                      ASSOC-EQ-EQUAL-ALISTP ASSOC-EQUAL
                      ASSOC-EQ SYMBOL-ALISTP MEMBER-EQ
                      SYMBOL-LISTP SUBSETP-EQUAL UNION-EQUAL
                      MEMBER-EQUAL ALISTP EQLABLE-ALISTP
                      MAKE-CHARACTER-LIST EQLABLE-LISTP
                      EQLABLEP COND-MACRO COND-CLAUSESP
                      ACL2-COUNT LEN XXXJOIN INTEGER-ABS
                      OR-MACRO AND-MACRO LIST-MACRO TRUE-LISTP
                      HIDE IMPLIES BOOLEANP IFF *STANDARD-CI*
                      *STANDARD-OI* *STANDARD-CO*
                      *COMMON-LISP-SPECIALS-AND-CONSTANTS*
                      *ACL2-FILES* *ACL2-VERSION*
                      *COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE*
                      E0-ORD-< E0-ORDINALP SYMBOL-PACKAGE-NAME
                      INTERN-IN-PACKAGE-OF-SYMBOL
                      COMPLEX-RATIONALP
                      UNARY-/ UNARY-- BINARY-+ BINARY-*
                      ACL2-NUMBERP LOCAL LD-SKIP-PROOFSP
                      DEFAULT-DEFUN-MODE-FROM-STATE
                      SKIP-WHEN-LOGIC
                      INCLUDE-BOOK INCLUDE-BOOK-FN ENCAPSULATE
                      ENCAPSULATE-FN TABLE TABLE-FN
                      PUSH-UNTOUCHABLE PUSH-UNTOUCHABLE-FN
                      IN-THEORY IN-THEORY-FN DEFTHEORY
                      DEFTHEORY-FN DEFDOC DEFDOC-FN DEFLABEL
                      DEFLABEL-FN DEFAXIOM DEFAXIOM-FN DEFTHM
                      DEFTHM-FN DEFSTOBJ DEFSTOBJ-FN DEFCONST
                      DEFCONST-FN DEFMACRO-FN VERIFY-GUARDS
                      VERIFY-GUARDS-FN VERIFY-TERMINATION
                      VERIFY-TERMINATION-FN DEFUNS DEFUNS-FN
                      DEFUN-FN DEFCHOOSE DEFCHOOSE-FN DEFPKG
                      DEFPKG-FN IN-PACKAGE-FN CURRENT-THEORY
                      REVERSED-STANDARD-THEORIES
                      SMALL-P KNOWN-PACKAGE-ALIST
		      ))
 (DEFCONST
  SYMBOLS::*ACL2-SYMBOLS*
  (APPEND
   (SYMBOLS::*ACL2-SYMBOLS*23)
   (APPEND
    (SYMBOLS::*ACL2-SYMBOLS*22)
    (APPEND
     (SYMBOLS::*ACL2-SYMBOLS*21)
     (APPEND
      (SYMBOLS::*ACL2-SYMBOLS*20)
      (APPEND
       (SYMBOLS::*ACL2-SYMBOLS*19)
       (APPEND
        (SYMBOLS::*ACL2-SYMBOLS*18)
        (APPEND
         (SYMBOLS::*ACL2-SYMBOLS*17)
         (APPEND
          (SYMBOLS::*ACL2-SYMBOLS*16)
          (APPEND
           (SYMBOLS::*ACL2-SYMBOLS*15)
           (APPEND
            (SYMBOLS::*ACL2-SYMBOLS*14)
            (APPEND
             (SYMBOLS::*ACL2-SYMBOLS*13)
             (APPEND
              (SYMBOLS::*ACL2-SYMBOLS*12)
              (APPEND
               (SYMBOLS::*ACL2-SYMBOLS*11)
               (APPEND
                (SYMBOLS::*ACL2-SYMBOLS*10)
                (APPEND
                 (SYMBOLS::*ACL2-SYMBOLS*9)
                 (APPEND
                  (SYMBOLS::*ACL2-SYMBOLS*8)
                  (APPEND
                   (SYMBOLS::*ACL2-SYMBOLS*7)
                   (APPEND
                    (SYMBOLS::*ACL2-SYMBOLS*6)
                    (APPEND
                     (SYMBOLS::*ACL2-SYMBOLS*5)
                     (APPEND
                      (SYMBOLS::*ACL2-SYMBOLS*4)
                      (APPEND
                        (SYMBOLS::*ACL2-SYMBOLS*3)
                        (APPEND (SYMBOLS::*ACL2-SYMBOLS*2)
                                (APPEND (SYMBOLS::*ACL2-SYMBOLS*1)
                                        (APPEND (SYMBOLS::*ACL2-SYMBOLS*0)
                                                NIL))))))))))))))))))))))))))

(defconst SYMBOLS::*lisp-symbols*
       `(BUTLAST SUBSEQ MAKE-LIST
         LOGTEST LOGNOR LOGXOR LOGEQV LOGANDC2
         LOGANDC1 LOGORC2 LOGORC1 LOGIOR LOGNAND
         LOGAND INTEGER-LENGTH SUBST SUBLIS
         SUBSETP REVERSE REVAPPEND STRING>=
         STRING<= STRING> STRING< CHAR>= CHAR<=
         CHAR> CHAR< THE LIST* ASH LOGBITP LAST
         NTHCDR LISTP LOGCOUNT EXPT LOGNOT SIGNUM
         ABS MAX MIN MINUSP PLUSP ZEROP ODDP
         EVENP REM MOD ROUND TRUNCATE CEILING
         FLOOR POSITION CASE PROGN IDENTITY REST
         TENTH NINTH EIGHTH SEVENTH SIXTH FIFTH
         FOURTH THIRD SECOND FIRST CDDDDR CDDDAR
         CDDADR CDDAAR CDADDR CDADAR CDAADR
         CDAAAR CADDDR CADDAR CADADR CADAAR
         CAADDR CAADAR CAAADR CAAAAR CDDDR CDDAR
         CDADR CDAAR CADDR CADAR CAADR CAAAR CDDR
         CDAR CADR CAAR REMOVE-DUPLICATES REMOVE
         1- 1+ CONCATENATE APPEND KEYWORDP INTERN
         STRING-EQUAL CHAR-EQUAL DIGIT-CHAR-P
         STRING-UPCASE STRING-DOWNCASE
         CHAR-DOWNCASE CHAR-UPCASE
         LOWER-CASE-P UPPER-CASE-P ALPHA-CHAR-P
         STRING STANDARD-CHAR-P RASSOC
         ASSOC MEMBER / CONJUGATE * NULL CHAR NTH
         >= > /= = <= EQL LET* ENDP ACONS ATOM
         COND LENGTH + - OR AND LIST EQ NOT T
         NIL SYMBOLP SYMBOL-NAME STRINGP REALPART
         RATIONALP NUMERATOR INTEGERP IMAGPART
         IF EQUAL DENOMINATOR CONSP CONS COERCE
         COMPLEX CODE-CHAR CHARACTERP CHAR-CODE
         CDR CAR < DEFMACRO DEFUN IN-PACKAGE))


(defconst SYMBOLS::*baseline-symbols*
  (union-eq *acl2-exports*
	    (union-eq *common-lisp-symbols-from-main-lisp-package*
		      (union-eq SYMBOLS::*acl2-symbols* SYMBOLS::*lisp-symbols*))))

(defconst SYMBOLS::*datastructure-symbols*
  `(SETP-EQUAL
    INTERSECTION-EQUAL
    MEMBERP-EQUAL
    SET-EQUAL
    ADJOIN-EQUAL
    ;;DEFSTRUCTURE
    G
    S
    t
    otherwise
    ))

;; (defun remove-list (list target)
;;   (declare (type (satisfies eqlable-listp) list target))
;;   (if (consp list)
;;       (remove-list (cdr list) (remove (car list) target))
;;     target))

(defconst SYMBOLS::*base-symbols*
  (set-difference-eq (union-eq SYMBOLS::*baseline-symbols* SYMBOLS::*datastructure-symbols*)
                     '(common-lisp::block acl2::pc)))

;; (defconst SYMBOLS::*base-symbols*
;;   (remove-list '(lisp::block acl2::pc)
;; 	       (union-eq SYMBOLS::*baseline-symbols* SYMBOLS::*datastructure-symbols*)))
