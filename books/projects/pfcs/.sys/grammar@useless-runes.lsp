(PFCS::UNTRANSLATE-PREPROCESS-*GRAMMAR*)
(PFCS::RULELIST-WFP-OF-*GRAMMAR*)
(PFCS::RULELIST-CLOSEDP-OF-*GRAMMAR*)
(PFCS::ASCII-ONLY-*GRAMMAR*)
(PFCS::CST-MATCHP$)
(PFCS::BOOLEANP-OF-CST-MATCHP$)
(PFCS::CST-MATCHP$-OF-TREE-FIX-TREE
 (12 1 (:REWRITE ABNF::TREE-FIX-WHEN-TREEP))
 (6 6 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (5 1 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (4 4 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (3 3 (:TYPE-PRESCRIPTION ABNF::TREEP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (2 1 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 )
(PFCS::CST-MATCHP$-TREE-EQUIV-CONGRUENCE-ON-TREE)
(PFCS::CST-MATCHP$-OF-ELEMENT-FIX-ELEM
 (4 4 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (4 4 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (3 1 (:REWRITE ABNF::ELEMENT-FIX-WHEN-ELEMENTP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::ELEMENTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 )
(PFCS::CST-MATCHP$-ELEMENT-EQUIV-CONGRUENCE-ON-ELEM)
(PFCS::CST-LIST-ELEM-MATCHP$)
(PFCS::BOOLEANP-OF-CST-LIST-ELEM-MATCHP$)
(PFCS::CST-LIST-ELEM-MATCHP$-OF-TREE-LIST-FIX-TREES
 (28 3 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (28 3 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (18 2 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-NOT-CONSP))
 (18 2 (:REWRITE ABNF::CONSP-OF-TREE-LIST-FIX))
 (16 1 (:REWRITE ABNF::TREE-LIST-FIX-WHEN-TREE-LISTP))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (9 1 (:REWRITE ABNF::TREE-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (6 6 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (4 4 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-LISTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::TREE-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 )
(PFCS::CST-LIST-ELEM-MATCHP$-TREE-LIST-EQUIV-CONGRUENCE-ON-TREES)
(PFCS::CST-LIST-ELEM-MATCHP$-OF-ELEMENT-FIX-ELEM
 (18 2 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (4 4 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (4 4 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (4 4 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (3 1 (:REWRITE ABNF::ELEMENT-FIX-WHEN-ELEMENTP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::ELEMENTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 )
(PFCS::CST-LIST-ELEM-MATCHP$-ELEMENT-EQUIV-CONGRUENCE-ON-ELEM)
(PFCS::CST-LIST-REP-MATCHP$)
(PFCS::BOOLEANP-OF-CST-LIST-REP-MATCHP$)
(PFCS::CST-LIST-REP-MATCHP$-OF-TREE-LIST-FIX-TREES
 (28 3 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (28 3 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (18 2 (:REWRITE ABNF::CONSP-OF-TREE-LIST-FIX))
 (16 1 (:REWRITE ABNF::TREE-LIST-FIX-WHEN-TREE-LISTP))
 (9 1 (:REWRITE ABNF::TREE-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (7 7 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (7 7 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (6 6 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-LISTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::TREE-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 )
(PFCS::CST-LIST-REP-MATCHP$-TREE-LIST-EQUIV-CONGRUENCE-ON-TREES)
(PFCS::CST-LIST-REP-MATCHP$-OF-REPETITION-FIX-REP
 (10 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (5 1 (:REWRITE ABNF::REPETITION-FIX-WHEN-REPETITIONP))
 (4 4 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::REPETITIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::REPETITIONP-WHEN-MEMBER-EQUAL-OF-CONCATENATIONP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (2 2 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 )
(PFCS::CST-LIST-REP-MATCHP$-REPETITION-EQUIV-CONGRUENCE-ON-REP)
(PFCS::CST-LIST-LIST-CONC-MATCHP$)
(PFCS::BOOLEANP-OF-CST-LIST-LIST-CONC-MATCHP$)
(PFCS::CST-LIST-LIST-CONC-MATCHP$-OF-TREE-LIST-LIST-FIX-TREESS
 (28 3 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (28 3 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (18 2 (:REWRITE ABNF::TREE-LIST-LIST-MATCH-CONCATENATION-P-WHEN-ATOM-CONCATENATION))
 (18 2 (:REWRITE ABNF::CONSP-OF-TREE-LIST-LIST-FIX))
 (14 1 (:REWRITE ABNF::TREE-LIST-LIST-FIX-WHEN-TREE-LIST-LISTP))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (9 1 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (6 6 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-LISTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 )
(PFCS::CST-LIST-LIST-CONC-MATCHP$-TREE-LIST-LIST-EQUIV-CONGRUENCE-ON-TREESS)
(PFCS::CST-LIST-LIST-CONC-MATCHP$-OF-CONCATENATION-FIX-CONC
 (18 2 (:REWRITE ABNF::TREE-LIST-LIST-MATCH-CONCATENATION-P-WHEN-ATOM-CONCATENATION))
 (16 1 (:REWRITE ABNF::CONCATENATION-FIX-WHEN-CONCATENATIONP))
 (10 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (9 1 (:REWRITE ABNF::CONCATENATIONP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (5 5 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (4 4 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ABNF::CONCATENATIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::CONCATENATIONP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::CONCATENATIONP-WHEN-MEMBER-EQUAL-OF-ALTERNATIONP))
 )
(PFCS::CST-LIST-LIST-CONC-MATCHP$-CONCATENATION-EQUIV-CONGRUENCE-ON-CONC)
(PFCS::CST-LIST-LIST-ALT-MATCHP$)
(PFCS::BOOLEANP-OF-CST-LIST-LIST-ALT-MATCHP$)
(PFCS::CST-LIST-LIST-ALT-MATCHP$-OF-TREE-LIST-LIST-FIX-TREESS
 (28 3 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (28 3 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (18 2 (:REWRITE ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-WHEN-ATOM-ALTERNATION))
 (18 2 (:REWRITE ABNF::CONSP-OF-TREE-LIST-LIST-FIX))
 (14 1 (:REWRITE ABNF::TREE-LIST-LIST-FIX-WHEN-TREE-LIST-LISTP))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (9 9 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (9 1 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (6 6 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-LISTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 )
(PFCS::CST-LIST-LIST-ALT-MATCHP$-TREE-LIST-LIST-EQUIV-CONGRUENCE-ON-TREESS)
(PFCS::CST-LIST-LIST-ALT-MATCHP$-OF-ALTERNATION-FIX-ALT
 (18 2 (:REWRITE ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-WHEN-ATOM-ALTERNATION))
 (14 1 (:REWRITE ABNF::ALTERNATION-FIX-WHEN-ALTERNATIONP))
 (10 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (10 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (9 1 (:REWRITE ABNF::ALTERNATIONP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (5 5 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (4 4 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION ABNF::ALTERNATIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE ABNF::ALTERNATIONP-WHEN-SUBSETP-EQUAL))
 )
(PFCS::CST-LIST-LIST-ALT-MATCHP$-ALTERNATION-EQUIV-CONGRUENCE-ON-ALT)
(PFCS::CST-LINE-FEED-NONLEAF)
(PFCS::CST-CARRIAGE-RETURN-NONLEAF)
(PFCS::CST-SPACE-NONLEAF)
(PFCS::CST-LINE-TERMINATOR-NONLEAF)
(PFCS::CST-WHITESPACE-NONLEAF)
(PFCS::CST-UPPERCASE-LETTER-NONLEAF)
(PFCS::CST-LOWERCASE-LETTER-NONLEAF)
(PFCS::CST-LETTER-NONLEAF)
(PFCS::CST-DIGIT-NONLEAF)
(PFCS::CST-NUMERAL-NONLEAF)
(PFCS::CST-INTEGER-NONLEAF)
(PFCS::CST-IDENTIFIER-NONLEAF)
(PFCS::CST-OPERATOR-NONLEAF)
(PFCS::CST-SEPARATOR-NONLEAF)
(PFCS::CST-TOKEN-NONLEAF)
(PFCS::CST-LEXEME-NONLEAF)
(PFCS::CST-PRIMARY-EXPRESSION-NONLEAF)
(PFCS::CST-MULTIPLICATION-EXPRESSION-NONLEAF)
(PFCS::CST-ADDITION-EXPRESSION-NONLEAF)
(PFCS::CST-EXPRESSION-NONLEAF)
(PFCS::CST-EQUALITY-CONSTRAINT-NONLEAF)
(PFCS::CST-RELATION-CONSTRAINT-NONLEAF)
(PFCS::CST-CONSTRAINT-NONLEAF)
(PFCS::CST-DEFINITION-NONLEAF)
(PFCS::CST-SYSTEM-NONLEAF)
(PFCS::CST-LINE-FEED-RULENAME)
(PFCS::CST-CARRIAGE-RETURN-RULENAME)
(PFCS::CST-SPACE-RULENAME)
(PFCS::CST-LINE-TERMINATOR-RULENAME)
(PFCS::CST-WHITESPACE-RULENAME)
(PFCS::CST-UPPERCASE-LETTER-RULENAME)
(PFCS::CST-LOWERCASE-LETTER-RULENAME)
(PFCS::CST-LETTER-RULENAME)
(PFCS::CST-DIGIT-RULENAME)
(PFCS::CST-NUMERAL-RULENAME)
(PFCS::CST-INTEGER-RULENAME)
(PFCS::CST-IDENTIFIER-RULENAME)
(PFCS::CST-OPERATOR-RULENAME)
(PFCS::CST-SEPARATOR-RULENAME)
(PFCS::CST-TOKEN-RULENAME)
(PFCS::CST-LEXEME-RULENAME)
(PFCS::CST-PRIMARY-EXPRESSION-RULENAME)
(PFCS::CST-MULTIPLICATION-EXPRESSION-RULENAME)
(PFCS::CST-ADDITION-EXPRESSION-RULENAME)
(PFCS::CST-EXPRESSION-RULENAME)
(PFCS::CST-EQUALITY-CONSTRAINT-RULENAME)
(PFCS::CST-RELATION-CONSTRAINT-RULENAME)
(PFCS::CST-CONSTRAINT-RULENAME)
(PFCS::CST-DEFINITION-RULENAME)
(PFCS::CST-SYSTEM-RULENAME)
(PFCS::CST-LINE-FEED-BRANCHES-MATCH-ALT)
(PFCS::CST-CARRIAGE-RETURN-BRANCHES-MATCH-ALT)
(PFCS::CST-SPACE-BRANCHES-MATCH-ALT)
(PFCS::CST-LINE-TERMINATOR-BRANCHES-MATCH-ALT)
(PFCS::CST-WHITESPACE-BRANCHES-MATCH-ALT)
(PFCS::CST-UPPERCASE-LETTER-BRANCHES-MATCH-ALT)
(PFCS::CST-LOWERCASE-LETTER-BRANCHES-MATCH-ALT)
(PFCS::CST-LETTER-BRANCHES-MATCH-ALT)
(PFCS::CST-DIGIT-BRANCHES-MATCH-ALT)
(PFCS::CST-NUMERAL-BRANCHES-MATCH-ALT)
(PFCS::CST-INTEGER-BRANCHES-MATCH-ALT)
(PFCS::CST-IDENTIFIER-BRANCHES-MATCH-ALT)
(PFCS::CST-OPERATOR-BRANCHES-MATCH-ALT)
(PFCS::CST-SEPARATOR-BRANCHES-MATCH-ALT)
(PFCS::CST-TOKEN-BRANCHES-MATCH-ALT)
(PFCS::CST-LEXEME-BRANCHES-MATCH-ALT)
(PFCS::CST-PRIMARY-EXPRESSION-BRANCHES-MATCH-ALT)
(PFCS::CST-MULTIPLICATION-EXPRESSION-BRANCHES-MATCH-ALT)
(PFCS::CST-ADDITION-EXPRESSION-BRANCHES-MATCH-ALT)
(PFCS::CST-EXPRESSION-BRANCHES-MATCH-ALT)
(PFCS::CST-EQUALITY-CONSTRAINT-BRANCHES-MATCH-ALT)
(PFCS::CST-RELATION-CONSTRAINT-BRANCHES-MATCH-ALT)
(PFCS::CST-CONSTRAINT-BRANCHES-MATCH-ALT)
(PFCS::CST-DEFINITION-BRANCHES-MATCH-ALT)
(PFCS::CST-SYSTEM-BRANCHES-MATCH-ALT)
(PFCS::CST-LINE-FEED-CONCS)
(PFCS::CST-CARRIAGE-RETURN-CONCS)
(PFCS::CST-SPACE-CONCS)
(PFCS::CST-LINE-TERMINATOR-CONCS)
(PFCS::CST-WHITESPACE-CONCS)
(PFCS::CST-UPPERCASE-LETTER-CONCS)
(PFCS::CST-LOWERCASE-LETTER-CONCS)
(PFCS::CST-LETTER-CONCS)
(PFCS::CST-DIGIT-CONCS)
(PFCS::CST-NUMERAL-CONCS)
(PFCS::CST-INTEGER-CONCS)
(PFCS::CST-IDENTIFIER-CONCS)
(PFCS::CST-OPERATOR-CONCS)
(PFCS::CST-SEPARATOR-CONCS)
(PFCS::CST-TOKEN-CONCS)
(PFCS::CST-LEXEME-CONCS)
(PFCS::CST-PRIMARY-EXPRESSION-CONCS)
(PFCS::CST-MULTIPLICATION-EXPRESSION-CONCS)
(PFCS::CST-ADDITION-EXPRESSION-CONCS)
(PFCS::CST-EXPRESSION-CONCS)
(PFCS::CST-EQUALITY-CONSTRAINT-CONCS)
(PFCS::CST-RELATION-CONSTRAINT-CONCS)
(PFCS::CST-CONSTRAINT-CONCS)
(PFCS::CST-DEFINITION-CONCS)
(PFCS::CST-SYSTEM-CONCS)
(PFCS::CST-LINE-FEED-CONC-MATCHING)
(PFCS::CST-CARRIAGE-RETURN-CONC-MATCHING)
(PFCS::CST-SPACE-CONC-MATCHING)
(PFCS::CST-WHITESPACE-CONC1-MATCHING)
(PFCS::CST-WHITESPACE-CONC2-MATCHING)
(PFCS::CST-UPPERCASE-LETTER-CONC-MATCHING)
(PFCS::CST-LOWERCASE-LETTER-CONC-MATCHING)
(PFCS::CST-LETTER-CONC1-MATCHING)
(PFCS::CST-LETTER-CONC2-MATCHING)
(PFCS::CST-DIGIT-CONC-MATCHING)
(PFCS::CST-NUMERAL-CONC-MATCHING)
(PFCS::CST-OPERATOR-CONC1-MATCHING)
(PFCS::CST-OPERATOR-CONC2-MATCHING)
(PFCS::CST-OPERATOR-CONC3-MATCHING)
(PFCS::CST-OPERATOR-CONC4-MATCHING)
(PFCS::CST-SEPARATOR-CONC1-MATCHING)
(PFCS::CST-SEPARATOR-CONC2-MATCHING)
(PFCS::CST-SEPARATOR-CONC3-MATCHING)
(PFCS::CST-SEPARATOR-CONC4-MATCHING)
(PFCS::CST-SEPARATOR-CONC5-MATCHING)
(PFCS::CST-TOKEN-CONC1-MATCHING)
(PFCS::CST-TOKEN-CONC2-MATCHING)
(PFCS::CST-TOKEN-CONC3-MATCHING)
(PFCS::CST-TOKEN-CONC4-MATCHING)
(PFCS::CST-LEXEME-CONC1-MATCHING)
(PFCS::CST-LEXEME-CONC2-MATCHING)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-MATCHING)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-MATCHING)
(PFCS::CST-MULTIPLICATION-EXPRESSION-CONC1-MATCHING)
(PFCS::CST-ADDITION-EXPRESSION-CONC1-MATCHING)
(PFCS::CST-EXPRESSION-CONC-MATCHING)
(PFCS::CST-CONSTRAINT-CONC1-MATCHING)
(PFCS::CST-CONSTRAINT-CONC2-MATCHING)
(PFCS::CST-LINE-FEED-CONC-REP-MATCHING)
(PFCS::CST-CARRIAGE-RETURN-CONC-REP-MATCHING)
(PFCS::CST-SPACE-CONC-REP-MATCHING)
(PFCS::CST-WHITESPACE-CONC1-REP-MATCHING)
(PFCS::CST-WHITESPACE-CONC2-REP-MATCHING)
(PFCS::CST-UPPERCASE-LETTER-CONC-REP-MATCHING)
(PFCS::CST-LOWERCASE-LETTER-CONC-REP-MATCHING)
(PFCS::CST-LETTER-CONC1-REP-MATCHING)
(PFCS::CST-LETTER-CONC2-REP-MATCHING)
(PFCS::CST-DIGIT-CONC-REP-MATCHING)
(PFCS::CST-OPERATOR-CONC1-REP-MATCHING)
(PFCS::CST-OPERATOR-CONC2-REP-MATCHING)
(PFCS::CST-OPERATOR-CONC3-REP-MATCHING)
(PFCS::CST-OPERATOR-CONC4-REP-MATCHING)
(PFCS::CST-SEPARATOR-CONC1-REP-MATCHING)
(PFCS::CST-SEPARATOR-CONC2-REP-MATCHING)
(PFCS::CST-SEPARATOR-CONC3-REP-MATCHING)
(PFCS::CST-SEPARATOR-CONC4-REP-MATCHING)
(PFCS::CST-SEPARATOR-CONC5-REP-MATCHING)
(PFCS::CST-TOKEN-CONC1-REP-MATCHING)
(PFCS::CST-TOKEN-CONC2-REP-MATCHING)
(PFCS::CST-TOKEN-CONC3-REP-MATCHING)
(PFCS::CST-TOKEN-CONC4-REP-MATCHING)
(PFCS::CST-LEXEME-CONC1-REP-MATCHING)
(PFCS::CST-LEXEME-CONC2-REP-MATCHING)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-MATCHING)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-MATCHING)
(PFCS::CST-MULTIPLICATION-EXPRESSION-CONC1-REP-MATCHING)
(PFCS::CST-ADDITION-EXPRESSION-CONC1-REP-MATCHING)
(PFCS::CST-EXPRESSION-CONC-REP-MATCHING)
(PFCS::CST-CONSTRAINT-CONC1-REP-MATCHING)
(PFCS::CST-CONSTRAINT-CONC2-REP-MATCHING)
(PFCS::CST-WHITESPACE-CONC-EQUIVS)
(PFCS::CST-LETTER-CONC-EQUIVS)
(PFCS::CST-TOKEN-CONC-EQUIVS)
(PFCS::CST-LEXEME-CONC-EQUIVS)
(PFCS::CST-PRIMARY-EXPRESSION-CONC-EQUIVS)
(PFCS::CST-CONSTRAINT-CONC-EQUIVS)
(PFCS::CST-WHITESPACE-CONC?)
(PFCS::POSP-OF-CST-WHITESPACE-CONC?)
(PFCS::CST-WHITESPACE-CONC?-POSSIBILITIES)
(PFCS::CST-WHITESPACE-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-WHITESPACE-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-WHITESPACE-CONC?-2-IFF-MATCH-CONC)
(PFCS::CST-LETTER-CONC?)
(PFCS::POSP-OF-CST-LETTER-CONC?)
(PFCS::CST-LETTER-CONC?-POSSIBILITIES)
(PFCS::CST-LETTER-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-LETTER-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-LETTER-CONC?-2-IFF-MATCH-CONC)
(PFCS::CST-TOKEN-CONC?)
(PFCS::POSP-OF-CST-TOKEN-CONC?)
(PFCS::CST-TOKEN-CONC?-POSSIBILITIES)
(PFCS::CST-TOKEN-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-TOKEN-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-TOKEN-CONC?-2-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-TOKEN-CONC?-3-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-TOKEN-CONC?-4-IFF-MATCH-CONC)
(PFCS::CST-LEXEME-CONC?)
(PFCS::POSP-OF-CST-LEXEME-CONC?)
(PFCS::CST-LEXEME-CONC?-POSSIBILITIES)
(PFCS::CST-LEXEME-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-LEXEME-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-LEXEME-CONC?-2-IFF-MATCH-CONC)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?)
(PFCS::POSP-OF-CST-PRIMARY-EXPRESSION-CONC?)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?-POSSIBILITIES)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-PRIMARY-EXPRESSION-CONC?-2-IFF-MATCH-CONC)
(PFCS::CST-CONSTRAINT-CONC?)
(PFCS::POSP-OF-CST-CONSTRAINT-CONC?)
(PFCS::CST-CONSTRAINT-CONC?-POSSIBILITIES)
(PFCS::CST-CONSTRAINT-CONC?-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC?-TREE-EQUIV-CONGRUENCE-ON-CST)
(ABNF::LEMMA)
(PFCS::CST-CONSTRAINT-CONC?-1-IFF-MATCH-CONC)
(ABNF::LEMMA)
(PFCS::CST-CONSTRAINT-CONC?-2-IFF-MATCH-CONC)
(PFCS::CST-LINE-FEED-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-LINE-FEED-CONC)
(PFCS::CST-LINE-FEED-CONC-MATCH)
(PFCS::CST-LINE-FEED-CONC-OF-TREE-FIX-CST)
(PFCS::CST-LINE-FEED-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CARRIAGE-RETURN-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-CARRIAGE-RETURN-CONC)
(PFCS::CST-CARRIAGE-RETURN-CONC-MATCH)
(PFCS::CST-CARRIAGE-RETURN-CONC-OF-TREE-FIX-CST)
(PFCS::CST-CARRIAGE-RETURN-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-SPACE-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-SPACE-CONC)
(PFCS::CST-SPACE-CONC-MATCH)
(PFCS::CST-SPACE-CONC-OF-TREE-FIX-CST)
(PFCS::CST-SPACE-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LINE-TERMINATOR-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-LINE-TERMINATOR-CONC)
(PFCS::CST-LINE-TERMINATOR-CONC-MATCH)
(PFCS::CST-LINE-TERMINATOR-CONC-OF-TREE-FIX-CST)
(PFCS::CST-LINE-TERMINATOR-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-WHITESPACE-CONC1)
(PFCS::CST-WHITESPACE-CONC1-MATCH)
(PFCS::CST-WHITESPACE-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-WHITESPACE-CONC2)
(PFCS::CST-WHITESPACE-CONC2-MATCH)
(PFCS::CST-WHITESPACE-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-UPPERCASE-LETTER-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-UPPERCASE-LETTER-CONC)
(PFCS::CST-UPPERCASE-LETTER-CONC-MATCH)
(PFCS::CST-UPPERCASE-LETTER-CONC-OF-TREE-FIX-CST)
(PFCS::CST-UPPERCASE-LETTER-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LOWERCASE-LETTER-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-LOWERCASE-LETTER-CONC)
(PFCS::CST-LOWERCASE-LETTER-CONC-MATCH)
(PFCS::CST-LOWERCASE-LETTER-CONC-OF-TREE-FIX-CST)
(PFCS::CST-LOWERCASE-LETTER-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-LETTER-CONC1)
(PFCS::CST-LETTER-CONC1-MATCH)
(PFCS::CST-LETTER-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-LETTER-CONC2)
(PFCS::CST-LETTER-CONC2-MATCH)
(PFCS::CST-LETTER-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-DIGIT-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-DIGIT-CONC)
(PFCS::CST-DIGIT-CONC-MATCH)
(PFCS::CST-DIGIT-CONC-OF-TREE-FIX-CST)
(PFCS::CST-DIGIT-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-NUMERAL-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-NUMERAL-CONC)
(PFCS::CST-NUMERAL-CONC-MATCH)
(PFCS::CST-NUMERAL-CONC-OF-TREE-FIX-CST)
(PFCS::CST-NUMERAL-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-INTEGER-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-INTEGER-CONC)
(PFCS::CST-INTEGER-CONC-MATCH)
(PFCS::CST-INTEGER-CONC-OF-TREE-FIX-CST)
(PFCS::CST-INTEGER-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-IDENTIFIER-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-IDENTIFIER-CONC)
(PFCS::CST-IDENTIFIER-CONC-MATCH)
(PFCS::CST-IDENTIFIER-CONC-OF-TREE-FIX-CST)
(PFCS::CST-IDENTIFIER-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-TOKEN-CONC1)
(PFCS::CST-TOKEN-CONC1-MATCH)
(PFCS::CST-TOKEN-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-TOKEN-CONC2)
(PFCS::CST-TOKEN-CONC2-MATCH)
(PFCS::CST-TOKEN-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC3)
(PFCS::TREE-LIST-LISTP-OF-CST-TOKEN-CONC3)
(PFCS::CST-TOKEN-CONC3-MATCH)
(PFCS::CST-TOKEN-CONC3-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC3-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC4)
(PFCS::TREE-LIST-LISTP-OF-CST-TOKEN-CONC4)
(PFCS::CST-TOKEN-CONC4-MATCH)
(PFCS::CST-TOKEN-CONC4-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC4-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-LEXEME-CONC1)
(PFCS::CST-LEXEME-CONC1-MATCH)
(PFCS::CST-LEXEME-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-LEXEME-CONC2)
(PFCS::CST-LEXEME-CONC2-MATCH)
(PFCS::CST-LEXEME-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-PRIMARY-EXPRESSION-CONC1)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-PRIMARY-EXPRESSION-CONC2)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-EXPRESSION-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-EXPRESSION-CONC)
(PFCS::CST-EXPRESSION-CONC-MATCH)
(PFCS::CST-EXPRESSION-CONC-OF-TREE-FIX-CST)
(PFCS::CST-EXPRESSION-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-EQUALITY-CONSTRAINT-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-EQUALITY-CONSTRAINT-CONC)
(PFCS::CST-EQUALITY-CONSTRAINT-CONC-MATCH)
(PFCS::CST-EQUALITY-CONSTRAINT-CONC-OF-TREE-FIX-CST)
(PFCS::CST-EQUALITY-CONSTRAINT-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-RELATION-CONSTRAINT-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-RELATION-CONSTRAINT-CONC)
(PFCS::CST-RELATION-CONSTRAINT-CONC-MATCH)
(PFCS::CST-RELATION-CONSTRAINT-CONC-OF-TREE-FIX-CST)
(PFCS::CST-RELATION-CONSTRAINT-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC1)
(PFCS::TREE-LIST-LISTP-OF-CST-CONSTRAINT-CONC1)
(PFCS::CST-CONSTRAINT-CONC1-MATCH)
(PFCS::CST-CONSTRAINT-CONC1-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC1-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC2)
(PFCS::TREE-LIST-LISTP-OF-CST-CONSTRAINT-CONC2)
(PFCS::CST-CONSTRAINT-CONC2-MATCH)
(PFCS::CST-CONSTRAINT-CONC2-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC2-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-DEFINITION-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-DEFINITION-CONC)
(PFCS::CST-DEFINITION-CONC-MATCH)
(PFCS::CST-DEFINITION-CONC-OF-TREE-FIX-CST)
(PFCS::CST-DEFINITION-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-SYSTEM-CONC)
(PFCS::TREE-LIST-LISTP-OF-CST-SYSTEM-CONC)
(PFCS::CST-SYSTEM-CONC-MATCH)
(PFCS::CST-SYSTEM-CONC-OF-TREE-FIX-CST)
(PFCS::CST-SYSTEM-CONC-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LINE-FEED-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-LINE-FEED-CONC-REP)
(PFCS::CST-LINE-FEED-CONC-REP-MATCH)
(PFCS::CST-LINE-FEED-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-LINE-FEED-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CARRIAGE-RETURN-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-CARRIAGE-RETURN-CONC-REP)
(PFCS::CST-CARRIAGE-RETURN-CONC-REP-MATCH)
(PFCS::CST-CARRIAGE-RETURN-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-CARRIAGE-RETURN-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-SPACE-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-SPACE-CONC-REP)
(PFCS::CST-SPACE-CONC-REP-MATCH)
(PFCS::CST-SPACE-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-SPACE-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-WHITESPACE-CONC1-REP)
(PFCS::CST-WHITESPACE-CONC1-REP-MATCH)
(PFCS::CST-WHITESPACE-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-WHITESPACE-CONC2-REP)
(PFCS::CST-WHITESPACE-CONC2-REP-MATCH)
(PFCS::CST-WHITESPACE-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-UPPERCASE-LETTER-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-UPPERCASE-LETTER-CONC-REP)
(PFCS::CST-UPPERCASE-LETTER-CONC-REP-MATCH)
(PFCS::CST-UPPERCASE-LETTER-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-UPPERCASE-LETTER-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LOWERCASE-LETTER-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-LOWERCASE-LETTER-CONC-REP)
(PFCS::CST-LOWERCASE-LETTER-CONC-REP-MATCH)
(PFCS::CST-LOWERCASE-LETTER-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-LOWERCASE-LETTER-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-LETTER-CONC1-REP)
(PFCS::CST-LETTER-CONC1-REP-MATCH)
(PFCS::CST-LETTER-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-LETTER-CONC2-REP)
(PFCS::CST-LETTER-CONC2-REP-MATCH)
(PFCS::CST-LETTER-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-DIGIT-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-DIGIT-CONC-REP)
(PFCS::CST-DIGIT-CONC-REP-MATCH)
(PFCS::CST-DIGIT-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-DIGIT-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-TOKEN-CONC1-REP)
(PFCS::CST-TOKEN-CONC1-REP-MATCH)
(PFCS::CST-TOKEN-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-TOKEN-CONC2-REP)
(PFCS::CST-TOKEN-CONC2-REP-MATCH)
(PFCS::CST-TOKEN-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC3-REP)
(PFCS::TREE-LISTP-OF-CST-TOKEN-CONC3-REP)
(PFCS::CST-TOKEN-CONC3-REP-MATCH)
(PFCS::CST-TOKEN-CONC3-REP-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC3-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC4-REP)
(PFCS::TREE-LISTP-OF-CST-TOKEN-CONC4-REP)
(PFCS::CST-TOKEN-CONC4-REP-MATCH)
(PFCS::CST-TOKEN-CONC4-REP-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC4-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-LEXEME-CONC1-REP)
(PFCS::CST-LEXEME-CONC1-REP-MATCH)
(PFCS::CST-LEXEME-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-LEXEME-CONC2-REP)
(PFCS::CST-LEXEME-CONC2-REP-MATCH)
(PFCS::CST-LEXEME-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-PRIMARY-EXPRESSION-CONC1-REP)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-PRIMARY-EXPRESSION-CONC2-REP)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-EXPRESSION-CONC-REP)
(PFCS::TREE-LISTP-OF-CST-EXPRESSION-CONC-REP)
(PFCS::CST-EXPRESSION-CONC-REP-MATCH)
(PFCS::CST-EXPRESSION-CONC-REP-OF-TREE-FIX-CST)
(PFCS::CST-EXPRESSION-CONC-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC1-REP)
(PFCS::TREE-LISTP-OF-CST-CONSTRAINT-CONC1-REP)
(PFCS::CST-CONSTRAINT-CONC1-REP-MATCH)
(PFCS::CST-CONSTRAINT-CONC1-REP-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC1-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC2-REP)
(PFCS::TREE-LISTP-OF-CST-CONSTRAINT-CONC2-REP)
(PFCS::CST-CONSTRAINT-CONC2-REP-MATCH)
(PFCS::CST-CONSTRAINT-CONC2-REP-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC2-REP-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-WHITESPACE-CONC1-REP-ELEM)
(PFCS::CST-WHITESPACE-CONC1-REP-ELEM-MATCH)
(PFCS::CST-WHITESPACE-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-WHITESPACE-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-WHITESPACE-CONC2-REP-ELEM)
(PFCS::CST-WHITESPACE-CONC2-REP-ELEM-MATCH)
(PFCS::CST-WHITESPACE-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-WHITESPACE-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-LETTER-CONC1-REP-ELEM)
(PFCS::CST-LETTER-CONC1-REP-ELEM-MATCH)
(PFCS::CST-LETTER-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LETTER-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-LETTER-CONC2-REP-ELEM)
(PFCS::CST-LETTER-CONC2-REP-ELEM-MATCH)
(PFCS::CST-LETTER-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-LETTER-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-TOKEN-CONC1-REP-ELEM)
(PFCS::CST-TOKEN-CONC1-REP-ELEM-MATCH)
(PFCS::CST-TOKEN-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-TOKEN-CONC2-REP-ELEM)
(PFCS::CST-TOKEN-CONC2-REP-ELEM-MATCH)
(PFCS::CST-TOKEN-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC3-REP-ELEM)
(PFCS::TREEP-OF-CST-TOKEN-CONC3-REP-ELEM)
(PFCS::CST-TOKEN-CONC3-REP-ELEM-MATCH)
(PFCS::CST-TOKEN-CONC3-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC3-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-TOKEN-CONC4-REP-ELEM)
(PFCS::TREEP-OF-CST-TOKEN-CONC4-REP-ELEM)
(PFCS::CST-TOKEN-CONC4-REP-ELEM-MATCH)
(PFCS::CST-TOKEN-CONC4-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-TOKEN-CONC4-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-LEXEME-CONC1-REP-ELEM)
(PFCS::CST-LEXEME-CONC1-REP-ELEM-MATCH)
(PFCS::CST-LEXEME-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-LEXEME-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-LEXEME-CONC2-REP-ELEM)
(PFCS::CST-LEXEME-CONC2-REP-ELEM-MATCH)
(PFCS::CST-LEXEME-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-LEXEME-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-PRIMARY-EXPRESSION-CONC1-REP-ELEM)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-ELEM-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-PRIMARY-EXPRESSION-CONC2-REP-ELEM)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-ELEM-MATCH)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-PRIMARY-EXPRESSION-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-EXPRESSION-CONC-REP-ELEM)
(PFCS::TREEP-OF-CST-EXPRESSION-CONC-REP-ELEM)
(PFCS::CST-EXPRESSION-CONC-REP-ELEM-MATCH)
(PFCS::CST-EXPRESSION-CONC-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-EXPRESSION-CONC-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC1-REP-ELEM)
(PFCS::TREEP-OF-CST-CONSTRAINT-CONC1-REP-ELEM)
(PFCS::CST-CONSTRAINT-CONC1-REP-ELEM-MATCH)
(PFCS::CST-CONSTRAINT-CONC1-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC1-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
(PFCS::CST-CONSTRAINT-CONC2-REP-ELEM)
(PFCS::TREEP-OF-CST-CONSTRAINT-CONC2-REP-ELEM)
(PFCS::CST-CONSTRAINT-CONC2-REP-ELEM-MATCH)
(PFCS::CST-CONSTRAINT-CONC2-REP-ELEM-OF-TREE-FIX-CST)
(PFCS::CST-CONSTRAINT-CONC2-REP-ELEM-TREE-EQUIV-CONGRUENCE-ON-CST)
