(ABNF::NUM-VAL-IN-TERMSET-P
 (17 1 (:REWRITE INTEGERS-FROM-TO-NIL-WHEN-MIN>MAX))
 (6 2 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (4 4 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (4 2 (:DEFINITION IFIX))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(ABNF::BOOLEANP-OF-NUM-VAL-IN-TERMSET-P)
(ABNF::CHAR-SENSITIVE-IN-TERMSET-P)
(ABNF::BOOLEANP-OF-CHAR-SENSITIVE-IN-TERMSET-P)
(ABNF::CHAR-INSENSITIVE-IN-TERMSET-P)
(ABNF::BOOLEANP-OF-CHAR-INSENSITIVE-IN-TERMSET-P)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P
 (6 3 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-CONS)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-CDR-WHEN-CHARS-SENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::CHAR-SENSITIVE-IN-TERMSET-P-OF-CAR-WHEN-CHARS-SENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-APPEND)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-SFIX)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-INSERT)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-DELETE)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-MERGESORT)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-UNION)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-REV)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-RCONS)
(ABNF::CHAR-SENSITIVE-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-CHARS-SENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-TAKE)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-REPEAT)
(ABNF::CHAR-SENSITIVE-IN-TERMSET-P-OF-NTH-WHEN-CHARS-SENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-BUTLAST)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-NTHCDR)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-LAST)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-REMOVE)
(ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-REVAPPEND)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P
 (6 3 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-CONS)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-CDR-WHEN-CHARS-INSENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::CHAR-INSENSITIVE-IN-TERMSET-P-OF-CAR-WHEN-CHARS-INSENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-APPEND)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-SFIX)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-INSERT)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-DELETE)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-MERGESORT)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-UNION)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-REV)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-RCONS)
(ABNF::CHAR-INSENSITIVE-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-CHARS-INSENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-TAKE)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-REPEAT)
(ABNF::CHAR-INSENSITIVE-IN-TERMSET-P-OF-NTH-WHEN-CHARS-INSENSITIVE-IN-TERMSET-P)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-BUTLAST)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-NTHCDR)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-LAST)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-REMOVE)
(ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-REVAPPEND)
(ABNF::CHAR-VAL-IN-TERMSET-P
 (3 3 (:REWRITE ABNF::CHAR-VAL-P-WHEN-IN-CHAR-VAL-SETP-BINDS-FREE-X))
 )
(ABNF::BOOLEANP-OF-CHAR-VAL-IN-TERMSET-P)
(ABNF::PROSE-VAL-IN-TERMSET-P)
(ABNF::BOOLEANP-OF-PROSE-VAL-IN-TERMSET-P)
(ABNF::ALTERNATION-IN-TERMSET-P
 (120 40 (:REWRITE DEFAULT-<-1))
 (64 40 (:REWRITE DEFAULT-<-2))
 (14 1 (:DEFINITION ABNF::REPETITION-IN-TERMSET-P))
 (12 11 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (10 1 (:DEFINITION ABNF::CONCATENATION-IN-TERMSET-P))
 (9 8 (:REWRITE DEFAULT-CDR))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (5 5 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (4 4 (:REWRITE ABNF::CONCATENATIONP-WHEN-MEMBER-EQUAL-OF-ALTERNATIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE ABNF::CONCATENATIONP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE ABNF::ALTERNATIONP-WHEN-NOT-CONSP))
 )
(ABNF::ALT/CONC/REP/ELEM-IN-TERMSET-P-FLAG
 (301 1 (:DEFINITION O-P))
 (167 1 (:DEFINITION O<))
 (133 43 (:REWRITE DEFAULT-<-1))
 (119 8 (:DEFINITION O-FIRST-EXPT))
 (100 100 (:TYPE-PRESCRIPTION TWO-NATS-MEASURE))
 (97 43 (:REWRITE DEFAULT-<-2))
 (82 17 (:DEFINITION O-FINP))
 (76 31 (:REWRITE DEFAULT-CAR))
 (53 5 (:DEFINITION O-FIRST-COEFF))
 (48 18 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (44 16 (:REWRITE DEFAULT-CDR))
 (31 31 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (27 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 2 (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (18 18 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (18 18 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (18 18 (:REWRITE CONSP-BY-LEN))
 (18 4 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (16 4 (:DEFINITION O-RST))
 (16 1 (:DEFINITION ACL2-NUMBER-LISTP))
 (12 2 (:DEFINITION RATIONAL-LISTP))
 (3 1 (:DEFINITION POSP))
 (2 2 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (1 1 (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(ABNF::ALT/CONC/REP/ELEM-IN-TERMSET-P-FLAG-EQUIVALENCES)
(ABNF::FLAG-LEMMA-FOR-RETURN-TYPE-OF-ALTERNATION-IN-TERMSET-P.YES/NO)
(ABNF::RETURN-TYPE-OF-ALTERNATION-IN-TERMSET-P.YES/NO)
(ABNF::RETURN-TYPE-OF-CONCATENATION-IN-TERMSET-P.YES/NO)
(ABNF::RETURN-TYPE-OF-REPETITION-IN-TERMSET-P.YES/NO)
(ABNF::RETURN-TYPE-OF-ELEMENT-IN-TERMSET-P.YES/NO)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-CONS)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-CDR-WHEN-ALTERNATION-IN-TERMSET-P)
(ABNF::ALTERNATION-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-CAR-WHEN-ALTERNATION-IN-TERMSET-P)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-APPEND)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-SFIX)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-INSERT)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-DELETE)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-MERGESORT)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-UNION)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-REV)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-RCONS)
(ABNF::CONCATENATION-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-ALTERNATION-IN-TERMSET-P)
(ABNF::ALTERNATION-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::ALTERNATION-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-TAKE)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-REPEAT)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-NTH-WHEN-ALTERNATION-IN-TERMSET-P)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-BUTLAST)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-NTHCDR)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-LAST)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-REMOVE)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-REVAPPEND)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(ABNF::CONCATENATION-IN-TERMSET-P-OF-CONS)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-CDR-WHEN-CONCATENATION-IN-TERMSET-P)
(ABNF::CONCATENATION-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::REPETITION-IN-TERMSET-P-OF-CAR-WHEN-CONCATENATION-IN-TERMSET-P)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-APPEND)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-SFIX)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-INSERT)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-DELETE)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-MERGESORT)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-UNION)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-REV)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-RCONS)
(ABNF::REPETITION-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-CONCATENATION-IN-TERMSET-P)
(ABNF::CONCATENATION-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::CONCATENATION-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-TAKE)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-REPEAT)
(ABNF::REPETITION-IN-TERMSET-P-OF-NTH-WHEN-CONCATENATION-IN-TERMSET-P)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-BUTLAST)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-NTHCDR)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-LAST)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-REMOVE)
(ABNF::CONCATENATION-IN-TERMSET-P-OF-REVAPPEND)
(ABNF::RULE-IN-TERMSET-P)
(ABNF::BOOLEANP-OF-RULE-IN-TERMSET-P)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM
 (2 2 (:REWRITE ABNF::ALTERNATION-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 )
(ABNF::RULELIST-IN-TERMSET-P
 (12 2 (:REWRITE ABNF::ALTERNATION-IN-TERMSET-P-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION ABNF::RULE->DEFINIENS$INLINE))
 (6 1 (:REWRITE ABNF::RULELISTP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE ABNF::ALTERNATION-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(ABNF::RULELIST-IN-TERMSET-P-OF-CONS)
(ABNF::RULELIST-IN-TERMSET-P-OF-CDR-WHEN-RULELIST-IN-TERMSET-P)
(ABNF::RULELIST-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::RULE-IN-TERMSET-P-OF-CAR-WHEN-RULELIST-IN-TERMSET-P)
(ABNF::RULELIST-IN-TERMSET-P-OF-APPEND)
(ABNF::RULELIST-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::RULELIST-IN-TERMSET-P-OF-SFIX)
(ABNF::RULELIST-IN-TERMSET-P-OF-INSERT)
(ABNF::RULELIST-IN-TERMSET-P-OF-DELETE)
(ABNF::RULELIST-IN-TERMSET-P-OF-MERGESORT)
(ABNF::RULELIST-IN-TERMSET-P-OF-UNION)
(ABNF::RULELIST-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::RULELIST-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::RULELIST-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::RULELIST-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::RULELIST-IN-TERMSET-P-OF-REV)
(ABNF::RULELIST-IN-TERMSET-P-OF-RCONS)
(ABNF::RULE-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-RULELIST-IN-TERMSET-P)
(ABNF::RULELIST-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::RULELIST-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::RULELIST-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::RULELIST-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::RULELIST-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::RULELIST-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::RULELIST-IN-TERMSET-P-OF-TAKE)
(ABNF::RULELIST-IN-TERMSET-P-OF-REPEAT)
(ABNF::RULE-IN-TERMSET-P-OF-NTH-WHEN-RULELIST-IN-TERMSET-P)
(ABNF::RULELIST-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::RULELIST-IN-TERMSET-P-OF-BUTLAST)
(ABNF::RULELIST-IN-TERMSET-P-OF-NTHCDR)
(ABNF::RULELIST-IN-TERMSET-P-OF-LAST)
(ABNF::RULELIST-IN-TERMSET-P-OF-REMOVE)
(ABNF::RULELIST-IN-TERMSET-P-OF-REVAPPEND)
(ABNF::ALTERNATION-IN-TERMSET-P-OF-LOOKUP-RULENAME
 (865 79 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (305 10 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (275 25 (:REWRITE ABNF::RULENAME-FIX-WHEN-RULENAMEP))
 (270 2 (:REWRITE SUBSETP-APPEND1))
 (265 5 (:REWRITE ABNF::LOOKUP-RULENAME-OF-RULENAME-FIX-RULENAME))
 (248 10 (:REWRITE ABNF::RULE-IN-TERMSET-P-OF-CAR-WHEN-RULELIST-IN-TERMSET-P))
 (199 10 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (156 156 (:TYPE-PRESCRIPTION ABNF::LOOKUP-RULENAME))
 (128 84 (:REWRITE DEFAULT-CDR))
 (125 25 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (124 124 (:TYPE-PRESCRIPTION ABNF::RULE->DEFINIENS$INLINE))
 (122 78 (:REWRITE DEFAULT-CAR))
 (112 14 (:REWRITE APPEND-UNDER-IFF))
 (80 12 (:REWRITE SUBSETP-TRANS2))
 (78 78 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (75 75 (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (50 50 (:TYPE-PRESCRIPTION ABNF::RULENAME-OPTIONP))
 (50 50 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (50 25 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (35 5 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (34 34 (:REWRITE ABNF::RULELIST-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (30 5 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (29 29 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (29 29 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (29 29 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (29 29 (:REWRITE CONSP-BY-LEN))
 (25 25 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (20 20 (:REWRITE ABNF::RULE-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-RULELIST-IN-TERMSET-P))
 (16 16 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (14 2 (:REWRITE ABNF::RULELIST-IN-TERMSET-P-OF-CDR-WHEN-RULELIST-IN-TERMSET-P))
 (12 12 (:REWRITE SUBSETP-TRANS))
 )
(ABNF::SYMBOL-IN-TERMSET-P)
(ABNF::BOOLEANP-OF-SYMBOL-IN-TERMSET-P)
(ABNF::SYMBOL-IN-TERMSET-P-WHEN-NATP
 (22 4 (:REWRITE SET::IN-TAIL))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (8 8 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (4 4 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ABNF::SYMBOL-IN-TERMSET-P-WHEN-RULENAMEP
 (11 2 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (8 1 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (4 4 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (3 3 (:TYPE-PRESCRIPTION ABNF::RULENAME-OPTIONP))
 (2 2 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-NATP))
 )
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM
 (1 1 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-RULENAMEP))
 (1 1 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-NATP))
 )
(ABNF::STRING-IN-TERMSET-P
 (174 2 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-NATP))
 (154 2 (:DEFINITION NATP))
 (112 8 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (106 4 (:DEFINITION INTEGER-LISTP))
 (40 8 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
 (34 2 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-RULENAMEP))
 (30 30 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (25 2 (:REWRITE ABNF::STRINGP-WHEN-NAT-LISTP))
 (22 15 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (22 4 (:REWRITE SET::IN-TAIL))
 (20 8 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (18 3 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (12 2 (:REWRITE ABNF::RULENAMEP-OF-CAR-WHEN-RULENAME-LISTP))
 (12 2 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (12 2 (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (12 2 (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (10 2 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (8 8 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (6 6 (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 1 (:REWRITE ABNF::STRINGP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION ABNF::RULENAME-OPTIONP))
 (4 4 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (4 4 (:REWRITE ABNF::RULENAME-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 2 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE ABNF::RULENAME-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 )
(ABNF::STRING-IN-TERMSET-P-OF-CONS)
(ABNF::STRING-IN-TERMSET-P-OF-CDR-WHEN-STRING-IN-TERMSET-P)
(ABNF::STRING-IN-TERMSET-P-WHEN-NOT-CONSP)
(ABNF::SYMBOL-IN-TERMSET-P-OF-CAR-WHEN-STRING-IN-TERMSET-P)
(ABNF::STRING-IN-TERMSET-P-OF-APPEND)
(ABNF::STRING-IN-TERMSET-P-OF-LIST-FIX)
(ABNF::STRING-IN-TERMSET-P-OF-SFIX)
(ABNF::STRING-IN-TERMSET-P-OF-INSERT)
(ABNF::STRING-IN-TERMSET-P-OF-DELETE)
(ABNF::STRING-IN-TERMSET-P-OF-MERGESORT)
(ABNF::STRING-IN-TERMSET-P-OF-UNION)
(ABNF::STRING-IN-TERMSET-P-OF-INTERSECT-1)
(ABNF::STRING-IN-TERMSET-P-OF-INTERSECT-2)
(ABNF::STRING-IN-TERMSET-P-OF-DIFFERENCE)
(ABNF::STRING-IN-TERMSET-P-OF-DUPLICATED-MEMBERS)
(ABNF::STRING-IN-TERMSET-P-OF-REV)
(ABNF::STRING-IN-TERMSET-P-OF-RCONS)
(ABNF::SYMBOL-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-STRING-IN-TERMSET-P)
(ABNF::STRING-IN-TERMSET-P-WHEN-SUBSETP-EQUAL)
(ABNF::STRING-IN-TERMSET-P-SET-EQUIV-CONGRUENCE)
(ABNF::STRING-IN-TERMSET-P-OF-SET-DIFFERENCE-EQUAL)
(ABNF::STRING-IN-TERMSET-P-OF-INTERSECTION-EQUAL-1)
(ABNF::STRING-IN-TERMSET-P-OF-INTERSECTION-EQUAL-2)
(ABNF::STRING-IN-TERMSET-P-OF-UNION-EQUAL)
(ABNF::STRING-IN-TERMSET-P-OF-TAKE)
(ABNF::STRING-IN-TERMSET-P-OF-REPEAT)
(ABNF::SYMBOL-IN-TERMSET-P-OF-NTH-WHEN-STRING-IN-TERMSET-P)
(ABNF::STRING-IN-TERMSET-P-OF-UPDATE-NTH)
(ABNF::STRING-IN-TERMSET-P-OF-BUTLAST)
(ABNF::STRING-IN-TERMSET-P-OF-NTHCDR)
(ABNF::STRING-IN-TERMSET-P-OF-LAST)
(ABNF::STRING-IN-TERMSET-P-OF-REMOVE)
(ABNF::STRING-IN-TERMSET-P-OF-REVAPPEND)
(ABNF::STRING-IN-TERMSET-P-WHEN-NAT-LISTP
 (486 20 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-OF-CAR-WHEN-STRING-IN-TERMSET-P))
 (383 19 (:REWRITE ABNF::STRING-IN-TERMSET-P-OF-CDR-WHEN-STRING-IN-TERMSET-P))
 (372 45 (:REWRITE SET::IN-TAIL))
 (286 20 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-RULENAMEP))
 (279 41 (:REWRITE SET::IN-OF-CAR-WHEN-LIST-IN))
 (134 134 (:REWRITE SET::LIST-IN-WHEN-SUBSETP-EQUAL))
 (114 15 (:REWRITE ABNF::RULENAMEP-OF-CAR-WHEN-RULENAME-LISTP))
 (88 88 (:REWRITE ABNF::STRING-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (78 13 (:REWRITE SET::LIST-IN-OF-CDR-WHEN-LIST-IN))
 (75 15 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (70 70 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (63 21 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (45 45 (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (45 45 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (42 14 (:REWRITE SET::NEVER-IN-EMPTY))
 (42 7 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (40 40 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-STRING-IN-TERMSET-P))
 (38 38 (:REWRITE ABNF::RULENAME-LISTP-WHEN-SUBSETP-EQUAL))
 (37 37 (:REWRITE DEFAULT-CDR))
 (30 30 (:TYPE-PRESCRIPTION ABNF::RULENAME-OPTIONP))
 (30 30 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (30 15 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (24 4 (:REWRITE ABNF::RULENAME-LISTP-OF-CDR-WHEN-RULENAME-LISTP))
 (23 23 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (19 19 (:REWRITE ABNF::RULENAME-LISTP-WHEN-NOT-CONSP))
 (19 19 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (17 15 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (15 15 (:REWRITE SUBSETP-TRANS2))
 (15 15 (:REWRITE SUBSETP-TRANS))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (7 7 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (7 7 (:REWRITE CONSP-BY-LEN))
 (2 2 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-NUM-VAL-IN-TERMSET
 (90 10 (:REWRITE DEFAULT-<-1))
 (76 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (73 10 (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (66 18 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (63 3 (:DEFINITION ACL2-NUMBER-LISTP))
 (56 10 (:REWRITE DEFAULT-<-2))
 (53 11 (:REWRITE SET::LIST-IN-WHEN-NOT-CONSP))
 (52 2 (:REWRITE INTEGERS-FROM-TO-IFF-MIN<=MAX))
 (48 6 (:DEFINITION RATIONAL-LISTP))
 (36 4 (:REWRITE SET::IN-TAIL))
 (34 2 (:REWRITE INTEGERS-FROM-TO-NIL-WHEN-MIN>MAX))
 (32 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (31 2 (:REWRITE SET::LIST-IN-OF-CDR-WHEN-LIST-IN))
 (28 4 (:REWRITE SET::IN-OF-CAR-WHEN-LIST-IN))
 (18 18 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-INTEGERS-FROM-TO))
 (10 2 (:REWRITE LEN-WHEN-ATOM))
 (9 9 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (6 6 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION IFIX))
 (4 4 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 )
(ABNF::NAT-IN-TERMSET-WHEN-MATCH-SENSITIVE-CHAR-IN-TERMSET
 (11 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (3 3 (:REWRITE DEFAULT-CHAR-CODE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE STR::EQUAL-OF-CHAR-CODE-AND-CONSTANT))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(ABNF::NATS-IN-TERMSET-WHEN-MATCH-SENSITIVE-CHARS-IN-TERMSET
 (234 23 (:REWRITE ABNF::CHAR-SENSITIVE-IN-TERMSET-P-OF-CAR-WHEN-CHARS-SENSITIVE-IN-TERMSET-P))
 (221 21 (:REWRITE ABNF::CHARS-SENSITIVE-IN-TERMSET-P-OF-CDR-WHEN-CHARS-SENSITIVE-IN-TERMSET-P))
 (152 106 (:REWRITE ABNF::CHARS-SENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (76 76 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (76 76 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (76 76 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (76 76 (:REWRITE CONSP-BY-LEN))
 (66 11 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (57 55 (:REWRITE DEFAULT-CDR))
 (56 56 (:REWRITE DEFAULT-CAR))
 (56 56 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (45 11 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (32 32 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (31 5 (:REWRITE SET::LIST-IN-OF-CDR-WHEN-LIST-IN))
 (26 2 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (21 21 (:REWRITE SUBSETP-TRANS2))
 (21 21 (:REWRITE SUBSETP-TRANS))
 (11 11 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (11 11 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (10 1 (:REWRITE SUBSETP-OF-CONS))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ABNF::NAT-IN-TERMSET-WHEN-MATCH-INSENSITIVE-CHAR-IN-TERMSET
 (66 12 (:REWRITE SET::IN-TAIL))
 (24 24 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (24 24 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (18 6 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (18 6 (:REWRITE SET::NEVER-IN-EMPTY))
 (18 3 (:REWRITE STR::UPCASE-CHAR-DOES-NOTHING-UNLESS-DOWN-ALPHA-P))
 (14 9 (:REWRITE DEFAULT-CHAR-CODE))
 (12 12 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (10 10 (:TYPE-PRESCRIPTION STR::UP-ALPHA-P$INLINE))
 (9 3 (:REWRITE STR::DOWN-ALPHA-P-WHEN-UP-ALPHA-P))
 (6 6 (:TYPE-PRESCRIPTION STR::DOWN-ALPHA-P$INLINE))
 (6 2 (:REWRITE STR::DOWNCASE-CHAR-DOES-NOTHING-UNLESS-UP-ALPHA-P))
 (3 3 (:REWRITE STR::EQUAL-OF-CHAR-CODE-AND-CONSTANT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ABNF::NATS-IN-TERMSET-WHEN-MATCH-INSENSITIVE-CHARS-IN-TERMSET
 (234 23 (:REWRITE ABNF::CHAR-INSENSITIVE-IN-TERMSET-P-OF-CAR-WHEN-CHARS-INSENSITIVE-IN-TERMSET-P))
 (221 21 (:REWRITE ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-OF-CDR-WHEN-CHARS-INSENSITIVE-IN-TERMSET-P))
 (152 106 (:REWRITE ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (76 76 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (76 76 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (76 76 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (76 76 (:REWRITE CONSP-BY-LEN))
 (66 11 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (57 55 (:REWRITE DEFAULT-CDR))
 (56 56 (:REWRITE DEFAULT-CAR))
 (56 56 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (45 11 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (32 32 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (31 5 (:REWRITE SET::LIST-IN-OF-CDR-WHEN-LIST-IN))
 (26 2 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (21 21 (:REWRITE SUBSETP-TRANS2))
 (21 21 (:REWRITE SUBSETP-TRANS))
 (11 11 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (11 11 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (10 1 (:REWRITE SUBSETP-OF-CONS))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-CHAR-VAL-IN-TERMSET
 (40 4 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (28 4 (:REWRITE STR::EXPLODE-UNDER-IFF))
 (16 16 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (13 1 (:REWRITE ABNF::NATS-MATCH-SENSITIVE-CHARS-P-WHEN-ATOM-CHARS))
 (13 1 (:REWRITE ABNF::NATS-MATCH-INSENSITIVE-CHARS-P-WHEN-ATOM-CHARS))
 (13 1 (:REWRITE ABNF::CHARS-SENSITIVE-IN-TERMSET-P-WHEN-NOT-CONSP))
 (13 1 (:REWRITE ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-WHEN-NOT-CONSP))
 (12 12 (:TYPE-PRESCRIPTION ABNF::CHAR-VAL-SENSITIVE->GET$INLINE))
 (12 12 (:TYPE-PRESCRIPTION ABNF::CHAR-VAL-INSENSITIVE->GET$INLINE))
 (10 10 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (8 4 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:REWRITE ABNF::CHARS-SENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::CHARS-INSENSITIVE-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 )
(ABNF::FLAG-LEMMA-FOR-LEAVES-IN-TERMSET-WHEN-MATCH-ALTERNATION-IN-TERMSET
 (771 23 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (666 41 (:REWRITE APPEND-UNDER-IFF))
 (480 2 (:REWRITE NAT-LISTP-OF-APPEND))
 (461 12 (:REWRITE ABNF::STRING-IN-TERMSET-P-WHEN-NOT-CONSP))
 (379 4 (:REWRITE SUBSETP-APPEND1))
 (370 14 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (363 363 (:TYPE-PRESCRIPTION ABNF::TREE-LIST->STRING))
 (297 14 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (296 296 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (296 296 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (296 296 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (296 296 (:REWRITE CONSP-BY-LEN))
 (273 7 (:DEFINITION ABNF::ALTERNATION-IN-TERMSET-P))
 (252 252 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-LIST->STRING))
 (237 20 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (229 50 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (217 40 (:REWRITE SUBSETP-TRANS2))
 (198 20 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (192 176 (:REWRITE DEFAULT-CDR))
 (189 11 (:REWRITE ABNF::NAT-LISTP-OF-TREE-LIST-LIST->STRING-WHEN-TERMINATED))
 (188 47 (:REWRITE ABNF::ALTERNATION-IN-TERMSET-P-WHEN-NOT-CONSP))
 (187 187 (:TYPE-PRESCRIPTION ABNF::TREE->STRING))
 (175 159 (:REWRITE DEFAULT-CAR))
 (159 159 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (152 8 (:REWRITE ABNF::NAT-LISTP-OF-TREE-LIST->STRING-WHEN-TERMINATED))
 (148 148 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (96 96 (:TYPE-PRESCRIPTION ABNF::ELEMENT-GROUP->GET$INLINE))
 (78 13 (:REWRITE ABNF::RULELIST-IN-TERMSET-P-WHEN-NOT-CONSP))
 (66 14 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (66 14 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (60 60 (:TYPE-PRESCRIPTION ABNF::TRUE-LISTP-OF-CAR-OF-TREE-NONLEAF->BRANCHES))
 (60 10 (:REWRITE LEN-WHEN-ATOM))
 (49 7 (:REWRITE ABNF::CONCATENATION-IN-TERMSET-P-OF-CAR-WHEN-ALTERNATION-IN-TERMSET-P))
 (49 7 (:REWRITE ABNF::ALTERNATION-IN-TERMSET-P-OF-CDR-WHEN-ALTERNATION-IN-TERMSET-P))
 (46 5 (:REWRITE ABNF::CONCATENATION-IN-TERMSET-P-OF-CDR-WHEN-CONCATENATION-IN-TERMSET-P))
 (43 43 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (43 6 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-OF-CDR-WHEN-TREE-LIST-MATCH-ELEMENT-P))
 (42 10 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (42 10 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (40 40 (:REWRITE SUBSETP-TRANS))
 (36 3 (:REWRITE ABNF::REPETITION-IN-TERMSET-P-OF-CAR-WHEN-CONCATENATION-IN-TERMSET-P))
 (32 32 (:TYPE-PRESCRIPTION ABNF::LOOKUP-RULENAME))
 (29 3 (:REWRITE ABNF::NAT-LISTP-OF-TREE->STRING-WHEN-TERMINATED))
 (28 28 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (24 24 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (24 24 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (20 20 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (20 3 (:REWRITE ABNF::NAT-LISTP-OF-TREE->STRING-WHEN-MATCH-ELEMENT-NUM/CHAR-VAL))
 (18 2 (:REWRITE ABNF::TREE-TERMINATEDP-OF-CAR-WHEN-TREE-LIST-TERMINATEDP))
 (18 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-OF-CDR-WHEN-TREE-LIST-TERMINATEDP))
 (14 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-OF-CAR-WHEN-TREE-LIST-LIST-TERMINATEDP))
 (14 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-OF-CDR-WHEN-TREE-LIST-LIST-TERMINATEDP))
 (13 2 (:REWRITE MEMBER-OF-CONS))
 (12 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (10 10 (:REWRITE SET::LIST-IN-WHEN-SUBSETP-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION ABNF::TREE-LEAFTERM->GET$INLINE))
 (8 8 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (7 1 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-OF-CAR-WHEN-TREE-LIST-MATCH-ELEMENT-P))
 (4 4 (:TYPE-PRESCRIPTION ABNF::TREE-TERMINATEDP))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 4 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (4 2 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE ABNF::SYMBOL-IN-TERMSET-P-WHEN-MEMBER-EQUAL-OF-STRING-IN-TERMSET-P))
 (2 1 (:REWRITE NAT-LISTP-OF-CONS))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::REPEAT-RANGE-FIX-UNDER-REPEAT-RANGE-EQUIV))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-ALTERNATION-IN-TERMSET)
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-CONCATENATION-IN-TERMSET)
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-REPETITION-IN-TERMSET)
(ABNF::LEAVES-IN-TERMSET-WHEN-LIST-MATCH-ELEMENT-IN-TERMSET)
(ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-ELEMENT-IN-TERMSET)
(ABNF::TERMINAL-STRINGS-IN-TERMSET-WHEN-RULES-IN-TERMSET
 (138 8 (:REWRITE ABNF::NOT-STRING-PARSABLEP-WHEN-PARSE-NIL))
 (72 6 (:REWRITE ABNF::PARSE-IS-PARSE!-WHEN-STRING-UNAMBIGUOUSP))
 (68 12 (:REWRITE ABNF::STRING-UNAMBIGUOUSP-WHEN-STRING-HAS-FINITE-PARSE-TREES-P-ONE))
 (62 6 (:REWRITE ABNF::PARSE-TREEP-WHEN-STRING-UNAMBIGUOUSP))
 (56 6 (:REWRITE ABNF::PARSE-WHEN-NOT-STRING-PARSABLEP))
 (52 12 (:REWRITE ABNF::STRING-UNAMBIGUOUSP-WHEN-PARSE-ONE))
 (50 4 (:REWRITE ABNF::STRING-HAS-FINITE-PARSE-TREES-P-WHEN-NOT-STRING-PARSABLEP))
 (30 8 (:REWRITE ABNF::NOT-STRING-PARSABLEP-WHEN-STRING-HAS-FINITE-PARSE-TREES-P-NIL))
 (28 4 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (22 8 (:REWRITE ABNF::NOT-STRING-PARSABLEP-WHEN-PARSE-TREES-OF-STRING-P-OF-NIL))
 (22 4 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (22 2 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (20 6 (:REWRITE ABNF::PARSE-WHEN-STRING-UNAMBIGUOUSP))
 (18 4 (:REWRITE ABNF::STRING-HAS-FINITE-PARSE-TREES-P-WHEN-STRING-UNAMBIGUOUSP))
 (18 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION SET::INSERT))
 (16 6 (:REWRITE ABNF::PARSE-TREEP-OF-STRING-PARSABLEP-WITNESS-WHEN-STRING-PARSABLEP))
 (16 2 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (16 2 (:REWRITE SET::INSERT-IDENTITY))
 (14 7 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (14 4 (:REWRITE ABNF::TREEP-OF-STRING-PARSABLEP-WITNESS-WHEN-STRING-UNAMBIGUOUSP))
 (14 2 (:REWRITE ABNF::NOT-PARSE-TREEP-WHEN-NOT-STRING-PARSABLEP))
 (12 12 (:REWRITE ABNF::STRING-UNAMBIGUOUSP-WHEN-PARSE-TREES-OF-STRING-P-OF-ONE))
 (10 10 (:TYPE-PRESCRIPTION ABNF::STRING-HAS-FINITE-PARSE-TREES-P))
 (10 4 (:REWRITE ABNF::TREEP-OF-STRING-PARSABLEP-WITNESS-WHEN-STRING-PARSABLEP))
 (8 8 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (8 8 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (8 8 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (6 6 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION ABNF::RULENAME-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (6 6 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE ABNF::STRING-IN-TERMSET-P-WHEN-NOT-CONSP))
 (6 1 (:REWRITE ABNF::RULELIST-IN-TERMSET-P-WHEN-NOT-CONSP))
 (5 1 (:REWRITE ABNF::NAT-LISTP-OF-TREE->STRING-WHEN-TERMINATED))
 (4 4 (:TYPE-PRESCRIPTION ABNF::TREEP))
 (4 4 (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (4 4 (:TYPE-PRESCRIPTION ABNF::PARSE-TREES-OF-STRING-P))
 (4 4 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (4 4 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE SET::LIST-IN-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE SET::IN-WHEN-MEMBER-EQUAL-OF-LIST-IN))
 (4 2 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-WHEN-STRING-UNAMBIGUOUSP))
 (4 2 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-WHEN-NOT-STRING-PARSABLEP))
 (4 2 (:REWRITE SET::LIST-IN-WHEN-NOT-CONSP))
 (4 2 (:REWRITE SET::IN-TAIL))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-TERMINATEDP))
 (2 2 (:TYPE-PRESCRIPTION NAT-LISTP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::TREE-SET-FIX-UNDER-TREE-SET-EQUIV))
 (2 2 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (2 2 (:REWRITE ABNF::STRING-IN-TERMSET-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::PARSE-TREES-OF-STRING-P-NECC))
 (2 2 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE ABNF::NAT-LISTP-OF-TREE->STRING-WHEN-MATCH-ELEMENT-NUM/CHAR-VAL))
 (1 1 (:REWRITE ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-NUM-VAL-IN-TERMSET))
 (1 1 (:REWRITE ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-ELEMENT-IN-TERMSET))
 (1 1 (:REWRITE ABNF::LEAVES-IN-TERMSET-WHEN-MATCH-CHAR-VAL-IN-TERMSET))
 )
