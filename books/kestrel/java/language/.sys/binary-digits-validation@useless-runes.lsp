(JAVA::GRAMMAR-BIN-DIGITP)
(JAVA::GRAMMAR-BIN-DIGITP-SUFF)
(JAVA::BOOLEANP-OF-GRAMMAR-BIN-DIGITP)
(JAVA::GRAMMAR-BIN-DIGITP)
(JAVA::SINGLETON-WHEN-GRAMMAR-BIN-DIGITP
 (117 18 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (116 114 (:REWRITE DEFAULT-CAR))
 (114 114 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (92 12 (:REWRITE ABNF::TREE-TERMINATEDP-OF-CAR-WHEN-TREE-LIST-TERMINATEDP))
 (90 9 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (76 20 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-OF-CAR-WHEN-TREE-LIST-LIST-TERMINATEDP))
 (50 48 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (40 40 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (38 38 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (36 36 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (34 34 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (27 27 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (22 17 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (22 17 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (20 20 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (20 20 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (18 18 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (18 18 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (18 18 (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (15 6 (:REWRITE LEN-WHEN-ATOM))
 (14 9 (:REWRITE ABNF::TREE-LIST-LIST->STRING-WHEN-ATOM))
 (12 2 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-OF-CAR-WHEN-TREE-LIST-MATCH-ELEMENT-P))
 (8 8 (:REWRITE ABNF::TREE-LIST->STRING-WHEN-ATOM))
 (6 6 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (4 4 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-MATCH-ELEMENT-P))
 (4 4 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (4 4 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (4 4 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE JAVA::ABNF-TREE-WITH-ROOT-P-WHEN-MEMBER-EQUAL-OF-ABNF-TREE-LIST-WITH-ROOT-P))
 (2 2 (:LINEAR INDEX-OF-<-LEN))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (1 1 (:REWRITE JAVA::GRAMMAR-BIN-DIGITP-SUFF))
 )
(JAVA::BIN-DIGIT-TREE
 (1 1 (:TYPE-PRESCRIPTION JAVA::BIN-DIGIT-FIX))
 )
(JAVA::RETURN-TYPE-OF-BIN-DIGIT-TREE
 (12 2 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (10 2 (:REWRITE JAVA::BIN-DIGIT-FIX-WHEN-BIN-DIGITP))
 (8 8 (:REWRITE JAVA::BIN-DIGITP-WHEN-MEMBER-EQUAL-OF-BIN-DIGIT-LISTP))
 (6 2 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (4 4 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (4 4 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (4 4 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (3 3 (:REWRITE-QUOTED-CONSTANT ABNF::TREE-LIST-LIST-FIX-UNDER-TREE-LIST-LIST-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT ABNF::TREE-LIST-FIX-UNDER-TREE-LIST-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:TYPE-PRESCRIPTION JAVA::BIN-DIGITP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULENAME-OPTION-FIX-UNDER-RULENAME-OPTION-EQUIV))
 (2 2 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (2 2 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (2 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LIST-TERMINATEDP))
 (2 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (2 2 (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::ELEMENT-FIX-UNDER-ELEMENT-EQUIV))
 (1 1 (:REWRITE ABNF::TREE-NONLEAF->RULENAME?-OF-TREE-NONLEAF))
 (1 1 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ABNF::TREE-LIST-TERMINATEDP-WHEN-ATOM))
 (1 1 (:REWRITE ABNF::TREE-LIST-LIST-MATCH-ALTERNATION-P-WHEN-ATOM-ALTERNATION))
 )
(JAVA::TREE->STRING-OF-BIN-DIGIT-TREE
 (6 6 (:REWRITE JAVA::BIN-DIGITP-WHEN-MEMBER-EQUAL-OF-BIN-DIGIT-LISTP))
 (6 2 (:REWRITE JAVA::BIN-DIGIT-FIX-WHEN-BIN-DIGITP))
 (6 1 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (3 1 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (2 2 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::TREE-LIST-LIST-FIX-UNDER-TREE-LIST-LIST-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::TREE-LIST-FIX-UNDER-TREE-LIST-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT NAT-LIST-FIX-UNDER-NAT-LIST-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION JAVA::BIN-DIGITP))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::RULENAME-OPTION-FIX-UNDER-RULENAME-OPTION-EQUIV))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (1 1 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE ABNF::TREE-LIST-LIST->STRING-WHEN-ATOM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 )
(JAVA::BIN-DIGIT-TREE-OF-BIN-DIGIT-FIX-DIGIT)
(JAVA::BIN-DIGIT-TREE-BIN-DIGIT-EQUIV-CONGRUENCE-ON-DIGIT)
(JAVA::GRAMMAR-BIN-DIGITP-WHEN-BIN-DIGITP)
(JAVA::LEMMA
 (825 552 (:REWRITE DEFAULT-CDR))
 (759 457 (:REWRITE DEFAULT-CAR))
 (672 32 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (576 32 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (560 31 (:REWRITE ABNF::RULENAME-OPTIONP-WHEN-RULENAMEP))
 (457 457 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (338 23 (:REWRITE ABNF::RULENAMEP-OF-CAR-WHEN-RULENAME-LISTP))
 (216 26 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-PSEUDOEVENTFORM-ALISTP . 2))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-PSEUDOEVENTFORM-ALISTP . 1))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (173 173 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-NUMRANGE-INFO-ALISTP . 2))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-NUMRANGE-INFO-ALISTP . 1))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-CHARVAL-INFO-ALISTP . 2))
 (173 173 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-CHARVAL-INFO-ALISTP . 1))
 (173 173 (:REWRITE CONSP-BY-LEN))
 (166 23 (:REWRITE ABNF::RULENAMEP-WHEN-RULENAME-OPTIONP))
 (160 19 (:REWRITE ABNF::RULENAME-LISTP-OF-CDR-WHEN-RULENAME-LISTP))
 (154 11 (:REWRITE JAVA::BIN-DIGITP-OF-CAR-WHEN-BIN-DIGIT-LISTP))
 (148 8 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (146 50 (:REWRITE LEN-WHEN-ATOM))
 (144 20 (:REWRITE ABNF::TREEP-OF-CAR-WHEN-TREE-LISTP))
 (136 38 (:REWRITE ABNF::RULENAME-LISTP-WHEN-NOT-CONSP))
 (132 4 (:DEFINITION INTEGER-LISTP))
 (104 4 (:REWRITE NAT-LIST-FIX-WHEN-NAT-LISTP))
 (92 30 (:REWRITE ABNF::TREE-LISTP-OF-CAR-WHEN-TREE-LIST-LISTP))
 (90 90 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (90 90 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (90 90 (:LINEAR LEN-WHEN-PREFIXP))
 (88 8 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (80 4 (:REWRITE ABNF::TREE-LIST-LIST-FIX-UNDER-IFF))
 (76 76 (:REWRITE ABNF::RULENAME-LISTP-WHEN-SUBSETP-EQUAL))
 (72 72 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (68 68 (:REWRITE ABNF::TREE-LISTP-WHEN-SUBSETP-EQUAL))
 (68 68 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (68 68 (:REWRITE ABNF::TREE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (66 11 (:REWRITE JAVA::BIN-DIGIT-LISTP-WHEN-NOT-CONSP))
 (64 64 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (64 64 (:REWRITE TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (64 64 (:REWRITE TRUE-LISTP-OF-CDR-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP))
 (64 32 (:REWRITE ABNF::SETP-WHEN-TREE-SETP))
 (64 32 (:REWRITE ABNF::SETP-WHEN-RULENAME-SETP))
 (64 32 (:REWRITE ABNF::SETP-WHEN-NUM-RANGE-SETP))
 (64 32 (:REWRITE SET::SETP-WHEN-NAT-SETP))
 (64 32 (:REWRITE SET::SETP-WHEN-INTEGER-SETP))
 (64 32 (:REWRITE ABNF::SETP-WHEN-CHAR-VAL-SETP))
 (64 32 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (60 60 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (60 10 (:REWRITE TRUE-LISTP-OF-CDAR-WHEN-KEYWORD-TRUELIST-ALISTP))
 (60 10 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-NOT-CONSP))
 (60 10 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-ATOM))
 (52 52 (:TYPE-PRESCRIPTION ABNF::RULENAMEP))
 (46 46 (:REWRITE ABNF::RULENAMEP-WHEN-MEMBER-EQUAL-OF-RULENAME-LISTP))
 (46 46 (:REWRITE ABNF::RULENAMEP-OF-CAR-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP))
 (45 45 (:LINEAR INDEX-OF-<-LEN))
 (34 34 (:REWRITE JAVA::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (32 32 (:TYPE-PRESCRIPTION ABNF::TREE-SETP))
 (32 32 (:TYPE-PRESCRIPTION ABNF::RULENAME-SETP))
 (32 32 (:TYPE-PRESCRIPTION ABNF::NUM-RANGE-SETP))
 (32 32 (:TYPE-PRESCRIPTION SET::NAT-SETP))
 (32 32 (:TYPE-PRESCRIPTION SET::INTEGER-SETP))
 (32 32 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (32 32 (:TYPE-PRESCRIPTION ABNF::CHAR-VAL-SETP))
 (32 32 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (32 32 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (32 32 (:REWRITE JAVA::TRUE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (32 32 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (32 32 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (32 32 (:REWRITE SET::IN-SET))
 (32 32 (:REWRITE JAVA::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (32 8 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP))
 (28 4 (:REWRITE LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (26 26 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (24 4 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-OF-CAR-WHEN-TREE-LIST-MATCH-ELEMENT-P))
 (23 23 (:REWRITE ABNF::RULENAMEP-WHEN-IN-RULENAME-SETP-BINDS-FREE-X))
 (22 22 (:REWRITE JAVA::BIN-DIGITP-WHEN-MEMBER-EQUAL-OF-BIN-DIGIT-LISTP))
 (22 22 (:REWRITE JAVA::BIN-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE ABNF::TREE-LIST-LIST-TERMINATEDP-WHEN-SUBSETP-EQUAL))
 (20 20 (:REWRITE KEYWORD-TRUELIST-ALISTP-WHEN-SUBSETP-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-LIST-FIX$INLINE))
 (10 10 (:REWRITE ABNF::TREE-TERMINATEDP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-TERMINATEDP))
 (10 10 (:REWRITE ABNF::TREE-MATCH-ELEMENT-P-WHEN-MEMBER-EQUAL-OF-TREE-LIST-MATCH-ELEMENT-P))
 (10 10 (:REWRITE KEYWORD-TRUELIST-ALISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION ABNF::TREE-LIST-MATCH-ELEMENT-P))
 (8 8 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (8 8 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-SUBSETP-EQUAL))
 (8 4 (:REWRITE ABNF::TREE-LIST-LISTP-OF-CDR-WHEN-TREE-LIST-LISTP))
 (8 4 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (5 5 (:REWRITE ABNF::RULENAME-OPTION-FIX-WHEN-NONE))
 (5 5 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (4 4 (:REWRITE ABNF::TREE-LIST-MATCH-ELEMENT-P-WHEN-NOT-CONSP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE-QUOTED-CONSTANT ABNF::RULELIST-FIX-UNDER-RULELIST-EQUIV))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::ELEMENT-FIX-UNDER-ELEMENT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT ABNF::ALTERNATION-FIX-UNDER-ALTERNATION-EQUIV))
 )
(JAVA::BIN-DIGITP-WHEN-GRAMMAR-BIN-DIGITP
 (72 3 (:REWRITE JAVA::BIN-DIGITP-OF-CAR-WHEN-BIN-DIGIT-LISTP))
 (54 3 (:REWRITE DEFAULT-CAR))
 (54 3 (:REWRITE JAVA::BIN-DIGIT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION JAVA::BIN-DIGIT-LISTP))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-PSEUDOEVENTFORM-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-PSEUDOEVENTFORM-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOLLIST-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-STRING-SYMBOL-ALISTP . 1))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 2))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-RULENAME-INFO-ALISTP . 1))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-NUMRANGE-INFO-ALISTP . 2))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-NUMRANGE-INFO-ALISTP . 1))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-CHARVAL-INFO-ALISTP . 2))
 (6 6 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-DEFTREEOPS-CHARVAL-INFO-ALISTP . 1))
 (6 6 (:REWRITE JAVA::BIN-DIGITP-WHEN-MEMBER-EQUAL-OF-BIN-DIGIT-LISTP))
 (6 6 (:REWRITE JAVA::BIN-DIGIT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE JAVA::ABNF-TREE-WITH-ROOT-P-WHEN-MEMBER-EQUAL-OF-ABNF-TREE-LIST-WITH-ROOT-P))
 )
(JAVA::BIN-DIGITP-IS-GRAMMAR-BIN-DIGITP
 (2 2 (:REWRITE JAVA::BIN-DIGITP-WHEN-MEMBER-EQUAL-OF-BIN-DIGIT-LISTP))
 )
