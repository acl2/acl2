(VL::EXIT-OK)
(VL::EXIT-FAIL)
(VL::MUST-BE-REGULAR-FILES!-FN)
(VL::STATE-P1-OF-MUST-BE-REGULAR-FILES!
 (361 3 (:DEFINITION SET::MERGESORT))
 (329 5 (:REWRITE SET::IN-MERGESORT-UNDER-IFF))
 (265 4 (:REWRITE SET::INSERT-IDENTITY))
 (173 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (139 1 (:DEFINITION SET::DIFFERENCE))
 (80 3 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (79 10 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (77 6 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (75 4 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (64 1 (:REWRITE SET::SUBSET-DIFFERENCE))
 (56 10 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (55 55 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 1 (:DEFINITION SET::SUBSET))
 (43 43 (:TYPE-PRESCRIPTION OSLIB::TRUE-LISTP-OF-REGULAR-FILES))
 (42 17 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (39 39 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (39 9 (:REWRITE DEFAULT-CAR))
 (36 3 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (34 21 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (33 13 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (33 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (28 6 (:REWRITE VL::SETP-OF-CDR))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 20 (:REWRITE DEFAULT-CDR))
 (22 3 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (20 20 (:TYPE-PRESCRIPTION OSLIB::TRUE-LISTP-OF-MISSING-PATHS))
 (17 17 (:REWRITE SET::IN-SET))
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (10 1 (:REWRITE MEMBER-WHEN-ATOM))
 (9 9 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (9 9 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (9 3 (:REWRITE SET::DIFFERENCE-EMPTYP-Y))
 (9 3 (:REWRITE SET::DIFFERENCE-EMPTYP-X))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 2 (:DEFINITION STATE-P))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET-2))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET))
 (4 4 (:TYPE-PRESCRIPTION SET::SUBSET-TYPE))
 (4 4 (:TYPE-PRESCRIPTION STATE-P))
 (4 4 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (4 4 (:REWRITE SET::SUBSET-TRANSITIVE))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 1 (:REWRITE SET::DIFFERENCE-IN))
 (3 3 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (3 3 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE SET::SUBSET-IN))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (1 1 (:REWRITE SUBSETP-MEMBER . 4))
 (1 1 (:REWRITE SUBSETP-MEMBER . 3))
 (1 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (1 1 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 (1 1 (:REWRITE SET::HEAD-UNIQUE))
 )
(VL::MUST-BE-DIRECTORIES!-FN)
(VL::STATE-P1-OF-MUST-BE-DIRECTORIES!
 (361 3 (:DEFINITION SET::MERGESORT))
 (329 5 (:REWRITE SET::IN-MERGESORT-UNDER-IFF))
 (265 4 (:REWRITE SET::INSERT-IDENTITY))
 (173 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (139 1 (:DEFINITION SET::DIFFERENCE))
 (80 3 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (79 10 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (77 6 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (75 4 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (64 1 (:REWRITE SET::SUBSET-DIFFERENCE))
 (56 10 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (55 55 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 1 (:DEFINITION SET::SUBSET))
 (43 43 (:TYPE-PRESCRIPTION OSLIB::TRUE-LISTP-OF-DIRECTORIES))
 (42 17 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (39 39 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (39 9 (:REWRITE DEFAULT-CAR))
 (36 3 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (34 21 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (33 13 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (33 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (28 6 (:REWRITE VL::SETP-OF-CDR))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 20 (:REWRITE DEFAULT-CDR))
 (22 3 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (20 20 (:TYPE-PRESCRIPTION OSLIB::TRUE-LISTP-OF-MISSING-PATHS))
 (17 17 (:REWRITE SET::IN-SET))
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (10 1 (:REWRITE MEMBER-WHEN-ATOM))
 (9 9 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (9 9 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (9 3 (:REWRITE SET::DIFFERENCE-EMPTYP-Y))
 (9 3 (:REWRITE SET::DIFFERENCE-EMPTYP-X))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 2 (:DEFINITION STATE-P))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET-2))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET))
 (4 4 (:TYPE-PRESCRIPTION SET::SUBSET-TYPE))
 (4 4 (:TYPE-PRESCRIPTION STATE-P))
 (4 4 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (4 4 (:REWRITE SET::SUBSET-TRANSITIVE))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 1 (:REWRITE SET::DIFFERENCE-IN))
 (3 3 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (3 3 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE SET::SUBSET-IN))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (1 1 (:REWRITE SUBSETP-MEMBER . 4))
 (1 1 (:REWRITE SUBSETP-MEMBER . 3))
 (1 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (1 1 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 (1 1 (:REWRITE SET::HEAD-UNIQUE))
 )
(VL::VL-PARSE-EDITION)
(VL::VL-EDITION-P-OF-VL-PARSE-EDITION.VALUE
 (28068 163 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-WEAK))
 (28024 22 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-STRONG))
 (24872 163 (:REWRITE STR::ICHARLISTEQV-WHEN-NOT-SAME-LENS))
 (9597 1078 (:LINEAR VL::LEN-OF-CDR-STRONG))
 (5255 5255 (:TYPE-PRESCRIPTION LEN))
 (4287 2297 (:REWRITE LEN-WHEN-ATOM))
 (2438 2438 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (2438 2438 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (2438 2438 (:LINEAR LEN-WHEN-PREFIXP))
 (1807 417 (:REWRITE STR::ICHAR<-TRICHOTOMY-WEAK))
 (1529 139 (:REWRITE STR::ICHAR<-TRICHOTOMY-STRONG))
 (1495 1495 (:REWRITE DEFAULT-CDR))
 (1269 141 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
 (1219 1219 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (1219 1219 (:LINEAR INDEX-OF-<-LEN))
 (1219 1219 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (930 930 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (886 886 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (717 717 (:TYPE-PRESCRIPTION GETOPT::STRINGP-OF-PARSE-STRING.VALUE))
 (592 163 (:DEFINITION NOT))
 (556 556 (:TYPE-PRESCRIPTION STR::ICHAR<$INLINE))
 (524 264 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (282 282 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (278 139 (:REWRITE STR::ICHAR<-ANTISYMMETRIC))
 (264 264 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (264 264 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (185 185 (:TYPE-PRESCRIPTION STR::ICHARLIST<))
 (139 139 (:TYPE-PRESCRIPTION STR::ICHAREQV$INLINE))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE-TWO))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE))
 (139 139 (:REWRITE DEFAULT-CAR))
 (139 139 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (132 22 (:REWRITE |(equal 0 (len x))|))
 (44 22 (:REWRITE STR::ICHARLIST<-ANTISYMMETRIC))
 (26 2 (:REWRITE STR::EXPLODE-UNDER-IFF))
 (22 22 (:REWRITE STR::ICHARLIST<-TRANSITIVE))
 (4 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 )
(VL::STRING-LISTP-OF-VL-PARSE-EDITION.REST-ARGS
 (28068 163 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-WEAK))
 (28024 22 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-STRONG))
 (24872 163 (:REWRITE STR::ICHARLISTEQV-WHEN-NOT-SAME-LENS))
 (9597 1078 (:LINEAR VL::LEN-OF-CDR-STRONG))
 (5255 5255 (:TYPE-PRESCRIPTION LEN))
 (4287 2297 (:REWRITE LEN-WHEN-ATOM))
 (2438 2438 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (2438 2438 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (2438 2438 (:LINEAR LEN-WHEN-PREFIXP))
 (1807 417 (:REWRITE STR::ICHAR<-TRICHOTOMY-WEAK))
 (1529 139 (:REWRITE STR::ICHAR<-TRICHOTOMY-STRONG))
 (1512 1497 (:REWRITE DEFAULT-CDR))
 (1269 141 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
 (1219 1219 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (1219 1219 (:LINEAR INDEX-OF-<-LEN))
 (1219 1219 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (950 950 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (906 906 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (717 717 (:TYPE-PRESCRIPTION GETOPT::STRINGP-OF-PARSE-STRING.VALUE))
 (530 265 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (282 282 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (278 139 (:REWRITE STR::ICHAR<-ANTISYMMETRIC))
 (265 265 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (265 265 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (185 185 (:TYPE-PRESCRIPTION STR::ICHARLIST<))
 (172 141 (:REWRITE DEFAULT-CAR))
 (141 141 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE-TWO))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE))
 (132 22 (:REWRITE |(equal 0 (len x))|))
 (108 4 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (84 2 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (61 2 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (44 22 (:REWRITE STR::ICHARLIST<-ANTISYMMETRIC))
 (32 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (32 2 (:REWRITE MEMBER-WHEN-ATOM))
 (26 2 (:REWRITE STR::EXPLODE-UNDER-IFF))
 (22 22 (:REWRITE STR::ICHARLIST<-TRANSITIVE))
 (19 2 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (17 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 2 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (10 2 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (9 9 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (9 9 (:REWRITE CONSP-BY-LEN))
 (8 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 2 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (7 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (3 3 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 4))
 (2 2 (:REWRITE SUBSETP-MEMBER . 3))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (2 2 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 3))
 (2 2 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(VL::VL-PARSE-EDITION-MAKES-PROGRESS
 (28068 163 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-WEAK))
 (28024 22 (:REWRITE STR::ICHARLIST<-TRICHOTOMY-STRONG))
 (24872 163 (:REWRITE STR::ICHARLISTEQV-WHEN-NOT-SAME-LENS))
 (9597 1078 (:LINEAR VL::LEN-OF-CDR-STRONG))
 (4323 2303 (:REWRITE LEN-WHEN-ATOM))
 (2446 2446 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (2446 2446 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (2446 2446 (:LINEAR LEN-WHEN-PREFIXP))
 (1807 417 (:REWRITE STR::ICHAR<-TRICHOTOMY-WEAK))
 (1529 139 (:REWRITE STR::ICHAR<-TRICHOTOMY-STRONG))
 (1495 1495 (:REWRITE DEFAULT-CDR))
 (1269 141 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
 (1223 1223 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (1223 1223 (:LINEAR INDEX-OF-<-LEN))
 (1223 1223 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (946 946 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (902 902 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (717 717 (:TYPE-PRESCRIPTION GETOPT::STRINGP-OF-PARSE-STRING.VALUE))
 (556 556 (:TYPE-PRESCRIPTION STR::ICHAR<$INLINE))
 (524 264 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (282 282 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (278 139 (:REWRITE STR::ICHAR<-ANTISYMMETRIC))
 (264 264 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (264 264 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (201 3 (:REWRITE LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (185 185 (:TYPE-PRESCRIPTION STR::ICHARLIST<))
 (165 1 (:REWRITE SUBLISTP-WHEN-PREFIXP))
 (139 139 (:TYPE-PRESCRIPTION STR::ICHAREQV$INLINE))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE-TWO))
 (139 139 (:REWRITE STR::ICHAR<-TRANSITIVE))
 (139 139 (:REWRITE DEFAULT-CAR))
 (139 139 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (132 22 (:REWRITE |(equal 0 (len x))|))
 (80 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
 (75 4 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (44 22 (:REWRITE STR::ICHARLIST<-ANTISYMMETRIC))
 (34 4 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (34 4 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (31 3 (:REWRITE LEN-WHEN-PREFIXP))
 (26 2 (:REWRITE STR::EXPLODE-UNDER-IFF))
 (22 22 (:REWRITE STR::ICHARLIST<-TRANSITIVE))
 (16 1 (:REWRITE SUBLISTP-WHEN-ATOM-RIGHT))
 (16 1 (:REWRITE SUBLISTP-WHEN-ATOM-LEFT))
 (11 11 (:TYPE-PRESCRIPTION PREFIXP))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE VL::PREFIXP-WHEN-MEMBER-EQUAL-OF-PREFIX-OF-EACHP))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (8 8 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (8 8 (:REWRITE CONSP-BY-LEN))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION SUBLISTP))
 (4 4 (:REWRITE VL::TRANSITIVITY-OF-PREFIXP))
 (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (4 4 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (4 4 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (4 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE SUBLISTP-COMPLETE))
 )
(VL::SPLIT-PLUSARGS-EXEC
 (1939 122 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (1232 30 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (977 137 (:REWRITE DEFAULT-CAR))
 (964 14 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (778 9 (:REWRITE SUBSETP-OF-CONS))
 (676 122 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (562 562 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (562 562 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (545 26 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (487 237 (:REWRITE DEFAULT-CDR))
 (443 84 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (408 16 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (363 60 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (357 12 (:REWRITE LEN-WHEN-ATOM))
 (324 16 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (315 133 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (281 66 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (275 275 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (260 26 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (257 60 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (212 16 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (194 29 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (192 192 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (182 182 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (177 12 (:REWRITE MEMBER-WHEN-ATOM))
 (170 16 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (137 137 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (133 133 (:REWRITE SET::IN-SET))
 (126 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (119 119 (:REWRITE SUBSETP-TRANS2))
 (119 119 (:REWRITE SUBSETP-TRANS))
 (102 3 (:REWRITE VL::NTH-WHEN-TOO-BIG))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (93 93 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (93 93 (:REWRITE CONSP-BY-LEN))
 (86 16 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (86 16 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (84 84 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (84 84 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (60 60 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (56 14 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (52 52 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (50 50 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (42 21 (:TYPE-PRESCRIPTION TRUE-LISTP-SUBSEQ))
 (40 40 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (32 32 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (29 29 (:REWRITE SUBSETP-MEMBER . 2))
 (29 29 (:REWRITE SUBSETP-MEMBER . 1))
 (28 28 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (28 28 (:TYPE-PRESCRIPTION ALISTP))
 (28 28 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (28 28 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (28 28 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (28 28 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (28 14 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (28 14 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (28 14 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (28 14 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (28 14 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (28 14 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (26 26 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (26 26 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 24 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP-SUBSEQ-TYPE-PRESCRIPTION))
 (21 21 (:TYPE-PRESCRIPTION STRINGP-SUBSEQ-TYPE-PRESCRIPTION))
 (21 3 (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (16 16 (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
 (14 14 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (14 14 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (14 14 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (14 14 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE ALISTP-WHEN-ATOM))
 (14 14 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (12 12 (:REWRITE SUBSETP-MEMBER . 4))
 (12 12 (:REWRITE SUBSETP-MEMBER . 3))
 (12 12 (:REWRITE INTERSECTP-MEMBER . 3))
 (12 12 (:REWRITE INTERSECTP-MEMBER . 2))
 (11 9 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE CDR-CONS))
 (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (4 4 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (3 3 (:REWRITE VL::NTH-OF-EXPLODE-WHEN-CHAR-FIX-KNOWN))
 (3 3 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE CAR-CONS))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(VL::STRING-LISTP-OF-SPLIT-PLUSARGS-EXEC.ACC
 (577 16 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (476 19 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (338 17 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (305 14 (:REWRITE LEN-WHEN-ATOM))
 (286 16 (:REWRITE STRINGP-OF-CAR-WHEN-STRING-LISTP))
 (271 44 (:REWRITE DEFAULT-CAR))
 (254 32 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (244 4 (:REWRITE VL::NTH-WHEN-TOO-BIG))
 (180 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (177 6 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (172 172 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (172 172 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (138 4 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (130 17 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (129 45 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (126 13 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (120 19 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (115 16 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (114 13 (:REWRITE MEMBER-WHEN-ATOM))
 (108 6 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (101 101 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (99 54 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (90 37 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (90 6 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (84 34 (:REWRITE DEFAULT-CDR))
 (74 74 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (72 6 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (62 19 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (57 16 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (53 53 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 13 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (52 4 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (47 47 (:REWRITE CONSP-BY-LEN))
 (45 45 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (45 45 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (44 44 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (43 13 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (42 42 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (38 38 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (38 13 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (37 37 (:REWRITE SET::IN-SET))
 (36 6 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (34 4 (:REWRITE STR::STRING-LIST-FIX-WHEN-ATOM))
 (26 26 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (26 26 (:TYPE-PRESCRIPTION ALISTP))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (23 23 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (22 13 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (21 3 (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (19 19 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (19 19 (:REWRITE FN-CHECK-DEF-FORMALS))
 (17 17 (:REWRITE SUBSETP-TRANS2))
 (17 17 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE SUBSETP-MEMBER . 2))
 (16 16 (:REWRITE SUBSETP-MEMBER . 1))
 (16 16 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (13 13 (:TYPE-PRESCRIPTION CONS-LISTP))
 (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (13 13 (:REWRITE SUBSETP-MEMBER . 4))
 (13 13 (:REWRITE SUBSETP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
 (13 13 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (13 13 (:REWRITE ALISTP-WHEN-ATOM))
 (12 12 (:TYPE-PRESCRIPTION VL::TRUE-LIST-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (12 12 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (12 12 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (12 12 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (12 6 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (12 6 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (12 6 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (10 10 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (9 3 (:REWRITE DEFAULT-<-2))
 (8 8 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (7 7 (:TYPE-PRESCRIPTION VL::ALL-HAVE-LEN))
 (6 6 (:TYPE-PRESCRIPTION VL::SYMBOL-LIST-LISTP))
 (6 6 (:TYPE-PRESCRIPTION VL::STRING-LIST-LISTP))
 (6 6 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION NAT-LISTP))
 (6 6 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
 (6 6 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (6 6 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION NFIX))
 (4 4 (:REWRITE VL::NTH-OF-EXPLODE-WHEN-CHAR-FIX-KNOWN))
 (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (4 4 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (3 3 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE VL::ALL-HAVE-LEN-WHEN-NOT-CONSP))
 )
(VL::STRING-LISTP-OF-SPLIT-PLUSARGS-EXEC.PLUSACC
 (577 16 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (476 19 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (338 17 (:REWRITE VL::SUBSETP-EQUAL-WHEN-FIRST-TWO-SAME-YADA-YADA))
 (305 14 (:REWRITE LEN-WHEN-ATOM))
 (286 16 (:REWRITE STRINGP-OF-CAR-WHEN-STRING-LISTP))
 (271 44 (:REWRITE DEFAULT-CAR))
 (254 32 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (244 4 (:REWRITE VL::NTH-WHEN-TOO-BIG))
 (180 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (177 6 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (172 172 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (172 172 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (138 4 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (130 17 (:REWRITE VL::SUBSETP-EQUAL-WHEN-CDR-ATOM))
 (129 45 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (126 13 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (120 19 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (115 16 (:REWRITE VL::PROMOTE-MEMBER-EQUAL-TO-MEMBERSHIP))
 (114 13 (:REWRITE MEMBER-WHEN-ATOM))
 (108 6 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (101 101 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (99 54 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (90 37 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (90 6 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (84 34 (:REWRITE DEFAULT-CDR))
 (74 74 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (72 6 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (62 19 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (57 16 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (53 53 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 13 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (52 4 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (47 47 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (47 47 (:REWRITE CONSP-BY-LEN))
 (45 45 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (45 45 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (44 44 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (43 13 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (42 42 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (38 38 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (38 13 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (37 37 (:REWRITE SET::IN-SET))
 (36 6 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (34 4 (:REWRITE STR::STRING-LIST-FIX-WHEN-ATOM))
 (26 26 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (26 26 (:TYPE-PRESCRIPTION ALISTP))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (23 23 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 (22 13 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (21 3 (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (19 19 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (19 19 (:REWRITE FN-CHECK-DEF-FORMALS))
 (17 17 (:REWRITE SUBSETP-TRANS2))
 (17 17 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE SUBSETP-MEMBER . 2))
 (16 16 (:REWRITE SUBSETP-MEMBER . 1))
 (16 16 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (13 13 (:TYPE-PRESCRIPTION CONS-LISTP))
 (13 13 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (13 13 (:REWRITE SUBSETP-MEMBER . 4))
 (13 13 (:REWRITE SUBSETP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
 (13 13 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (13 13 (:REWRITE ALISTP-WHEN-ATOM))
 (12 12 (:TYPE-PRESCRIPTION VL::TRUE-LIST-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (12 12 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (12 12 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (12 12 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (12 6 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (12 6 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (12 6 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (12 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (10 10 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (9 3 (:REWRITE DEFAULT-<-2))
 (8 8 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONGER))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (7 7 (:TYPE-PRESCRIPTION VL::ALL-HAVE-LEN))
 (6 6 (:TYPE-PRESCRIPTION VL::SYMBOL-LIST-LISTP))
 (6 6 (:TYPE-PRESCRIPTION VL::STRING-LIST-LISTP))
 (6 6 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION NAT-LISTP))
 (6 6 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LIST*P))
 (6 6 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (6 6 (:REWRITE TRUE-LISTP-WHEN-FUNCTION-SYMBOL-LISTP))
 (6 6 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (6 6 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION NFIX))
 (4 4 (:REWRITE VL::NTH-OF-EXPLODE-WHEN-CHAR-FIX-KNOWN))
 (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 4 (:LINEAR INDEX-OF-<-LEN))
 (4 4 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (3 3 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE VL::ALL-HAVE-LEN-WHEN-NOT-CONSP))
 )
(VL::SPLIT-PLUSARGS
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-REVERSE))
 (2 2 (:TYPE-PRESCRIPTION LISTP))
 (2 2 (:TYPE-PRESCRIPTION CONSP-REVERSE))
 )
(VL::STRING-LISTP-OF-SPLIT-PLUSARGS.NORMAL
 (32 2 (:REWRITE REV-WHEN-NOT-CONSP))
 (27 3 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (1 1 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 )
(VL::STRING-LISTP-OF-SPLIT-PLUSARGS.PLUSARGS
 (32 2 (:REWRITE REV-WHEN-NOT-CONSP))
 (27 3 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-TRUELIST-ALISTP . 1))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-KEYWORD-SYMBOL-ALISTP . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (1 1 (:REWRITE VL::STRING-LISTP-WHEN-SUBSET))
 )
