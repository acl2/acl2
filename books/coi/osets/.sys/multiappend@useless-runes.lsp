(SET::MULTIAPPEND)
(SET::MULTIAPPEND-SET
 (62 62 (:TYPE-PRESCRIPTION SET::MULTIAPPEND))
 (36 3 (:REWRITE SET::SFIX-SET-IDENTITY))
 (35 7 (:REWRITE SET::SETP-WHEN-LISTSETP-CHEAP))
 (27 27 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (22 7 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (14 14 (:TYPE-PRESCRIPTION SET::LISTSETP))
 (14 7 (:REWRITE SET::LISTSETP-WHEN-EMPTYP))
 (9 3 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (7 7 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE SET::EMPTYP-SFIX-CANCEL))
 (1 1 (:TYPE-PRESCRIPTION SET::SFIX))
 )
(SET::LISTSETP-OF-MULTIAPPEND
 (3900 48 (:DEFINITION SET::IN))
 (2743 25 (:DEFINITION SET::SUBSET))
 (2236 165 (:REWRITE SET::SETP-WHEN-LISTSETP-CHEAP))
 (1872 48 (:REWRITE SET::DOUBLE-CONTAINMENT-EXPENSIVE))
 (1674 4 (:REWRITE SET::ALL-IN-2<TRUE-LISTP>))
 (1616 134 (:REWRITE SET::ALL-IN<TRUE-LISTP>))
 (1415 145 (:REWRITE SET::IN-TAIL))
 (1399 65 (:DEFINITION TRUE-LISTP))
 (758 56 (:REWRITE SET::ALL-TAIL<TRUE-LISTP>))
 (708 4 (:REWRITE SET::ALL-IN-2-NOT<TRUE-LISTP>))
 (662 6 (:DEFINITION SET::ALL<NOT-TRUE-LISTP>))
 (618 9 (:REWRITE SET::SFIX-SET-IDENTITY))
 (616 134 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (588 290 (:REWRITE SET::SUBSET-IN))
 (385 165 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (351 351 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (334 142 (:REWRITE SET::ALL-EMPTYP<TRUE-LISTP>))
 (262 171 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (177 50 (:REWRITE SET::EMPTYP-SUBSET))
 (165 165 (:REWRITE SET::IN-SET))
 (148 8 (:REWRITE SET::ALL-TAIL-NOT<TRUE-LISTP>))
 (146 116 (:REWRITE SET::TAIL-PRESERVES-EMPTYP))
 (146 50 (:REWRITE SET::EMPTYP-SUBSET-2))
 (145 145 (:REWRITE SET::IN-WHEN-SUBSET-OF-FILTER<TRUE-LISTP>S))
 (137 133 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (134 134 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP))
 (134 134 (:REWRITE SET::ALL-LIST-MEMBER<TRUE-LISTP>))
 (133 133 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (117 57 (:REWRITE SET::LISTSETP-WHEN-EMPTYP))
 (100 100 (:REWRITE SET::SUBSET-TRANSITIVE))
 (73 73 (:REWRITE DEFAULT-CDR))
 (50 50 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (48 48 (:TYPE-PRESCRIPTION BOOLEANP))
 (46 46 (:REWRITE SET::ALL-LIST-MEMBER-NOT<TRUE-LISTP>))
 (46 46 (:REWRITE SET::ALL-IN-NOT<TRUE-LISTP>))
 (40 12 (:REWRITE SET::ALL-EMPTYP-NOT<TRUE-LISTP>))
 (36 36 (:TYPE-PRESCRIPTION SET::ALL-TYPE-NOT<TRUE-LISTP>))
 (27 9 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (25 25 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (14 4 (:REWRITE SET::NEVER-IN-EMPTY))
 (12 12 (:REWRITE SET::ALL-SUBSET-NOT<TRUE-LISTP>))
 (12 12 (:REWRITE SET::ALL-STRATEGY<NOT-TRUE-LISTP>))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE SET::SUBSET-IN-2))
 (6 3 (:REWRITE SET::EMPTYP-SFIX-CANCEL))
 (4 4 (:REWRITE SET::ALL-IN-2<INVERSEP<FIX>>))
 (4 4 (:REWRITE SET::ALL-IN-2-NOT<INVERSEP<FIX>>))
 (2 2 (:TYPE-PRESCRIPTION SET::MULTIAPPEND))
 (1 1 (:TYPE-PRESCRIPTION SET::SFIX))
 )
(SET::MULTIAPPEND-2-INDUCTION
 (8 8 (:TYPE-PRESCRIPTION SET::SFIX))
 )
(SET::MULTIAPPEND-IN
 (26345 114 (:DEFINITION SET::IN))
 (19216 177 (:REWRITE SET::ALL-IN-2-NOT<TRUE-LISTP>))
 (18544 177 (:REWRITE SET::ALL-IN-2<TRUE-LISTP>))
 (17479 228 (:DEFINITION SET::ALL<NOT-TRUE-LISTP>))
 (16667 248 (:DEFINITION SET::ALL<TRUE-LISTP>))
 (16653 655 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (8620 508 (:DEFINITION TRUE-LISTP))
 (8121 1016 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (7251 25 (:REWRITE LIST::NTHCDR-WHEN-<=))
 (7185 24 (:REWRITE LIST::NTHCDR-OF-LEN-OR-MORE))
 (6773 325 (:REWRITE SET::ALL-TAIL-NOT<TRUE-LISTP>))
 (5865 355 (:REWRITE SET::ALL-TAIL<TRUE-LISTP>))
 (5456 203 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4914 356 (:REWRITE SET::IN-TAIL))
 (4800 4800 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4781 95 (:LINEAR LIST::LEN-OF-CDR-LINEAR))
 (4664 4661 (:REWRITE DEFAULT-CDR))
 (3951 95 (:LINEAR LIST::LEN-OF-CDR-BOUND-WEAK-LINEAR))
 (3831 95 (:LINEAR LIST::LEN-OF-CDR-BOUND-TIGHT-LINEAR))
 (3698 1849 (:REWRITE DEFAULT-+-2))
 (3490 65 (:DEFINITION SET::SUBSET))
 (2962 2962 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2775 1164 (:REWRITE SET::SETP-WHEN-LISTSETP-CHEAP))
 (2526 2526 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (2471 134 (:REWRITE SET::DOUBLE-CONTAINMENT-EXPENSIVE))
 (2444 1153 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2320 144 (:LINEAR LIST::LEN-NON-NEGATIVE-LINEAR))
 (1849 1849 (:REWRITE DEFAULT-+-1))
 (1581 500 (:REWRITE SET::ALL-EMPTYP<TRUE-LISTP>))
 (1526 1526 (:TYPE-PRESCRIPTION SET::ALL-TYPE<TRUE-LISTP>))
 (1451 460 (:REWRITE SET::ALL-EMPTYP-NOT<TRUE-LISTP>))
 (1406 1406 (:TYPE-PRESCRIPTION SET::ALL-TYPE-NOT<TRUE-LISTP>))
 (1356 452 (:TYPE-PRESCRIPTION LIST::TRUE-LISTP-OF-NTHCDR-TYPE-PRESCRIPTION))
 (1313 1313 (:TYPE-PRESCRIPTION SET::LISTSETP))
 (1289 1195 (:REWRITE SET::TAIL-PRESERVES-EMPTYP))
 (1074 790 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (1019 1019 (:REWRITE LIST::TRUE-LISTP-OF-NON-CONSP))
 (1016 1016 (:REWRITE SET::ALL-LIST-MEMBER<TRUE-LISTP>))
 (1016 1016 (:REWRITE SET::ALL-IN<TRUE-LISTP>))
 (928 144 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (904 452 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (655 655 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (634 170 (:REWRITE SET::NEVER-IN-EMPTY))
 (567 18 (:REWRITE LIST::TRUE-LISTP-FIX))
 (500 500 (:REWRITE SET::ALL-SUBSET<TRUE-LISTP>))
 (500 500 (:REWRITE SET::ALL-STRATEGY<TRUE-LISTP>))
 (460 460 (:REWRITE SET::ALL-SUBSET-NOT<TRUE-LISTP>))
 (460 460 (:REWRITE SET::ALL-STRATEGY<NOT-TRUE-LISTP>))
 (456 456 (:REWRITE SET::ALL-LIST-MEMBER-NOT<TRUE-LISTP>))
 (456 456 (:REWRITE SET::ALL-IN-NOT<TRUE-LISTP>))
 (407 101 (:REWRITE SET::EMPTYP-SUBSET-2))
 (397 397 (:REWRITE SET::IN-WHEN-SUBSET-OF-FILTER<TRUE-LISTP>S))
 (383 13 (:REWRITE LIST::EQUIV-OF-TWO-TRUE-LISTPS))
 (298 149 (:REWRITE SET::LISTSETP-WHEN-EMPTYP))
 (222 13 (:REWRITE LIST::EQUAL-CAR-DIFFERENTIAL))
 (200 200 (:REWRITE SET::SUBSET-TRANSITIVE))
 (182 92 (:REWRITE DEFAULT-<-1))
 (181 13 (:REWRITE LIST::EQUIV-OF-NON-CONSP-TWO))
 (177 177 (:REWRITE SET::ALL-IN-2<INVERSEP<FIX>>))
 (177 177 (:REWRITE SET::ALL-IN-2-NOT<INVERSEP<FIX>>))
 (159 92 (:REWRITE DEFAULT-<-2))
 (143 143 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (143 143 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (136 101 (:REWRITE SET::EMPTYP-SUBSET))
 (127 127 (:TYPE-PRESCRIPTION BOOLEANP))
 (122 2 (:REWRITE SET::ALL-SFIX-NOT<TRUE-LISTP>))
 (114 2 (:REWRITE SET::ALL-SFIX<TRUE-LISTP>))
 (100 100 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (96 12 (:REWRITE LIST::CONSP-FIRSTN))
 (87 84 (:REWRITE DEFAULT-CAR))
 (65 65 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (58 4 (:REWRITE LIST::LEN-CONS))
 (56 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (51 17 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (34 34 (:REWRITE SET::HEAD-UNIQUE))
 (28 28 (:TYPE-PRESCRIPTION ZP))
 (14 7 (:REWRITE SET::EMPTYP-SFIX-CANCEL))
 (13 13 (:REWRITE LIST::OPEN-EQUIV))
 (13 13 (:REWRITE LIST::EQUIV-OF-NON-CONSP-ONE))
 (13 13 (:REWRITE LIST::EQUIV-OF-CONSTANT))
 (13 13 (:REWRITE LIST::CARS-MATCH-FROM-FIRSTN-FACT-2))
 (13 13 (:REWRITE LIST::CARS-MATCH-FROM-FIRSTN-FACT))
 (4 1 (:REWRITE SET::TAIL-SFIX-CANCEL))
 )
