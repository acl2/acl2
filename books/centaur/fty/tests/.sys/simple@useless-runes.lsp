(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(FTY::STUDENT-P
 (40 10 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-CAR))
 )
(FTY::CONSP-WHEN-STUDENT-P)
(FTY::TAG-WHEN-STUDENT-P)
(FTY::STUDENT-P-WHEN-WRONG-TAG)
(FTY::STUDENT-FIX$INLINE)
(FTY::STUDENT-P-OF-STUDENT-FIX
 (14 6 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::STUDENT-FIX-WHEN-STUDENT-P
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::STUDENT-FIX$INLINE
 (105 21 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (91 90 (:REWRITE DEFAULT-CDR))
 (71 70 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(FTY::STUDENT-EQUIV$INLINE)
(FTY::STUDENT-EQUIV-IS-AN-EQUIVALENCE)
(FTY::STUDENT-EQUIV-IMPLIES-EQUAL-STUDENT-FIX-1)
(FTY::STUDENT-FIX-UNDER-STUDENT-EQUIV)
(FTY::EQUAL-OF-STUDENT-FIX-1-FORWARD-TO-STUDENT-EQUIV)
(FTY::EQUAL-OF-STUDENT-FIX-2-FORWARD-TO-STUDENT-EQUIV)
(FTY::STUDENT-EQUIV-OF-STUDENT-FIX-1-FORWARD)
(FTY::STUDENT-EQUIV-OF-STUDENT-FIX-2-FORWARD)
(FTY::TAG-OF-STUDENT-FIX)
(FTY::STUDENT->NAME$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::STRINGP-OF-STUDENT->NAME)
(FTY::STUDENT->NAME$INLINE-OF-STUDENT-FIX-X
 (9 3 (:REWRITE FTY::STUDENT-FIX-WHEN-STUDENT-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::STUDENT->NAME$INLINE-STUDENT-EQUIV-CONGRUENCE-ON-X)
(FTY::STUDENT->AGE$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(FTY::NATP-OF-STUDENT->AGE)
(FTY::STUDENT->AGE$INLINE-OF-STUDENT-FIX-X
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (9 3 (:REWRITE FTY::STUDENT-FIX-WHEN-STUDENT-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT-FIX$INLINE))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::STUDENT->AGE$INLINE-STUDENT-EQUIV-CONGRUENCE-ON-X)
(FTY::STUDENT)
(FTY::STUDENT-P-OF-STUDENT
 (8 4 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::STUDENT->NAME-OF-STUDENT
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT))
 )
(FTY::STUDENT->AGE-OF-STUDENT
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION FTY::STUDENT))
 )
(FTY::STUDENT-OF-FIELDS
 (3 1 (:REWRITE FTY::STUDENT-FIX-WHEN-STUDENT-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::STUDENT-FIX-WHEN-STUDENT
 (3 1 (:REWRITE FTY::STUDENT-FIX-WHEN-STUDENT-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::EQUAL-OF-STUDENT
 (24 24 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::STUDENT-OF-STR-FIX-NAME
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::STUDENT-STREQV-CONGRUENCE-ON-NAME)
(FTY::STUDENT-OF-NFIX-AGE
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::STUDENT-NAT-EQUIV-CONGRUENCE-ON-AGE)
(FTY::STUDENT-FIX-REDEF)
(FTY::TAG-OF-STUDENT)
(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(FTY::TEACHER-P
 (40 10 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-CAR))
 )
(FTY::CONSP-WHEN-TEACHER-P)
(FTY::TAG-WHEN-TEACHER-P)
(FTY::TEACHER-P-WHEN-WRONG-TAG)
(FTY::TEACHER-FIX$INLINE)
(FTY::TEACHER-P-OF-TEACHER-FIX
 (14 6 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::TEACHER-FIX-WHEN-TEACHER-P
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TEACHER-FIX$INLINE
 (105 21 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (91 90 (:REWRITE DEFAULT-CDR))
 (71 70 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(FTY::TEACHER-EQUIV$INLINE)
(FTY::TEACHER-EQUIV-IS-AN-EQUIVALENCE)
(FTY::TEACHER-EQUIV-IMPLIES-EQUAL-TEACHER-FIX-1)
(FTY::TEACHER-FIX-UNDER-TEACHER-EQUIV)
(FTY::EQUAL-OF-TEACHER-FIX-1-FORWARD-TO-TEACHER-EQUIV)
(FTY::EQUAL-OF-TEACHER-FIX-2-FORWARD-TO-TEACHER-EQUIV)
(FTY::TEACHER-EQUIV-OF-TEACHER-FIX-1-FORWARD)
(FTY::TEACHER-EQUIV-OF-TEACHER-FIX-2-FORWARD)
(FTY::TAG-OF-TEACHER-FIX)
(FTY::TEACHER->NAME$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::STRINGP-OF-TEACHER->NAME)
(FTY::TEACHER->NAME$INLINE-OF-TEACHER-FIX-X
 (9 3 (:REWRITE FTY::TEACHER-FIX-WHEN-TEACHER-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::TEACHER->NAME$INLINE-TEACHER-EQUIV-CONGRUENCE-ON-X)
(FTY::TEACHER->GRADE$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(FTY::NATP-OF-TEACHER->GRADE)
(FTY::TEACHER->GRADE$INLINE-OF-TEACHER-FIX-X
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (9 3 (:REWRITE FTY::TEACHER-FIX-WHEN-TEACHER-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER-FIX$INLINE))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::TEACHER->GRADE$INLINE-TEACHER-EQUIV-CONGRUENCE-ON-X)
(FTY::TEACHER)
(FTY::TEACHER-P-OF-TEACHER
 (8 4 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::TEACHER->NAME-OF-TEACHER
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER))
 )
(FTY::TEACHER->GRADE-OF-TEACHER
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION FTY::TEACHER))
 )
(FTY::TEACHER-OF-FIELDS
 (3 1 (:REWRITE FTY::TEACHER-FIX-WHEN-TEACHER-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::TEACHER-FIX-WHEN-TEACHER
 (3 1 (:REWRITE FTY::TEACHER-FIX-WHEN-TEACHER-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::EQUAL-OF-TEACHER
 (24 24 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::TEACHER-OF-STR-FIX-NAME
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FTY::TEACHER-STREQV-CONGRUENCE-ON-NAME)
(FTY::TEACHER-OF-NFIX-GRADE
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::TEACHER-NAT-EQUIV-CONGRUENCE-ON-GRADE)
(FTY::TEACHER-FIX-REDEF)
(FTY::TAG-OF-TEACHER)
(FTY::PERSON-P
 (8 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(FTY::CONSP-WHEN-PERSON-P)
(FTY::PERSON-P-WHEN-STUDENT-P
 (6 2 (:REWRITE FTY::STUDENT-P-WHEN-WRONG-TAG))
 (4 2 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 )
(FTY::PERSON-P-WHEN-TEACHER-P
 (6 2 (:REWRITE FTY::TEACHER-P-WHEN-WRONG-TAG))
 (2 1 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 )
(FTY::STUDENT-P-BY-TAG-WHEN-PERSON-P)
(FTY::TEACHER-P-BY-TAG-WHEN-PERSON-P)
(FTY::PERSON-P-WHEN-INVALID-TAG
 (6 3 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (6 3 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (1 1 (:REWRITE FTY::TEACHER-P-BY-TAG-WHEN-PERSON-P))
 )
(FTY::TAG-WHEN-PERSON-P-FORWARD)
(FTY::PERSON-FIX$INLINE)
(FTY::PERSON-P-OF-PERSON-FIX
 (54 3 (:REWRITE FTY::STUDENT-FIX-WHEN-STUDENT-P))
 (30 15 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (26 13 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (24 3 (:REWRITE FTY::TEACHER-FIX-WHEN-TEACHER-P))
 (12 6 (:REWRITE FTY::PERSON-P-WHEN-TEACHER-P))
 (12 6 (:REWRITE FTY::PERSON-P-WHEN-STUDENT-P))
 (5 1 (:REWRITE FTY::TEACHER-P-WHEN-WRONG-TAG))
 (1 1 (:REWRITE FTY::STUDENT-P-WHEN-WRONG-TAG))
 )
(FTY::PERSON-FIX-WHEN-PERSON-P
 (8 2 (:REWRITE FTY::STUDENT-P-BY-TAG-WHEN-PERSON-P))
 (6 2 (:REWRITE FTY::PERSON-P-WHEN-TEACHER-P))
 (6 2 (:REWRITE FTY::PERSON-P-WHEN-STUDENT-P))
 (2 2 (:REWRITE FTY::TEACHER-P-BY-TAG-WHEN-PERSON-P))
 (1 1 (:REWRITE FTY::PERSON-P-WHEN-INVALID-TAG))
 )
(FTY::PERSON-FIX$INLINE
 (8 2 (:REWRITE FTY::STUDENT-P-BY-TAG-WHEN-PERSON-P))
 (6 2 (:REWRITE FTY::PERSON-P-WHEN-TEACHER-P))
 (6 2 (:REWRITE FTY::PERSON-P-WHEN-STUDENT-P))
 (2 2 (:REWRITE FTY::TEACHER-P-BY-TAG-WHEN-PERSON-P))
 (1 1 (:REWRITE FTY::PERSON-P-WHEN-INVALID-TAG))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (4 1 (:REWRITE FTY::PERSON-P-WHEN-TEACHER-P))
 (4 1 (:REWRITE FTY::PERSON-P-WHEN-STUDENT-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (1 1 (:REWRITE FTY::TEACHER-P-BY-TAG-WHEN-PERSON-P))
 (1 1 (:REWRITE FTY::STUDENT-P-BY-TAG-WHEN-PERSON-P))
 )
(FTY::PERSON-EQUIV$INLINE)
(FTY::PERSON-EQUIV-IS-AN-EQUIVALENCE)
(FTY::PERSON-EQUIV-IMPLIES-EQUAL-PERSON-FIX-1)
(FTY::PERSON-FIX-UNDER-PERSON-EQUIV)
(FTY::EQUAL-OF-PERSON-FIX-1-FORWARD-TO-PERSON-EQUIV)
(FTY::EQUAL-OF-PERSON-FIX-2-FORWARD-TO-PERSON-EQUIV)
(FTY::PERSON-EQUIV-OF-PERSON-FIX-1-FORWARD)
(FTY::PERSON-EQUIV-OF-PERSON-FIX-2-FORWARD)
(FTY::TAG-OF-PERSON-FIX-FORWARD)
(TMP-DEFTYPES-INTEGERP-OF-IFIX)
(TMP-DEFTYPES-IFIX-WHEN-INTEGERP)
(TMP-DEFTYPES-BOOLEANP-OF-BOOL-FIX$INLINE)
(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(FTY::CANDY-P)
(FTY::CONSP-WHEN-CANDY-P)
(FTY::CANDY-KIND$INLINE)
(FTY::CANDY-KIND-POSSIBILITIES)
(FTY::CANDY-FIX$INLINE)
(FTY::CANDY-P-OF-CANDY-FIX
 (12 4 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE STR-FIX-WHEN-STRINGP))
 (4 4 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(FTY::CANDY-FIX-WHEN-CANDY-P)
(FTY::CANDY-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(FTY::CANDY-EQUIV$INLINE)
(FTY::CANDY-EQUIV-IS-AN-EQUIVALENCE)
(FTY::CANDY-EQUIV-IMPLIES-EQUAL-CANDY-FIX-1)
(FTY::CANDY-FIX-UNDER-CANDY-EQUIV)
(FTY::EQUAL-OF-CANDY-FIX-1-FORWARD-TO-CANDY-EQUIV)
(FTY::EQUAL-OF-CANDY-FIX-2-FORWARD-TO-CANDY-EQUIV)
(FTY::CANDY-EQUIV-OF-CANDY-FIX-1-FORWARD)
(FTY::CANDY-EQUIV-OF-CANDY-FIX-2-FORWARD)
(FTY::CANDY-KIND$INLINE-OF-CANDY-FIX-X
 (14 14 (:REWRITE STR-FIX-WHEN-STRINGP))
 (9 9 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (7 5 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 )
(FTY::CANDY-KIND$INLINE-CANDY-EQUIV-CONGRUENCE-ON-X)
(FTY::CONSP-OF-CANDY-FIX)
(FTY::TAG-WHEN-CANDY-P-FORWARD)
(FTY::TAG-OF-CANDY-FIX)
(FTY::CANDY-CHOCOLATE->DARKNESS$INLINE)
(FTY::INTEGERP-OF-CANDY-CHOCOLATE->DARKNESS)
(FTY::CANDY-CHOCOLATE->DARKNESS$INLINE-OF-CANDY-FIX-X
 (13 5 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (9 9 (:TYPE-PRESCRIPTION FTY::CONSP-OF-CANDY-FIX))
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-FIX$INLINE))
 (8 8 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-CHOCOLATE->DARKNESS$INLINE-CANDY-EQUIV-CONGRUENCE-ON-X)
(FTY::CANDY-CHOCOLATE->DARKNESS-WHEN-WRONG-KIND
 (2 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(FTY::CANDY-CHOCOLATE->MAKER$INLINE)
(FTY::STRINGP-OF-CANDY-CHOCOLATE->MAKER)
(FTY::CANDY-CHOCOLATE->MAKER$INLINE-OF-CANDY-FIX-X
 (13 5 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (9 9 (:TYPE-PRESCRIPTION FTY::CONSP-OF-CANDY-FIX))
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-FIX$INLINE))
 (8 8 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 (2 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(FTY::CANDY-CHOCOLATE->MAKER$INLINE-CANDY-EQUIV-CONGRUENCE-ON-X)
(FTY::CANDY-CHOCOLATE->MAKER-WHEN-WRONG-KIND
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-CHOCOLATE)
(FTY::RETURN-TYPE-OF-CANDY-CHOCOLATE
 (1 1 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-CHOCOLATE->DARKNESS-OF-CANDY-CHOCOLATE
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-CHOCOLATE))
 )
(FTY::CANDY-CHOCOLATE->MAKER-OF-CANDY-CHOCOLATE
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-CHOCOLATE))
 )
(FTY::CANDY-CHOCOLATE-OF-FIELDS
 (3 1 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 )
(FTY::CANDY-FIX-WHEN-CHOCOLATE
 (3 1 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 )
(FTY::EQUAL-OF-CANDY-CHOCOLATE
 (11 11 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 (8 7 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:REWRITE STR-FIX-DEFAULT))
 )
(FTY::CANDY-CHOCOLATE-OF-IFIX-DARKNESS
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-CHOCOLATE-INT-EQUIV-CONGRUENCE-ON-DARKNESS)
(FTY::CANDY-CHOCOLATE-OF-STR-FIX-MAKER
 (2 2 (:REWRITE TMP-DEFTYPES-IFIX-WHEN-INTEGERP))
 )
(FTY::CANDY-CHOCOLATE-STREQV-CONGRUENCE-ON-MAKER)
(FTY::CANDY-HARD->HAS-SUGARP$INLINE)
(FTY::BOOLEANP-OF-CANDY-HARD->HAS-SUGARP
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 )
(FTY::CANDY-HARD->HAS-SUGARP$INLINE-OF-CANDY-FIX-X
 (12 4 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (8 8 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-HARD->HAS-SUGARP$INLINE-CANDY-EQUIV-CONGRUENCE-ON-X)
(FTY::CANDY-HARD->HAS-SUGARP-WHEN-WRONG-KIND
 (6 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(FTY::CANDY-HARD->STYLE$INLINE)
(FTY::STRINGP-OF-CANDY-HARD->STYLE)
(FTY::CANDY-HARD->STYLE$INLINE-OF-CANDY-FIX-X
 (12 4 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (9 9 (:TYPE-PRESCRIPTION FTY::CONSP-OF-CANDY-FIX))
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-FIX$INLINE))
 (8 8 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(FTY::CANDY-HARD->STYLE$INLINE-CANDY-EQUIV-CONGRUENCE-ON-X)
(FTY::CANDY-HARD->STYLE-WHEN-WRONG-KIND
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-HARD)
(FTY::RETURN-TYPE-OF-CANDY-HARD
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-HARD->HAS-SUGARP-OF-CANDY-HARD)
(FTY::CANDY-HARD->STYLE-OF-CANDY-HARD
 (9 9 (:TYPE-PRESCRIPTION FTY::CANDY-HARD))
 )
(FTY::CANDY-HARD-OF-FIELDS
 (3 1 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 )
(FTY::CANDY-FIX-WHEN-HARD
 (3 1 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 )
(FTY::EQUAL-OF-CANDY-HARD
 (24 24 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (6 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(FTY::CANDY-HARD-OF-BOOL-FIX-HAS-SUGARP
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CANDY-HARD-IFF-CONGRUENCE-ON-HAS-SUGARP)
(FTY::CANDY-HARD-OF-STR-FIX-STYLE
 (4 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(FTY::CANDY-HARD-STREQV-CONGRUENCE-ON-STYLE)
(FTY::CANDY-FIX-REDEF
 (9 3 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 )
(FTY::WOLFCHOW-P
 (16 4 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(FTY::CONSP-WHEN-WOLFCHOW-P)
(FTY::WOLFCHOW-P-WHEN-PERSON-P
 (2 2 (:REWRITE FTY::PERSON-P-WHEN-INVALID-TAG))
 (2 1 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (2 1 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (1 1 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (1 1 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 )
(FTY::WOLFCHOW-P-WHEN-CANDY-P
 (2 1 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (2 1 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (1 1 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (1 1 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (1 1 (:REWRITE FTY::PERSON-P-WHEN-INVALID-TAG))
 )
(FTY::PERSON-P-BY-TAG-WHEN-WOLFCHOW-P)
(FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P)
(FTY::WOLFCHOW-P-WHEN-INVALID-TAG
 (10 5 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (10 5 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (5 5 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (5 5 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (1 1 (:REWRITE FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P))
 )
(FTY::TAG-WHEN-WOLFCHOW-P-FORWARD)
(FTY::WOLFCHOW-FIX$INLINE)
(FTY::WOLFCHOW-P-OF-WOLFCHOW-FIX
 (93 6 (:REWRITE FTY::PERSON-FIX-WHEN-PERSON-P))
 (66 33 (:REWRITE FTY::TAG-WHEN-TEACHER-P))
 (66 33 (:REWRITE FTY::TAG-WHEN-STUDENT-P))
 (64 7 (:REWRITE FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P))
 (36 3 (:REWRITE FTY::CANDY-FIX-WHEN-CANDY-P))
 (33 33 (:TYPE-PRESCRIPTION FTY::TEACHER-P))
 (33 33 (:TYPE-PRESCRIPTION FTY::STUDENT-P))
 (16 8 (:REWRITE FTY::WOLFCHOW-P-WHEN-PERSON-P))
 (16 8 (:REWRITE FTY::WOLFCHOW-P-WHEN-CANDY-P))
 (2 2 (:REWRITE FTY::PERSON-P-WHEN-INVALID-TAG))
 )
(FTY::WOLFCHOW-FIX-WHEN-WOLFCHOW-P
 (8 2 (:REWRITE FTY::PERSON-P-BY-TAG-WHEN-WOLFCHOW-P))
 (6 2 (:REWRITE FTY::WOLFCHOW-P-WHEN-PERSON-P))
 (6 2 (:REWRITE FTY::WOLFCHOW-P-WHEN-CANDY-P))
 (2 2 (:REWRITE FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P))
 (1 1 (:REWRITE FTY::WOLFCHOW-P-WHEN-INVALID-TAG))
 )
(FTY::WOLFCHOW-FIX$INLINE
 (8 2 (:REWRITE FTY::PERSON-P-BY-TAG-WHEN-WOLFCHOW-P))
 (6 2 (:REWRITE FTY::WOLFCHOW-P-WHEN-PERSON-P))
 (6 2 (:REWRITE FTY::WOLFCHOW-P-WHEN-CANDY-P))
 (2 2 (:REWRITE FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P))
 (1 1 (:REWRITE FTY::WOLFCHOW-P-WHEN-INVALID-TAG))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (4 1 (:REWRITE FTY::WOLFCHOW-P-WHEN-PERSON-P))
 (4 1 (:REWRITE FTY::WOLFCHOW-P-WHEN-CANDY-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::PERSON-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CANDY-P))
 (1 1 (:REWRITE FTY::PERSON-P-BY-TAG-WHEN-WOLFCHOW-P))
 (1 1 (:REWRITE FTY::CANDY-P-BY-TAG-WHEN-WOLFCHOW-P))
 )
(FTY::WOLFCHOW-EQUIV$INLINE)
(FTY::WOLFCHOW-EQUIV-IS-AN-EQUIVALENCE)
(FTY::WOLFCHOW-EQUIV-IMPLIES-EQUAL-WOLFCHOW-FIX-1)
(FTY::WOLFCHOW-FIX-UNDER-WOLFCHOW-EQUIV)
(FTY::EQUAL-OF-WOLFCHOW-FIX-1-FORWARD-TO-WOLFCHOW-EQUIV)
(FTY::EQUAL-OF-WOLFCHOW-FIX-2-FORWARD-TO-WOLFCHOW-EQUIV)
(FTY::WOLFCHOW-EQUIV-OF-WOLFCHOW-FIX-1-FORWARD)
(FTY::WOLFCHOW-EQUIV-OF-WOLFCHOW-FIX-2-FORWARD)
(FTY::TAG-OF-WOLFCHOW-FIX-FORWARD)
(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(FTY::CONSTEST-P)
(FTY::CONSP-WHEN-CONSTEST-P)
(FTY::CONSTEST-FIX$INLINE)
(FTY::CONSTEST-P-OF-CONSTEST-FIX
 (12 4 (:REWRITE MAYBE-NATP-FIX-WHEN-MAYBE-NATP))
 (8 8 (:TYPE-PRESCRIPTION MAYBE-NATP$INLINE))
 (4 4 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CONSTEST-FIX-WHEN-CONSTEST-P)
(FTY::CONSTEST-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(FTY::CONSTEST-EQUIV$INLINE)
(FTY::CONSTEST-EQUIV-IS-AN-EQUIVALENCE)
(FTY::CONSTEST-EQUIV-IMPLIES-EQUAL-CONSTEST-FIX-1)
(FTY::CONSTEST-FIX-UNDER-CONSTEST-EQUIV)
(FTY::EQUAL-OF-CONSTEST-FIX-1-FORWARD-TO-CONSTEST-EQUIV)
(FTY::EQUAL-OF-CONSTEST-FIX-2-FORWARD-TO-CONSTEST-EQUIV)
(FTY::CONSTEST-EQUIV-OF-CONSTEST-FIX-1-FORWARD)
(FTY::CONSTEST-EQUIV-OF-CONSTEST-FIX-2-FORWARD)
(FTY::CONSTEST->FOO$INLINE)
(FTY::STRINGP-OF-CONSTEST->FOO)
(FTY::CONSTEST->FOO$INLINE-OF-CONSTEST-FIX-X
 (9 3 (:REWRITE FTY::CONSTEST-FIX-WHEN-CONSTEST-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::CONSTEST-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::CONSTEST-FIX$INLINE))
 (3 1 (:REWRITE MAYBE-NATP-FIX-WHEN-MAYBE-NATP))
 (2 2 (:TYPE-PRESCRIPTION MAYBE-NATP$INLINE))
 )
(FTY::CONSTEST->FOO$INLINE-CONSTEST-EQUIV-CONGRUENCE-ON-X)
(FTY::CONSTEST->BAR$INLINE)
(FTY::MAYBE-NATP-OF-CONSTEST->BAR)
(FTY::CONSTEST->BAR$INLINE-OF-CONSTEST-FIX-X
 (9 3 (:REWRITE FTY::CONSTEST-FIX-WHEN-CONSTEST-P))
 (6 6 (:TYPE-PRESCRIPTION FTY::CONSTEST-P))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CONSTEST->BAR$INLINE-CONSTEST-EQUIV-CONGRUENCE-ON-X)
(FTY::CONSTEST)
(FTY::CONSTEST-P-OF-CONSTEST)
(FTY::CONSTEST->FOO-OF-CONSTEST
 (6 6 (:TYPE-PRESCRIPTION FTY::CONSTEST))
 )
(FTY::CONSTEST->BAR-OF-CONSTEST)
(FTY::CONSTEST-OF-FIELDS
 (3 1 (:REWRITE FTY::CONSTEST-FIX-WHEN-CONSTEST-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CONSTEST-P))
 )
(FTY::CONSTEST-FIX-WHEN-CONSTEST
 (3 1 (:REWRITE FTY::CONSTEST-FIX-WHEN-CONSTEST-P))
 (2 2 (:TYPE-PRESCRIPTION FTY::CONSTEST-P))
 )
(FTY::EQUAL-OF-CONSTEST)
(FTY::CONSTEST-OF-STR-FIX-FOO
 (4 2 (:REWRITE MAYBE-NATP-FIX-WHEN-MAYBE-NATP))
 (2 2 (:TYPE-PRESCRIPTION MAYBE-NATP$INLINE))
 )
(FTY::CONSTEST-STREQV-CONGRUENCE-ON-FOO)
(FTY::CONSTEST-OF-MAYBE-NATP-FIX-BAR
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(FTY::CONSTEST-MAYBE-NAT-EQUIV-CONGRUENCE-ON-BAR)
(FTY::REMAKE-CONSTEST)
(FTY::CONSTEST-FIX-REDEF)
