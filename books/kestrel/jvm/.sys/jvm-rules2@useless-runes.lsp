(ALL-NON-NULLP)
(NOT-NULL-REFP-OF-NTH-WHEN-ALL-NON-NULLP
 (85 8 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (62 3 (:REWRITE NOT-EQUAL-NTH-WHEN-NOT-MEMBERP-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION MEMBERP))
 (16 8 (:REWRITE DEFAULT-<-2))
 (14 8 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (11 11 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (9 9 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (9 9 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (9 9 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (9 9 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (9 9 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (9 9 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE CLR-DIFFERENTIAL))
 (8 8 (:REWRITE JVM::USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (8 8 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (8 8 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (7 7 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (6 3 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (6 3 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (6 3 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (6 3 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (3 3 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (3 3 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (3 3 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (3 3 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (3 3 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (3 3 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (3 3 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE MEMBERP-OF-CDR-WHEN-NOT-MEMBERP))
 )
(ALL-BOUND-IN-RKEYS)
(IN-RKEYS-OF-NTH-WHEN-ALL-BOUND-IN-RKEYS
 (90 18 (:REWRITE SET::IN-TAIL))
 (36 36 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (31 11 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G-REV))
 (27 9 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (27 9 (:REWRITE SET::NEVER-IN-EMPTY))
 (22 22 (:REWRITE SET::SUBSET-IN-2))
 (22 22 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (21 9 (:REWRITE DEFAULT-CAR))
 (20 11 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (17 7 (:REWRITE DEFAULT-CDR))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE SET::SUBSET-IN-2-ALT))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (11 11 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G))
 (11 11 (:REWRITE IN-OF-RKEYS-WHEN-ARRAY-REFP))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE ARRAY-DIM-BOUND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE IN-OF-NTH-AND-RKEYS-WHEN-ARRAY-REF-LISTP))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE SUBSET-HACK))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 )
(ALL-ADDRESSES-BOUND-TO-OBJECT-OF-TYPE
 (25 6 (:REWRITE ADDRESSP-WHEN-ADDRESS-OR-NULLP-AND-NOT-NULL-REFP))
 (18 1 (:DEFINITION ADDRESS-OR-NULLP))
 (14 6 (:REWRITE USE-ALL-ADDRESSP-FOR-CAR))
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9 5 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (6 6 (:REWRITE USE-ALL-ADDRESSP-2))
 (6 6 (:REWRITE USE-ALL-ADDRESSP))
 (6 6 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (6 6 (:REWRITE ADDRESSP-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE ADDRESSP-WHEN-ARRAY-REF-LISTP-AND-MEMBERP))
 (5 5 (:REWRITE CLR-DIFFERENTIAL))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION ALL-ADDRESSP))
 (4 4 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (4 4 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (4 4 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (4 4 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (4 4 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (4 4 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION ADDRESS-OR-NULLP))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE JVM::USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (1 1 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:REWRITE ADDRESS-OR-NULLP-WHEN-ARRAY-REFP))
 (1 1 (:DEFINITION NULL-REF))
 )
(ALL-NULL-OR-ADDRESSES-BOUND-TO-OBJECT-OF-TYPE-WHEN-ALL-NON-NULLP
 (256 50 (:REWRITE USE-ALL-ADDRESSP-FOR-CAR))
 (253 23 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (100 100 (:TYPE-PRESCRIPTION ALL-ADDRESSP))
 (56 56 (:REWRITE ADDRESSP-WHEN-ARRAY-REFP))
 (56 56 (:REWRITE ADDRESSP-WHEN-ARRAY-REF-LISTP-AND-MEMBERP))
 (50 50 (:REWRITE USE-ALL-ADDRESSP-2))
 (50 50 (:REWRITE USE-ALL-ADDRESSP))
 (50 50 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP-CHEAP))
 (50 50 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP))
 (50 50 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (46 46 (:REWRITE CLR-DIFFERENTIAL))
 (44 44 (:REWRITE DEFAULT-CAR))
 (43 23 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (35 35 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (35 35 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (35 35 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (35 35 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (31 31 (:REWRITE DEFAULT-CDR))
 (30 6 (:REWRITE ALL-ADDRESSP-OF-CDR))
 (29 29 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (29 29 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (28 28 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (28 28 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (28 28 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (28 28 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (27 27 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (27 27 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (26 20 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (25 25 (:REWRITE ADDRESS-OR-NULLP-WHEN-ARRAY-REFP))
 (23 23 (:REWRITE JVM::USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (23 23 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (23 23 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (23 23 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (21 3 (:REWRITE LEN-OF-CDR))
 (20 20 (:REWRITE GET-CLASS-WHEN-ARRAY-REFP))
 (15 15 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(GET-FIELD-OF-NTH-WHEN-ALL-ADDRESSES-BOUND-TO-OBJECT-OF-TYPE
 (134 12 (:REWRITE ADDRESSP-WHEN-ADDRESS-OR-NULLP-AND-NOT-NULL-REFP))
 (116 6 (:DEFINITION ADDRESS-OR-NULLP))
 (76 12 (:REWRITE USE-ALL-ADDRESSP-FOR-CAR))
 (31 31 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (28 12 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP))
 (24 24 (:TYPE-PRESCRIPTION ALL-ADDRESSP))
 (22 14 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (21 9 (:REWRITE DEFAULT-CAR))
 (20 8 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (14 14 (:REWRITE CLR-DIFFERENTIAL))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 12 (:TYPE-PRESCRIPTION ADDRESS-OR-NULLP))
 (12 12 (:REWRITE USE-ALL-ADDRESSP-2))
 (12 12 (:REWRITE USE-ALL-ADDRESSP))
 (12 12 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (12 12 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (12 12 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (12 12 (:REWRITE ADDRESSP-WHEN-ARRAY-REFP))
 (12 12 (:REWRITE ADDRESSP-WHEN-ARRAY-REF-LISTP-AND-MEMBERP))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (8 8 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (8 8 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (8 8 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE ARRAY-DIM-BOUND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE GET-CLASS-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE ADDRESS-OR-NULLP-WHEN-ARRAY-REFP))
 (6 6 (:DEFINITION NULL-REF))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE GET-FIELD-CLASS-OF-NTH-WHEN-ARRAY-REF-LISTP))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 )
(GET-CLASS-OF-NTH-OF-ARRAY-CONTENTS-WHEN-ARRAY-REFP
 (83 4 (:DEFINITION NTH))
 (52 10 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (32 5 (:REWRITE DEFAULT-CDR))
 (26 1 (:DEFINITION ALL-NON-NULLP))
 (20 5 (:REWRITE CAR-OF-GET-FIELD-OF-CONTENTS-HACK))
 (17 17 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (16 2 (:REWRITE ADDRESSP-WHEN-ADDRESS-OR-NULLP-AND-NOT-NULL-REFP))
 (13 9 (:REWRITE DEFAULT-CAR))
 (13 1 (:DEFINITION ADDRESS-OR-NULLP))
 (12 12 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (11 11 (:REWRITE ARRAY-REFP-OF-SIZE-0-MEANS-CONTENTS-NIL))
 (11 4 (:REWRITE BOUND-WHEN-USB))
 (10 10 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (10 6 (:REWRITE ARRAY-LENGTH-WHEN-ARRAY-REFP))
 (10 2 (:REWRITE SET::IN-TAIL))
 (10 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (9 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (6 6 (:REWRITE LENGTH-FIELD-WHEN-ARRAY-REF-LISTP))
 (6 6 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (6 6 (:REWRITE LEN-OF-GET-FIELD-CONTENTS-WHEN-ARRAY-REF-LISTP))
 (6 6 (:REWRITE LEN-OF-CONTENTS-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE LEN-OF-CONTENTS-WHEN-ARRAY-REF-LISTP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE ARRAY-LENGTH-WHEN-A-ROW-OF-A-2D-ARRAY))
 (5 4 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (5 1 (:REWRITE LEN-OF-CDR))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE SET::SUBSET-IN))
 (4 4 (:REWRITE CLR-DIFFERENTIAL))
 (4 4 (:REWRITE ARRAY-DIM-BOUND))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (3 3 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (3 3 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (3 3 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE LEN-OF-GET-FIELDS-CONTENTS-IMPOSSIBLE-VALUE))
 (3 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G-REV))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ADDRESS-OR-NULLP))
 (2 2 (:REWRITE JVM::USE-ALL-CLASS-NAMESP-2))
 (2 2 (:REWRITE JVM::USE-ALL-CLASS-NAMESP))
 (2 2 (:REWRITE USE-ALL-ALL-UNSIGNED-BYTE-P-2))
 (2 2 (:REWRITE USE-ALL-ALL-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE USE-ALL-ADDRESSP-2))
 (2 2 (:REWRITE USE-ALL-ADDRESSP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE SET::SUBSET-IN-2))
 (2 2 (:REWRITE JVM::CLASS-NAMEP-WHEN-MV-NTH-0-OF-RESOLVE-METHOD))
 (2 2 (:REWRITE JVM::CLASS-NAMEP-WHEN-BOUND-IN-CLASS-TABLEP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (2 2 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (2 2 (:REWRITE ADDRESSP-WHEN-ARRAY-REFP))
 (2 2 (:REWRITE ADDRESSP-WHEN-ARRAY-REF-LISTP-AND-MEMBERP))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2 1 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ARRAY-REF-LISTP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE UBP-OF-DIM))
 (1 1 (:REWRITE TRUE-LISTP-OF-GET-FIELD-CONTENTS-WHEN-ARRAY-REF-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-OF-GET-FIELD-CONTENTS))
 (1 1 (:REWRITE SET::SUBSET-IN-2-ALT))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (1 1 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (1 1 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G))
 (1 1 (:REWRITE IN-OF-RKEYS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (1 1 (:REWRITE GET-CLASS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE ARRAY-REFP-WHEN-MEMBERP))
 (1 1 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 (1 1 (:REWRITE ADDRESS-OR-NULLP-WHEN-ARRAY-REFP))
 (1 1 (:DEFINITION NULL-REF))
 )
(GET-INTERNED-STRING-OF-MYIF
 (17 17 (:TYPE-PRESCRIPTION MYIF))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (2 2 (:REWRITE MYIF-WHEN-NOT-NIL))
 (2 2 (:REWRITE MYIF-WHEN-NIL))
 (2 2 (:REWRITE MYIF-OF-CONSTANT-WHEN-NOT-NIL))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (1 1 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE CLR-DIFFERENTIAL))
 )
(JVM::GET-INTERNED-STRING-OF-SET-INTERNED-STRING-DIFF
 (4 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:TYPE-PRESCRIPTION ACONS))
 (1 1 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (1 1 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE CLR-DIFFERENTIAL))
 )
(FIELD-HAS-TYPE)
(ALL-FIELDS-HAVE-TYPE)
(GET-CLASS-WHEN-ALL-FIELDS-HAVE-TYPE
 (23 23 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (22 14 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (21 9 (:REWRITE DEFAULT-CAR))
 (20 8 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (14 14 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (14 14 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (14 14 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (14 14 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (14 14 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (14 14 (:REWRITE CLR-DIFFERENTIAL))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 12 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (12 12 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE ARRAY-DIM-BOUND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (5 5 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 )
(IN-OF-RKEYS-WHEN-ALL-FIELDS-HAVE-TYPE
 (30 6 (:REWRITE SET::IN-TAIL))
 (22 22 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (21 9 (:REWRITE DEFAULT-CAR))
 (18 12 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (17 7 (:REWRITE DEFAULT-CDR))
 (14 5 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G-REV))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (12 12 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (12 12 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (12 12 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (12 12 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (12 12 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (12 12 (:REWRITE CLR-DIFFERENTIAL))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (9 5 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (9 3 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (9 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (8 8 (:REWRITE SET::SUBSET-IN-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE ARRAY-DIM-BOUND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (6 6 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G))
 (5 5 (:REWRITE IN-OF-RKEYS-WHEN-ARRAY-REFP))
 (4 4 (:REWRITE SET::SUBSET-IN-2-ALT))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 (1 1 (:REWRITE SUBSET-HACK))
 )
(NOT-NULL-REFP-WHEN-ALL-FIELDS-HAVE-TYPE
 (22 22 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (21 15 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (21 9 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (17 7 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (15 15 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (15 15 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (15 15 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (15 15 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (15 15 (:REWRITE CLR-DIFFERENTIAL))
 (13 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (12 8 (:REWRITE DEFAULT-<-2))
 (11 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE BOUND-WHEN-USB))
 (8 8 (:REWRITE ARRAY-DIM-BOUND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE NTH-WHEN-ALL-EQUAL$))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD-ALT))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-EQUAL-OF-GET-FIELD))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE NOT-NULL-REFP-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (6 6 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (6 6 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (5 5 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (2 2 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 )
(NOT-EQUAL-NTH-NEW-AD-WHEN-CLASS-NON-NIL
 (4 1 (:REWRITE NTH-NEW-AD-WHEN-ZP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE ZP-OPEN))
 )
(NOT-EQUAL-NTH-NEW-AD-WHEN-CLASS-NON-NIL-ALT
 (4 1 (:REWRITE NTH-NEW-AD-WHEN-ZP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE ZP-OPEN))
 )
(NOT-EQUAL-NEW-AD-WHEN-CLASS-NON-NIL
 (2 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G-REV))
 (1 1 (:REWRITE NEW-AD-KNOWN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G))
 (1 1 (:REWRITE IN-OF-RKEYS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (1 1 (:REWRITE G-OF-NEW-AD))
 )
(NOT-EQUAL-NEW-AD-WHEN-CLASS-NON-NIL-ALT
 (2 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G-REV))
 (1 1 (:REWRITE NEW-AD-KNOWN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:REWRITE JVM::IN-OF-RKEYS-WHEN-G))
 (1 1 (:REWRITE IN-OF-RKEYS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REFP))
 (1 1 (:REWRITE GET-FIELD-CLASS-WHEN-ARRAY-REF-LISTP-ONE-DIM))
 (1 1 (:REWRITE G-OF-NEW-AD))
 )
