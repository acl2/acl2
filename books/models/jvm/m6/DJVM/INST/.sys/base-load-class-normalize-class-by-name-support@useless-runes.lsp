(DJVM::INSTANCE-CLASS-TABLE-LOAD_CP_ENTRY)
(DJVM::INSTANCE-CLASS-TABLE-LOAD_CP_ENTRIES
 (30 18 (:REWRITE DEFAULT-CDR))
 (23 14 (:REWRITE DEFAULT-CAR))
 )
(DJVM::ISCLASSTERM-REMAINS-ISCLASSTERM-LOAD_ARRAY2-LEMMA
 (6 6 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE JVM::CLASS-BY-NAME-CONS))
 )
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2-LEMMA
 (7 7 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE JVM::CLASS-BY-NAME-CONS))
 )
(DJVM::ISCLASSTERM-REMAIN-ISCLASSTERM-LOAD-CLASS2
 (34848 858 (:DEFINITION MEM))
 (34760 88 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (27753 77 (:DEFINITION JVM::NORMALIZE-TYPE-REP))
 (22560 1880 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (21131 11 (:DEFINITION JVM::RUNTIME-STATIC-FIELDS-REP1))
 (20955 11 (:DEFINITION JVM::RUNTIME-STATIC-FIELD-REP))
 (15128 1891 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (13871 11 (:DEFINITION JVM::RUNTIME-METHODS-REP1))
 (13838 11 (:DEFINITION JVM::RUNTIME-METHOD-REP))
 (11343 9264 (:REWRITE DEFAULT-CDR))
 (8701 11 (:DEFINITION JVM::GETCPVALUE))
 (8536 11 (:REWRITE JVM::CENTRY-VALUE-NO-CHANGE-LOAD_CP_ENTRIES))
 (8448 22 (:DEFINITION JVM::NORMALIZE-TYPE-REPS))
 (7050 6792 (:REWRITE DEFAULT-CAR))
 (4446 57 (:DEFINITION JVM::LOAD_CP_ENTRIES))
 (4147 11 (:DEFINITION JVM::RUNTIME-INSTANCE-FIELDS-REP1))
 (3971 11 (:DEFINITION JVM::RUNTIME-INSTANCE-FIELD-REP))
 (1628 1628 (:REWRITE MEM-SUBSET))
 (1188 99 (:DEFINITION JVM::ARRAY-TYPE?))
 (858 22 (:DEFINITION JVM::RUNTIME-CODE-REP))
 (792 198 (:REWRITE ZP-OPEN))
 (572 22 (:DEFINITION JVM::RUNTIME-CODE-REP0))
 (550 110 (:DEFINITION LEN))
 (418 308 (:REWRITE DEFAULT-+-2))
 (399 399 (:TYPE-PRESCRIPTION JVM::LOAD_CP_ENTRY))
 (398 398 (:TYPE-PRESCRIPTION LEN))
 (308 308 (:REWRITE DEFAULT-+-1))
 (297 11 (:DEFINITION JVM::DEFAULT-VALUE))
 (242 242 (:TYPE-PRESCRIPTION MEM))
 (220 55 (:DEFINITION JVM::FIELD-FIELDACCESSFLAGS-S))
 (220 22 (:DEFINITION JVM::STATIC-FIELD?-S))
 (198 198 (:REWRITE DEFAULT-<-2))
 (198 198 (:REWRITE DEFAULT-<-1))
 (176 44 (:DEFINITION JVM::METHOD-ACCESSFLAGS-S))
 (143 11 (:DEFINITION JVM::REFERENCE-TYPE))
 (132 44 (:DEFINITION JVM::FIELD-FIELDTYPE-S))
 (110 110 (:REWRITE DEL-SET-LEN))
 (110 22 (:DEFINITION JVM::MAKE-STATIC-FIELD))
 (99 33 (:DEFINITION JVM::FIELD-FIELDNAME-S))
 (88 22 (:DEFINITION JVM::METHOD-RETURNTYPE-S))
 (88 22 (:DEFINITION JVM::METHOD-ARGS-S))
 (88 22 (:DEFINITION JVM::CODE-STACKMAPS-S))
 (88 22 (:DEFINITION JVM::CODE-MAX-STACK-S))
 (88 22 (:DEFINITION JVM::CODE-MAX-LOCAL-S))
 (88 22 (:DEFINITION JVM::CODE-INSTRS-S))
 (88 22 (:DEFINITION JVM::CODE-HANDLERS-S))
 (88 22 (:DEFINITION JVM::CODE-CODE-LENGTH-S))
 (77 77 (:DEFINITION JVM::MAKE-ARRAY-TYPE))
 (66 22 (:DEFINITION JVM::METHOD-METHODNAME-S))
 (66 22 (:DEFINITION JVM::METHOD-CODE-S))
 (66 22 (:DEFINITION JVM::FIELD-CPINDEX-S))
 (33 11 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (33 11 (:DEFINITION JVM::CPENTRY-VALUE))
 (22 22 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (22 22 (:DEFINITION JVM::MAKE-METHOD))
 (22 22 (:DEFINITION JVM::MAKE-CODE))
 (22 11 (:DEFINITION JVM::CPENTRY-TYPE-S))
 (11 11 (:TYPE-PRESCRIPTION JVM::PRIMITIVE-TYPE?))
 (11 11 (:DEFINITION JVM::MAKE-FIELD))
 (10 5 (:REWRITE JVM::CLASS-BY-NAME-CONS))
 (8 1 (:DEFINITION BIND))
 (5 5 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2-LEMMA))
 (4 1 (:REWRITE JVM::NO-FATAL-ERROR?-LOAD_CLASS2-IMPLIES-FOUND))
 (1 1 (:TYPE-PRESCRIPTION JVM::NO-FATAL-ERROR?))
 (1 1 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (1 1 (:REWRITE JVM::CORRECTLY-LOADED?-FOUND))
 (1 1 (:DEFINITION JVM::NO-FATAL-ERROR?))
 )
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2
 (34848 858 (:DEFINITION MEM))
 (34760 88 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (27753 77 (:DEFINITION JVM::NORMALIZE-TYPE-REP))
 (22560 1880 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (21131 11 (:DEFINITION JVM::RUNTIME-STATIC-FIELDS-REP1))
 (20955 11 (:DEFINITION JVM::RUNTIME-STATIC-FIELD-REP))
 (15128 1891 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (13871 11 (:DEFINITION JVM::RUNTIME-METHODS-REP1))
 (13838 11 (:DEFINITION JVM::RUNTIME-METHOD-REP))
 (11357 9278 (:REWRITE DEFAULT-CDR))
 (8701 11 (:DEFINITION JVM::GETCPVALUE))
 (8536 11 (:REWRITE JVM::CENTRY-VALUE-NO-CHANGE-LOAD_CP_ENTRIES))
 (8448 22 (:DEFINITION JVM::NORMALIZE-TYPE-REPS))
 (7078 6820 (:REWRITE DEFAULT-CAR))
 (4446 57 (:DEFINITION JVM::LOAD_CP_ENTRIES))
 (4147 11 (:DEFINITION JVM::RUNTIME-INSTANCE-FIELDS-REP1))
 (3971 11 (:DEFINITION JVM::RUNTIME-INSTANCE-FIELD-REP))
 (1628 1628 (:REWRITE MEM-SUBSET))
 (1188 99 (:DEFINITION JVM::ARRAY-TYPE?))
 (858 22 (:DEFINITION JVM::RUNTIME-CODE-REP))
 (792 198 (:REWRITE ZP-OPEN))
 (572 22 (:DEFINITION JVM::RUNTIME-CODE-REP0))
 (550 110 (:DEFINITION LEN))
 (418 308 (:REWRITE DEFAULT-+-2))
 (399 399 (:TYPE-PRESCRIPTION JVM::LOAD_CP_ENTRY))
 (398 398 (:TYPE-PRESCRIPTION LEN))
 (308 308 (:REWRITE DEFAULT-+-1))
 (297 11 (:DEFINITION JVM::DEFAULT-VALUE))
 (242 242 (:TYPE-PRESCRIPTION MEM))
 (220 55 (:DEFINITION JVM::FIELD-FIELDACCESSFLAGS-S))
 (220 22 (:DEFINITION JVM::STATIC-FIELD?-S))
 (198 198 (:REWRITE DEFAULT-<-2))
 (198 198 (:REWRITE DEFAULT-<-1))
 (176 44 (:DEFINITION JVM::METHOD-ACCESSFLAGS-S))
 (143 11 (:DEFINITION JVM::REFERENCE-TYPE))
 (132 44 (:DEFINITION JVM::FIELD-FIELDTYPE-S))
 (110 110 (:REWRITE DEL-SET-LEN))
 (110 22 (:DEFINITION JVM::MAKE-STATIC-FIELD))
 (99 33 (:DEFINITION JVM::FIELD-FIELDNAME-S))
 (88 22 (:DEFINITION JVM::METHOD-RETURNTYPE-S))
 (88 22 (:DEFINITION JVM::METHOD-ARGS-S))
 (88 22 (:DEFINITION JVM::CODE-STACKMAPS-S))
 (88 22 (:DEFINITION JVM::CODE-MAX-STACK-S))
 (88 22 (:DEFINITION JVM::CODE-MAX-LOCAL-S))
 (88 22 (:DEFINITION JVM::CODE-INSTRS-S))
 (88 22 (:DEFINITION JVM::CODE-HANDLERS-S))
 (88 22 (:DEFINITION JVM::CODE-CODE-LENGTH-S))
 (77 77 (:DEFINITION JVM::MAKE-ARRAY-TYPE))
 (66 22 (:DEFINITION JVM::METHOD-METHODNAME-S))
 (66 22 (:DEFINITION JVM::METHOD-CODE-S))
 (66 22 (:DEFINITION JVM::FIELD-CPINDEX-S))
 (33 11 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (33 11 (:DEFINITION JVM::CPENTRY-VALUE))
 (22 22 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (22 22 (:DEFINITION JVM::MAKE-METHOD))
 (22 22 (:DEFINITION JVM::MAKE-CODE))
 (22 11 (:DEFINITION JVM::CPENTRY-TYPE-S))
 (11 11 (:TYPE-PRESCRIPTION JVM::PRIMITIVE-TYPE?))
 (11 11 (:DEFINITION JVM::MAKE-FIELD))
 (10 5 (:REWRITE JVM::CLASS-BY-NAME-CONS))
 (8 1 (:DEFINITION BIND))
 (5 5 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2-LEMMA))
 (4 1 (:REWRITE JVM::NO-FATAL-ERROR?-LOAD_CLASS2-IMPLIES-FOUND))
 (1 1 (:TYPE-PRESCRIPTION JVM::NO-FATAL-ERROR?))
 (1 1 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (1 1 (:REWRITE JVM::CORRECTLY-LOADED?-FOUND))
 (1 1 (:DEFINITION JVM::NO-FATAL-ERROR?))
 )
(DJVM::ISCLASSTERM-REMAIN-ISCLASSTERM-LOAD-CLASS-X
 (11369 31 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (11336 2 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (10137 300 (:DEFINITION SUBSET))
 (9266 902 (:REWRITE JVM::SUBSET-CONS))
 (6626 902 (:REWRITE SUBSET-CONS))
 (1598 1582 (:REWRITE DEFAULT-CAR))
 (1206 1206 (:REWRITE SUBSET-TRANSITIVE))
 (816 68 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (634 610 (:REWRITE DEFAULT-CDR))
 (544 68 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (532 28 (:REWRITE JVM::FOUND-IMPLIES-MEM))
 (504 14 (:DEFINITION JVM::ALL-CLASS-NAMES-S))
 (448 14 (:REWRITE SET-EQUAL-MEM-CONS-2))
 (344 83 (:DEFINITION JVM::CLASS-BY-NAME))
 (340 340 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (340 68 (:DEFINITION TRUE-LISTP))
 (72 18 (:REWRITE JVM::NO-FATAL-ERROR?-LOAD_CLASS2-IMPLIES-FOUND))
 (71 71 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (32 32 (:REWRITE JVM::CORRECTLY-LOADED?-FOUND))
 (14 14 (:REWRITE SET-EQUAL-CONS))
 (7 1 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS2))
 (5 5 (:REWRITE CDR-CONS))
 (5 5 (:REWRITE CAR-CONS))
 (4 1 (:REWRITE JVM::NO-FATAL-ERROR?-CONSP))
 (4 1 (:REWRITE JVM::NO-FATAL-ERROR?-CLASSNAME-LOAD_CLASS2))
 (4 1 (:REWRITE JVM::LOAD_CLASS2_NO-FATAL-ERROR?-CLASS-TABLE))
 (2 2 (:TYPE-PRESCRIPTION JVM::PRIMITIVE-TYPE?))
 (1 1 (:REWRITE JVM::CLASS-BY-NAME-EQUAL-AFTER-LOAD_CLASS2))
 )
(DJVM::NOT-LOADED-NOTLOADED-AFTER-LOAD-CLASS-X-SPECIFIC-ISCLASSTERM)
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS_X
 (5689 20 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (5668 1 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (5156 155 (:DEFINITION SUBSET))
 (4633 451 (:REWRITE JVM::SUBSET-CONS))
 (3313 451 (:REWRITE SUBSET-CONS))
 (1227 1209 (:REWRITE DEFAULT-CAR))
 (840 70 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (616 616 (:REWRITE SUBSET-TRANSITIVE))
 (597 573 (:REWRITE DEFAULT-CDR))
 (560 70 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (532 28 (:REWRITE JVM::FOUND-IMPLIES-MEM))
 (504 14 (:DEFINITION JVM::ALL-CLASS-NAMES-S))
 (448 14 (:REWRITE SET-EQUAL-MEM-CONS-2))
 (350 350 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (350 70 (:DEFINITION TRUE-LISTP))
 (108 108 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (80 20 (:REWRITE JVM::NO-FATAL-ERROR?-LOAD_CLASS2-IMPLIES-FOUND))
 (34 34 (:REWRITE JVM::CORRECTLY-LOADED?-FOUND))
 (14 14 (:REWRITE SET-EQUAL-CONS))
 (5 5 (:REWRITE CDR-CONS))
 (5 5 (:REWRITE CAR-CONS))
 (1 1 (:TYPE-PRESCRIPTION JVM::PRIMITIVE-TYPE?))
 )
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_ARRAY_CLASS
 (1379 1365 (:REWRITE DEFAULT-CAR))
 (1090 1090 (:REWRITE DEFAULT-CDR))
 (780 117 (:DEFINITION BIND))
 (686 14 (:DEFINITION JVM::LOAD_CLASS_X))
 (635 635 (:REWRITE MEM-SUBSET))
 (585 117 (:DEFINITION ASSOC-EQUAL))
 (468 156 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (468 78 (:DEFINITION ALISTP))
 (312 312 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (274 116 (:DEFINITION TRUE-LISTP))
 (175 107 (:REWRITE DEFAULT-+-2))
 (168 14 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (140 14 (:DEFINITION JVM::FATALERROR))
 (126 14 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (112 14 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (112 14 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (107 107 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (107 107 (:REWRITE DEFAULT-+-1))
 (68 68 (:REWRITE DEL-SET-LEN))
 (56 56 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (56 14 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (56 14 (:DEFINITION MV-NTH))
 (48 48 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (45 45 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 (42 14 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (28 14 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (28 14 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (4 4 (:LINEAR SUBSET-NODUP-SET-SIZE))
 )
(DJVM::ISCLASSTERM-REMAIN-ISCLASSTERM-LOAD-ARRAY-CLASS
 (810 1 (:DEFINITION JVM::LOAD_ARRAY_CLASS))
 (699 4 (:DEFINITION JVM::LOAD_ARRAY_CLASS2))
 (352 4 (:DEFINITION JVM::UPDATE-TRACE))
 (292 4 (:DEFINITION JVM::ADD-OBJ-TH-COUNT))
 (183 4 (:DEFINITION JVM::GEN-ACCESS-FLAGS))
 (116 115 (:REWRITE DEFAULT-CAR))
 (113 40 (:DEFINITION MEM))
 (108 4 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (107 107 (:REWRITE DEFAULT-CDR))
 (80 12 (:DEFINITION BIND))
 (75 75 (:REWRITE MEM-SUBSET))
 (68 68 (:REWRITE JVM::STATE-ACCESSOR))
 (60 12 (:DEFINITION ASSOC-EQUAL))
 (56 8 (:DEFINITION BINDING))
 (56 5 (:DEFINITION JVM::ARRAY-TYPE?))
 (50 1 (:DEFINITION JVM::LOAD_CLASS))
 (49 1 (:DEFINITION JVM::LOAD_CLASS_X))
 (48 16 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (48 8 (:DEFINITION ALISTP))
 (45 9 (:DEFINITION LEN))
 (42 21 (:DEFINITION NTH))
 (40 4 (:DEFINITION JVM::STATE-SET-TRACE))
 (40 4 (:DEFINITION JVM::STATE-SET-ARRAY-CLASS-TABLE))
 (32 32 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (32 4 (:DEFINITION JVM::TH-COUNTERS))
 (32 4 (:DEFINITION JVM::STATE-SET-CLASS-TABLE))
 (32 4 (:DEFINITION JVM::STATE-SET-AUX))
 (32 4 (:DEFINITION JVM::RTRACE))
 (29 13 (:DEFINITION TRUE-LISTP))
 (28 25 (:REWRITE JVM::STATE-ACCESSOR-SET-CURRENT-THREAD))
 (28 4 (:DEFINITION JVM::ALLOC))
 (26 26 (:TYPE-PRESCRIPTION LEN))
 (24 4 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS))
 (24 4 (:DEFINITION BOUND?))
 (22 13 (:REWRITE DEFAULT-+-2))
 (20 5 (:DEFINITION JVM::CLASS-BY-NAME))
 (20 4 (:DEFINITION JVM::STATE-SET-HEAP))
 (14 2 (:DEFINITION JVM::ARRAY-CLASS-BY-NAME))
 (13 13 (:REWRITE DEFAULT-+-1))
 (12 4 (:DEFINITION JVM::MTRACE))
 (12 1 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (11 1 (:DEFINITION JVM::ARRAYCLASSLOADED?))
 (10 1 (:DEFINITION JVM::FATALERROR))
 (9 9 (:REWRITE DEL-SET-LEN))
 (9 9 (:DEFINITION JVM::MAKE-ARRAY-TYPE))
 (9 1 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (9 1 (:DEFINITION JVM::ARRAYCLASSLOADED1?))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 8 (:DEFINITION JVM::MAKE-TRACE))
 (8 6 (:DEFINITION JVM::NO-FATAL-ERROR?))
 (8 4 (:DEFINITION JVM::MAKE-ARRAY-CLASS-TABLE-ENTRY))
 (8 4 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS-INFO))
 (8 2 (:DEFINITION JVM::CLASS-ACCESSFLAGS))
 (8 1 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (8 1 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS_X))
 (8 1 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (7 7 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (6 2 (:DEFINITION JVM::ARRAY-SIG))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (4 4 (:REWRITE JVM::INSTANCE-CLASS-TABLE-MAKE-STATE-2))
 (4 4 (:DEFINITION JVM::TRACE-AUX))
 (4 4 (:DEFINITION JVM::MAKE-OBJECT))
 (4 4 (:DEFINITION JVM::MAKE-INSTANCECLASSARRAYCLASS-INFO))
 (4 4 (:DEFINITION JVM::BUILD-JAVA-LANG-CLASS-JAVA-VISIBLE-PART))
 (4 4 (:DEFINITION JVM::ADD-ARRAY-CLASS-TABLE-ENTRY))
 (4 2 (:REWRITE JVM::ENV-DOES-NOT-CHANGE-LOAD_CLASS_X))
 (4 1 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (4 1 (:DEFINITION MV-NTH))
 (4 1 (:DEFINITION JVM::ARRAY-ACCESS-FLAGS))
 (3 3 (:TYPE-PRESCRIPTION MEM))
 (3 3 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (3 2 (:REWRITE JVM::ARRAY-CLASS-TABLE-STATE-SET-CURRENT-THREAD))
 (3 1 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (2 1 (:REWRITE JVM::LOAD_CLASS_X_ONLY_CHANGE_CLASS_TABLE_ERROR_FLAG_HEAP))
 (2 1 (:REWRITE JVM::LOAD_CLASS_X_CHANGE_NOT_ARRAY_CLASS_TABLE))
 (2 1 (:REWRITE JVM::LOAD_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 1 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (2 1 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (1 1 (:TYPE-PRESCRIPTION JVM::CLASS-LOADED?))
 (1 1 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (1 1 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-CURRENT-THREAD))
 (1 1 (:REWRITE JVM::ENV-NO-CHANGE-LOAD-ARRAY-CLASS))
 (1 1 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 )
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-RESOLVECLASSREFERENCE
 (4728 2 (:DEFINITION JVM::LOAD_ARRAY_CLASS))
 (2946 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-INV-HELPER-IMPLIES-NON-PRIMITIVE-TYPE-NON-ARRAY-TYPE-LOADED))
 (2888 6 (:DEFINITION JVM::ARRAY-CLASS-TABLE-INV-HELPER))
 (2538 6 (:DEFINITION JVM::ARRAY-CLASS-CORRECTLY-LOADED?))
 (2306 138 (:DEFINITION MEM))
 (2304 14 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (2225 6 (:DEFINITION JVM::LOAD_CLASS_X))
 (1542 8 (:DEFINITION JVM::LOAD_ARRAY_CLASS2))
 (1007 857 (:REWRITE DEFAULT-CAR))
 (988 2 (:REWRITE JVM::STATE-SET-CURRENT-THREAD-NOT-CHANGE-INV))
 (976 3 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (918 102 (:DEFINITION JVM::BASE-TYPES))
 (795 159 (:DEFINITION LEN))
 (704 8 (:DEFINITION JVM::UPDATE-TRACE))
 (636 106 (:DEFINITION JVM::ALL-ARRAY-SIGS))
 (584 8 (:DEFINITION JVM::ADD-OBJ-TH-COUNT))
 (543 525 (:REWRITE DEFAULT-CDR))
 (444 444 (:TYPE-PRESCRIPTION JVM::BASE-TYPES))
 (366 8 (:DEFINITION JVM::GEN-ACCESS-FLAGS))
 (348 116 (:DEFINITION JVM::ARRAY-SIG))
 (326 167 (:REWRITE DEFAULT-+-2))
 (308 154 (:DEFINITION NTH))
 (256 256 (:REWRITE MEM-SUBSET))
 (252 24 (:REWRITE JVM::MAKE-ARRAY-TYPE-ARRAY-BASE-TYPE-IS-IDENTITY-WHEN-ARRAY-TYPE?))
 (167 167 (:REWRITE DEFAULT-+-1))
 (166 8 (:DEFINITION JVM::ARRAYCLASSLOADED?))
 (160 24 (:DEFINITION BIND))
 (159 159 (:REWRITE DEL-SET-LEN))
 (138 45 (:DEFINITION TRUE-LISTP))
 (136 136 (:REWRITE JVM::STATE-ACCESSOR))
 (120 24 (:DEFINITION ASSOC-EQUAL))
 (120 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS))
 (112 16 (:DEFINITION BINDING))
 (96 32 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (96 16 (:DEFINITION ALISTP))
 (88 8 (:DEFINITION JVM::MAKE-ARRAY-CLASS-TABLE-ENTRY))
 (84 21 (:DEFINITION JVM::CLASS-BY-NAME))
 (80 8 (:DEFINITION JVM::STATE-SET-TRACE))
 (80 8 (:DEFINITION JVM::STATE-SET-ARRAY-CLASS-TABLE))
 (72 6 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (67 61 (:REWRITE JVM::STATE-ACCESSOR-SET-CURRENT-THREAD))
 (66 8 (:DEFINITION JVM::ARRAYCLASSLOADED1?))
 (64 64 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (64 10 (:DEFINITION JVM::ARRAY-CLASS-BY-NAME))
 (64 8 (:DEFINITION JVM::TH-COUNTERS))
 (64 8 (:DEFINITION JVM::STATE-SET-CLASS-TABLE))
 (64 8 (:DEFINITION JVM::STATE-SET-AUX))
 (64 8 (:DEFINITION JVM::RTRACE))
 (56 8 (:DEFINITION JVM::ALLOC))
 (54 54 (:TYPE-PRESCRIPTION JVM::ARRAY-CLASS-CORRECTLY-LOADED?))
 (50 50 (:TYPE-PRESCRIPTION JVM::ARRAY-CLASS-TABLE-INV-HELPER))
 (48 8 (:DEFINITION BOUND?))
 (48 6 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (40 8 (:DEFINITION JVM::STATE-SET-HEAP))
 (39 6 (:DEFINITION JVM::FATALERROR))
 (33 6 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (30 30 (:LINEAR SUBSET-NODUP-SET-SIZE))
 (29 24 (:DEFINITION JVM::NO-FATAL-ERROR?))
 (28 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-IMPLIES-ARRAY-CORRECTLY-LOADED-WHEN-INV-HOLD))
 (28 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-ARRAY-CORRECTLY-LOADED))
 (27 27 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (27 6 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (24 24 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (24 24 (:TYPE-PRESCRIPTION JVM::ARRAY-TYPE?))
 (24 24 (:TYPE-PRESCRIPTION JVM::ALL-ARRAY-SIGS))
 (24 8 (:DEFINITION JVM::MTRACE))
 (24 6 (:DEFINITION MV-NTH))
 (21 21 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (18 6 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (16 16 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:DEFINITION JVM::MAKE-TRACE))
 (16 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS-INFO))
 (16 4 (:DEFINITION JVM::CLASS-ACCESSFLAGS))
 (13 8 (:REWRITE JVM::ENV-DOES-NOT-CHANGE-LOAD_CLASS_X))
 (9 6 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (9 3 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (8 8 (:REWRITE JVM::INSTANCE-CLASS-TABLE-MAKE-STATE-2))
 (8 8 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 (8 8 (:DEFINITION JVM::TRACE-AUX))
 (8 8 (:DEFINITION JVM::MAKE-OBJECT))
 (8 8 (:DEFINITION JVM::MAKE-INSTANCECLASSARRAYCLASS-INFO))
 (8 8 (:DEFINITION JVM::BUILD-JAVA-LANG-CLASS-JAVA-VISIBLE-PART))
 (8 8 (:DEFINITION JVM::ADD-ARRAY-CLASS-TABLE-ENTRY))
 (8 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-STATE-SET-CURRENT-THREAD))
 (8 2 (:DEFINITION JVM::ARRAY-ACCESS-FLAGS))
 (6 6 (:TYPE-PRESCRIPTION MEM))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-INV-HELPER-LOADED-IMPLIES-CORRECTLY-LOADED))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-IMPLIES-ARRAY-CORRECTLY-LOADED))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_ONLY_CHANGE_CLASS_TABLE_ERROR_FLAG_HEAP))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_CHANGE_NOT_ARRAY_CLASS_TABLE))
 (4 2 (:REWRITE JVM::LOAD_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-CURRENT-THREAD))
 (2 2 (:REWRITE JVM::ENV-NO-CHANGE-LOAD-ARRAY-CLASS))
 )
(DJVM::ISCLASSTERM-REMAIN-ISCLASSTERM-RESOLVECLASSREFERNECE
 (4728 2 (:DEFINITION JVM::LOAD_ARRAY_CLASS))
 (2946 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-INV-HELPER-IMPLIES-NON-PRIMITIVE-TYPE-NON-ARRAY-TYPE-LOADED))
 (2888 6 (:DEFINITION JVM::ARRAY-CLASS-TABLE-INV-HELPER))
 (2538 6 (:DEFINITION JVM::ARRAY-CLASS-CORRECTLY-LOADED?))
 (2306 138 (:DEFINITION MEM))
 (2304 14 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (2225 6 (:DEFINITION JVM::LOAD_CLASS_X))
 (1542 8 (:DEFINITION JVM::LOAD_ARRAY_CLASS2))
 (997 847 (:REWRITE DEFAULT-CAR))
 (988 2 (:REWRITE JVM::STATE-SET-CURRENT-THREAD-NOT-CHANGE-INV))
 (976 3 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (918 102 (:DEFINITION JVM::BASE-TYPES))
 (795 159 (:DEFINITION LEN))
 (704 8 (:DEFINITION JVM::UPDATE-TRACE))
 (636 106 (:DEFINITION JVM::ALL-ARRAY-SIGS))
 (584 8 (:DEFINITION JVM::ADD-OBJ-TH-COUNT))
 (538 520 (:REWRITE DEFAULT-CDR))
 (444 444 (:TYPE-PRESCRIPTION JVM::BASE-TYPES))
 (366 8 (:DEFINITION JVM::GEN-ACCESS-FLAGS))
 (348 116 (:DEFINITION JVM::ARRAY-SIG))
 (326 167 (:REWRITE DEFAULT-+-2))
 (308 154 (:DEFINITION NTH))
 (256 256 (:REWRITE MEM-SUBSET))
 (252 24 (:REWRITE JVM::MAKE-ARRAY-TYPE-ARRAY-BASE-TYPE-IS-IDENTITY-WHEN-ARRAY-TYPE?))
 (167 167 (:REWRITE DEFAULT-+-1))
 (166 8 (:DEFINITION JVM::ARRAYCLASSLOADED?))
 (160 24 (:DEFINITION BIND))
 (159 159 (:REWRITE DEL-SET-LEN))
 (138 45 (:DEFINITION TRUE-LISTP))
 (136 136 (:REWRITE JVM::STATE-ACCESSOR))
 (120 24 (:DEFINITION ASSOC-EQUAL))
 (120 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS))
 (112 16 (:DEFINITION BINDING))
 (96 32 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (96 16 (:DEFINITION ALISTP))
 (88 8 (:DEFINITION JVM::MAKE-ARRAY-CLASS-TABLE-ENTRY))
 (80 8 (:DEFINITION JVM::STATE-SET-TRACE))
 (80 8 (:DEFINITION JVM::STATE-SET-ARRAY-CLASS-TABLE))
 (72 6 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (67 61 (:REWRITE JVM::STATE-ACCESSOR-SET-CURRENT-THREAD))
 (66 8 (:DEFINITION JVM::ARRAYCLASSLOADED1?))
 (64 64 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (64 16 (:DEFINITION JVM::CLASS-BY-NAME))
 (64 10 (:DEFINITION JVM::ARRAY-CLASS-BY-NAME))
 (64 8 (:DEFINITION JVM::TH-COUNTERS))
 (64 8 (:DEFINITION JVM::STATE-SET-CLASS-TABLE))
 (64 8 (:DEFINITION JVM::STATE-SET-AUX))
 (64 8 (:DEFINITION JVM::RTRACE))
 (56 8 (:DEFINITION JVM::ALLOC))
 (54 54 (:TYPE-PRESCRIPTION JVM::ARRAY-CLASS-CORRECTLY-LOADED?))
 (50 50 (:TYPE-PRESCRIPTION JVM::ARRAY-CLASS-TABLE-INV-HELPER))
 (48 8 (:DEFINITION BOUND?))
 (48 6 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (40 8 (:DEFINITION JVM::STATE-SET-HEAP))
 (39 6 (:DEFINITION JVM::FATALERROR))
 (33 6 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (30 30 (:LINEAR SUBSET-NODUP-SET-SIZE))
 (29 24 (:DEFINITION JVM::NO-FATAL-ERROR?))
 (28 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-IMPLIES-ARRAY-CORRECTLY-LOADED-WHEN-INV-HOLD))
 (28 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-ARRAY-CORRECTLY-LOADED))
 (27 27 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (27 6 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (24 24 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (24 24 (:TYPE-PRESCRIPTION JVM::ARRAY-TYPE?))
 (24 24 (:TYPE-PRESCRIPTION JVM::ALL-ARRAY-SIGS))
 (24 8 (:DEFINITION JVM::MTRACE))
 (24 6 (:DEFINITION MV-NTH))
 (21 21 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (18 6 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (16 16 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:DEFINITION JVM::MAKE-TRACE))
 (16 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS-INFO))
 (16 4 (:DEFINITION JVM::CLASS-ACCESSFLAGS))
 (13 8 (:REWRITE JVM::ENV-DOES-NOT-CHANGE-LOAD_CLASS_X))
 (9 6 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (9 3 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (8 8 (:REWRITE JVM::INSTANCE-CLASS-TABLE-MAKE-STATE-2))
 (8 8 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 (8 8 (:DEFINITION JVM::TRACE-AUX))
 (8 8 (:DEFINITION JVM::MAKE-OBJECT))
 (8 8 (:DEFINITION JVM::MAKE-INSTANCECLASSARRAYCLASS-INFO))
 (8 8 (:DEFINITION JVM::BUILD-JAVA-LANG-CLASS-JAVA-VISIBLE-PART))
 (8 8 (:DEFINITION JVM::ADD-ARRAY-CLASS-TABLE-ENTRY))
 (8 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-STATE-SET-CURRENT-THREAD))
 (8 2 (:DEFINITION JVM::ARRAY-ACCESS-FLAGS))
 (6 6 (:TYPE-PRESCRIPTION MEM))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-TABLE-INV-HELPER-LOADED-IMPLIES-CORRECTLY-LOADED))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-BY-NAME-IMPLIES-ARRAY-CORRECTLY-LOADED))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_ONLY_CHANGE_CLASS_TABLE_ERROR_FLAG_HEAP))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_CHANGE_NOT_ARRAY_CLASS_TABLE))
 (4 2 (:REWRITE JVM::LOAD_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-CURRENT-THREAD))
 (2 2 (:REWRITE JVM::ENV-NO-CHANGE-LOAD-ARRAY-CLASS))
 )
(DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-GETARRAYCLASS
 (1620 2 (:DEFINITION JVM::LOAD_ARRAY_CLASS))
 (1398 8 (:DEFINITION JVM::LOAD_ARRAY_CLASS2))
 (704 8 (:DEFINITION JVM::UPDATE-TRACE))
 (584 8 (:DEFINITION JVM::ADD-OBJ-TH-COUNT))
 (366 8 (:DEFINITION JVM::GEN-ACCESS-FLAGS))
 (242 240 (:REWRITE DEFAULT-CAR))
 (226 80 (:DEFINITION MEM))
 (218 218 (:REWRITE DEFAULT-CDR))
 (216 8 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (160 24 (:DEFINITION BIND))
 (150 150 (:REWRITE MEM-SUBSET))
 (136 136 (:REWRITE JVM::STATE-ACCESSOR))
 (120 24 (:DEFINITION ASSOC-EQUAL))
 (112 16 (:DEFINITION BINDING))
 (112 10 (:DEFINITION JVM::ARRAY-TYPE?))
 (100 2 (:DEFINITION JVM::LOAD_CLASS))
 (98 2 (:DEFINITION JVM::LOAD_CLASS_X))
 (96 32 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (96 16 (:DEFINITION ALISTP))
 (90 18 (:DEFINITION LEN))
 (88 44 (:DEFINITION NTH))
 (80 8 (:DEFINITION JVM::STATE-SET-TRACE))
 (80 8 (:DEFINITION JVM::STATE-SET-ARRAY-CLASS-TABLE))
 (64 64 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (64 8 (:DEFINITION JVM::TH-COUNTERS))
 (64 8 (:DEFINITION JVM::STATE-SET-CLASS-TABLE))
 (64 8 (:DEFINITION JVM::STATE-SET-AUX))
 (64 8 (:DEFINITION JVM::RTRACE))
 (58 26 (:DEFINITION TRUE-LISTP))
 (56 50 (:REWRITE JVM::STATE-ACCESSOR-SET-CURRENT-THREAD))
 (56 8 (:DEFINITION JVM::ALLOC))
 (52 52 (:TYPE-PRESCRIPTION LEN))
 (48 12 (:DEFINITION JVM::CLASS-BY-NAME))
 (48 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS))
 (48 8 (:DEFINITION BOUND?))
 (44 26 (:REWRITE DEFAULT-+-2))
 (42 6 (:DEFINITION JVM::ARRAY-CLASS-BY-NAME))
 (40 8 (:DEFINITION JVM::STATE-SET-HEAP))
 (26 26 (:REWRITE DEFAULT-+-1))
 (24 8 (:DEFINITION JVM::MTRACE))
 (24 2 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (20 2 (:DEFINITION JVM::FATALERROR))
 (18 18 (:REWRITE DEL-SET-LEN))
 (18 6 (:DEFINITION JVM::ARRAY-SIG))
 (18 2 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (16 16 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:DEFINITION JVM::MAKE-TRACE))
 (16 12 (:DEFINITION JVM::NO-FATAL-ERROR?))
 (16 8 (:DEFINITION JVM::MAKE-ARRAY-CLASS-TABLE-ENTRY))
 (16 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS-INFO))
 (16 4 (:DEFINITION JVM::CLASS-ACCESSFLAGS))
 (16 2 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (16 2 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS_X))
 (16 2 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (14 14 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (8 8 (:REWRITE JVM::INSTANCE-CLASS-TABLE-MAKE-STATE-2))
 (8 8 (:DEFINITION JVM::TRACE-AUX))
 (8 8 (:DEFINITION JVM::MAKE-OBJECT))
 (8 8 (:DEFINITION JVM::MAKE-INSTANCECLASSARRAYCLASS-INFO))
 (8 8 (:DEFINITION JVM::BUILD-JAVA-LANG-CLASS-JAVA-VISIBLE-PART))
 (8 8 (:DEFINITION JVM::ADD-ARRAY-CLASS-TABLE-ENTRY))
 (8 4 (:REWRITE JVM::ENV-DOES-NOT-CHANGE-LOAD_CLASS_X))
 (8 2 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (8 2 (:DEFINITION MV-NTH))
 (8 2 (:DEFINITION JVM::ARRAY-ACCESS-FLAGS))
 (6 6 (:TYPE-PRESCRIPTION MEM))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (6 4 (:REWRITE JVM::ARRAY-CLASS-TABLE-STATE-SET-CURRENT-THREAD))
 (6 2 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (4 4 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_ONLY_CHANGE_CLASS_TABLE_ERROR_FLAG_HEAP))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_CHANGE_NOT_ARRAY_CLASS_TABLE))
 (4 2 (:REWRITE JVM::LOAD_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (4 2 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (4 2 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (2 2 (:TYPE-PRESCRIPTION JVM::CLASS-LOADED?))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-CURRENT-THREAD))
 (2 2 (:REWRITE JVM::ENV-NO-CHANGE-LOAD-ARRAY-CLASS))
 )
(DJVM::ISCLASSTERM-REMAIN-ISCLASSTERM-GETARRAYCLASS
 (1620 2 (:DEFINITION JVM::LOAD_ARRAY_CLASS))
 (1398 8 (:DEFINITION JVM::LOAD_ARRAY_CLASS2))
 (704 8 (:DEFINITION JVM::UPDATE-TRACE))
 (584 8 (:DEFINITION JVM::ADD-OBJ-TH-COUNT))
 (366 8 (:DEFINITION JVM::GEN-ACCESS-FLAGS))
 (238 236 (:REWRITE DEFAULT-CAR))
 (226 80 (:DEFINITION MEM))
 (216 216 (:REWRITE DEFAULT-CDR))
 (216 8 (:DEFINITION JVM::PRIMITIVE-TYPE?))
 (160 24 (:DEFINITION BIND))
 (150 150 (:REWRITE MEM-SUBSET))
 (136 136 (:REWRITE JVM::STATE-ACCESSOR))
 (120 24 (:DEFINITION ASSOC-EQUAL))
 (112 16 (:DEFINITION BINDING))
 (112 10 (:DEFINITION JVM::ARRAY-TYPE?))
 (100 2 (:DEFINITION JVM::LOAD_CLASS))
 (98 2 (:DEFINITION JVM::LOAD_CLASS_X))
 (96 32 (:REWRITE JVM::WFF-HEAP-IMPLIES-ALISTP))
 (96 16 (:DEFINITION ALISTP))
 (90 18 (:DEFINITION LEN))
 (88 44 (:DEFINITION NTH))
 (80 8 (:DEFINITION JVM::STATE-SET-TRACE))
 (80 8 (:DEFINITION JVM::STATE-SET-ARRAY-CLASS-TABLE))
 (64 64 (:TYPE-PRESCRIPTION JVM::WFF-HEAP))
 (64 8 (:DEFINITION JVM::TH-COUNTERS))
 (64 8 (:DEFINITION JVM::STATE-SET-CLASS-TABLE))
 (64 8 (:DEFINITION JVM::STATE-SET-AUX))
 (64 8 (:DEFINITION JVM::RTRACE))
 (58 26 (:DEFINITION TRUE-LISTP))
 (56 50 (:REWRITE JVM::STATE-ACCESSOR-SET-CURRENT-THREAD))
 (56 8 (:DEFINITION JVM::ALLOC))
 (52 52 (:TYPE-PRESCRIPTION LEN))
 (48 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS))
 (48 8 (:DEFINITION BOUND?))
 (44 26 (:REWRITE DEFAULT-+-2))
 (42 6 (:DEFINITION JVM::ARRAY-CLASS-BY-NAME))
 (40 10 (:DEFINITION JVM::CLASS-BY-NAME))
 (40 8 (:DEFINITION JVM::STATE-SET-HEAP))
 (26 26 (:REWRITE DEFAULT-+-1))
 (24 8 (:DEFINITION JVM::MTRACE))
 (24 2 (:DEFINITION JVM::CLASS-BY-NAME-S))
 (20 2 (:DEFINITION JVM::FATALERROR))
 (18 18 (:REWRITE DEL-SET-LEN))
 (18 6 (:DEFINITION JVM::ARRAY-SIG))
 (18 2 (:DEFINITION JVM::M6-INTERNAL-ERROR))
 (16 16 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:DEFINITION JVM::MAKE-TRACE))
 (16 12 (:DEFINITION JVM::NO-FATAL-ERROR?))
 (16 8 (:DEFINITION JVM::MAKE-ARRAY-CLASS-TABLE-ENTRY))
 (16 8 (:DEFINITION JVM::BUILD-INSTANCECLASSARRAYCLASS-INFO))
 (16 4 (:DEFINITION JVM::CLASS-ACCESSFLAGS))
 (16 2 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (16 2 (:REWRITE DJVM::CLASS-BY-NAME-NO-CHANGE-AFTER-LOAD_CLASS_X))
 (16 2 (:DEFINITION JVM::STATE-SET-ERROR-FLAG))
 (14 14 (:REWRITE JVM::NO-FATAL-ERROR?-NO-FATAL-ERROR?))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION JVM::CLASS-BY-NAME-S))
 (8 8 (:REWRITE JVM::INSTANCE-CLASS-TABLE-MAKE-STATE-2))
 (8 8 (:DEFINITION JVM::TRACE-AUX))
 (8 8 (:DEFINITION JVM::MAKE-OBJECT))
 (8 8 (:DEFINITION JVM::MAKE-INSTANCECLASSARRAYCLASS-INFO))
 (8 8 (:DEFINITION JVM::BUILD-JAVA-LANG-CLASS-JAVA-VISIBLE-PART))
 (8 8 (:DEFINITION JVM::ADD-ARRAY-CLASS-TABLE-ENTRY))
 (8 4 (:REWRITE JVM::ENV-DOES-NOT-CHANGE-LOAD_CLASS_X))
 (8 2 (:DEFINITION JVM::TRIVIAL-INV-ENV-DO-NOT-CHANGE))
 (8 2 (:DEFINITION MV-NTH))
 (8 2 (:DEFINITION JVM::ARRAY-ACCESS-FLAGS))
 (6 6 (:TYPE-PRESCRIPTION MEM))
 (6 6 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED?-MEM-NOT-PRIMITIVE-TYPE-NOT-ARRAY-TYPE))
 (6 4 (:REWRITE JVM::ARRAY-CLASS-TABLE-STATE-SET-CURRENT-THREAD))
 (6 2 (:REWRITE JVM::NO-FATAL-ERROR-SET-THREAD-LOAD_CLASS_X))
 (4 4 (:REWRITE JVM::ARRAY-CLASS-CORRECTLY-LOADED-IMPLIES-BASE-CLASS-LOADED-GENERAL))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_ONLY_CHANGE_CLASS_TABLE_ERROR_FLAG_HEAP))
 (4 2 (:REWRITE JVM::LOAD_CLASS_X_CHANGE_NOT_ARRAY_CLASS_TABLE))
 (4 2 (:REWRITE JVM::LOAD_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (4 2 (:REWRITE JVM::CLASS-LOADED-SET-CURRENT-THREAD))
 (4 2 (:DEFINITION JVM::EXTERNAL-CLASS-TABLE))
 (2 2 (:TYPE-PRESCRIPTION JVM::CLASS-LOADED?))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-THREAD-TABLE))
 (2 2 (:REWRITE JVM::LOAD_ARRAY_CLASS-DOES-NOT-CHANGE-CURRENT-THREAD))
 (2 2 (:REWRITE JVM::ENV-NO-CHANGE-LOAD-ARRAY-CLASS))
 )
