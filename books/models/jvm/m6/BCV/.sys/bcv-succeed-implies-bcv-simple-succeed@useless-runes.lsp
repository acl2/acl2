(BCV::MERGEDCODEISTYPESAFE-INDUCT
 (4811 2062 (:REWRITE DEFAULT-+-2))
 (2976 2062 (:REWRITE DEFAULT-+-1))
 (1037 19 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (905 181 (:DEFINITION LEN))
 (659 453 (:REWRITE DEFAULT-<-2))
 (519 453 (:REWRITE DEFAULT-<-1))
 (459 459 (:REWRITE DEFAULT-CAR))
 (381 381 (:REWRITE DEFAULT-UNARY-MINUS))
 (184 184 (:LINEAR JVM::MEM-BASE-TYPES))
 (181 181 (:REWRITE DEL-SET-LEN))
 (181 181 (:REWRITE DEFAULT-NUMERATOR))
 (181 181 (:REWRITE DEFAULT-DENOMINATOR))
 (181 181 (:REWRITE DEFAULT-COERCE-2))
 (181 181 (:REWRITE DEFAULT-COERCE-1))
 (177 177 (:REWRITE DEFAULT-REALPART))
 (177 177 (:REWRITE DEFAULT-IMAGPART))
 )
(BCV::IS-SUFFIX-FORWARD-TO-NEXT-IS-SUFFIX
 (14 14 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(BCV::PC-WFF-MERGEDCODE1-NEVER-END-ON-A-STACKMAP
 (263 263 (:REWRITE DEFAULT-CAR))
 (125 125 (:REWRITE DEFAULT-CDR))
 (26 19 (:REWRITE DEFAULT-<-1))
 (23 16 (:REWRITE DEFAULT-+-2))
 (23 16 (:REWRITE DEFAULT-+-1))
 (22 11 (:DEFINITION NTH))
 (19 19 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BCV::PC-WFF-MERGEDCODE1-NEVER-AFTERGOTO
 (283 283 (:REWRITE DEFAULT-CAR))
 (135 135 (:REWRITE DEFAULT-CDR))
 (30 22 (:REWRITE DEFAULT-<-1))
 (29 20 (:REWRITE DEFAULT-+-2))
 (29 20 (:REWRITE DEFAULT-+-1))
 (26 13 (:DEFINITION NTH))
 (22 22 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BCV::PC-WFF-MERGEDCODE1-F
 (40 22 (:REWRITE DEFAULT-<-1))
 (37 26 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (22 22 (:REWRITE DEFAULT-<-2))
 (4 2 (:DEFINITION NTH))
 )
(BCV::MERGEDCODEISTYPESAFE-FORWARD-TO-NEXT-INST
 (1290 1241 (:REWRITE DEFAULT-CAR))
 (790 741 (:REWRITE DEFAULT-CDR))
 (74 37 (:DEFINITION NTH))
 (51 34 (:REWRITE DEFAULT-+-2))
 (51 34 (:REWRITE DEFAULT-+-1))
 (34 34 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 )
(BCV::MERGEDCODEISTYPESAFE-FORWARD-TO-NEXT-INST-B
 (81 77 (:REWRITE DEFAULT-CAR))
 (56 52 (:REWRITE DEFAULT-CDR))
 (37 5 (:REWRITE BCV::PC-WFF-MERGEDCODE1-NEVER-AFTERGOTO))
 (32 8 (:DEFINITION MV-NTH))
 (24 4 (:DEFINITION MEMBER-EQUAL))
 (20 20 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION BCV::SIG-DO-INST))
 (12 2 (:DEFINITION JVM::INST-SIZE))
 (10 2 (:DEFINITION JVM::INST-OPCODE))
 (6 3 (:DEFINITION NTH))
 (6 2 (:DEFINITION JVM::INST-INST))
 (4 4 (:TYPE-PRESCRIPTION BCV::INSTRUCTIONSATISFIESHANDLERS))
 (4 4 (:TYPE-PRESCRIPTION BCV::FRAMEISASSIGNABLE))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(BCV::FORWARD-TO-NEXT-INST-GET-INST-IF-PC-WFF-MERGED-CODE
 (202 202 (:REWRITE DEFAULT-CAR))
 (94 94 (:REWRITE DEFAULT-CDR))
 (23 12 (:REWRITE DEFAULT-<-1))
 (22 12 (:REWRITE DEFAULT-+-2))
 (13 12 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (2 1 (:DEFINITION NTH))
 )
(BCV::FORWARD-TO-NEXT-INST-GET-INST-IF-PC-WFF-MERGED-CODE-SPECIFIC
 (516 516 (:REWRITE DEFAULT-CAR))
 (241 241 (:REWRITE DEFAULT-CDR))
 (67 34 (:REWRITE DEFAULT-<-1))
 (65 51 (:REWRITE DEFAULT-+-2))
 (51 51 (:REWRITE DEFAULT-+-1))
 (34 34 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BCV::PC-WFF-MERGEDCODE1-NEVER-END-ON-A-STACKMAP))
 (2 1 (:DEFINITION NTH))
 )
(BCV::EXTRACT-CODE-FORWARD-NEXT-INST-REDUCE
 (213 213 (:REWRITE DEFAULT-CAR))
 (62 62 (:REWRITE DEFAULT-CDR))
 )
(BCV::TYPELIST-ASSIGNABLE-REFLEXIVE
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 5 (:DEFINITION NTH))
 (9 9 (:REWRITE DEFAULT-CDR))
 )
(BCV::FRAMEISASSIGNABLE-REFLEXIVE
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 6 (:DEFINITION NTH))
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE DEL-SET-LEN))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE SUBSET-TRANSITIVE))
 )
(BCV::IS-SUFFIX-IMPLIES-MEMBER-CODE
 (20 20 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
(BCV::MEMBER-EXTRACT-CODE-MEMBER
 (163 162 (:REWRITE DEFAULT-CAR))
 (51 50 (:REWRITE DEFAULT-CDR))
 (50 50 (:REWRITE BCV::IS-SUFFIX-IMPLIES-MEMBER-CODE))
 )
(BCV::FORWARD-TO-NEXT-INST-REDUCE
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(BCV::EXTRACT-CODE-FORWARD-TO-NEXT
 (20 2 (:DEFINITION BCV::EXTRACT-CODE))
 (12 12 (:REWRITE DEFAULT-CAR))
 (9 1 (:DEFINITION BCV::WFF-MERGED-CODE-WEAK))
 (8 8 (:REWRITE DEFAULT-CDR))
 (4 4 (:TYPE-PRESCRIPTION BCV::ISINSTRUCTION))
 (4 1 (:DEFINITION BCV::FORWARD-TO-NEXT-INST))
 (3 3 (:TYPE-PRESCRIPTION BCV::ISSTACKMAP))
 (2 2 (:TYPE-PRESCRIPTION BCV::ISEND))
 )
(BCV::PC-WFF-MERGEDCODE1-PC-WFF-MERGEDCODE-PC-SPECIFIC)
(BCV::IS-SUFFIX-CONSP-CONSP)
(BCV::IS-SUFFIX-NOT-END-NOT-END
 (25 25 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-CDR))
 )
(BCV::IS-SUFFIX-WFF-MERGECODE-WEAK
 (126 126 (:REWRITE DEFAULT-CAR))
 (74 74 (:REWRITE DEFAULT-CDR))
 )
(BCV::IS-SUFFIX-WFF-MERGED-CODE-INSTR
 (340 340 (:REWRITE DEFAULT-CAR))
 (146 146 (:REWRITE DEFAULT-CDR))
 )
(BCV::IS-SUFFIX-WFF-MERGED-CODE-INSTR-WFF-MERGED-CODE-INSTR
 (130 130 (:REWRITE DEFAULT-CAR))
 (52 52 (:REWRITE DEFAULT-CDR))
 (15 3 (:DEFINITION BCV::ISINSTRUCTION))
 (6 3 (:DEFINITION BCV::INSTROFFSET))
 )
(BCV::IS-SUFFIX-WFF-MERGED-CODE-INSTR-2
 (144 144 (:REWRITE DEFAULT-CDR))
 )
(BCV::MERGEDCODEISTYPESAFE-IMPLIES-BCV-SIMPLE-METHOD1-LEMMA
 (39447 687 (:DEFINITION BCV::COLLECT-SIG-FRAME-VECTOR))
 (20976 912 (:DEFINITION BCV::STACK-MAP-WRAP))
 (19742 17921 (:REWRITE DEFAULT-CDR))
 (16416 912 (:DEFINITION BCV::MAKESTACKMAP))
 (15517 913 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (9052 904 (:DEFINITION BCV::SEARCHSTACKFRAME))
 (6384 6384 (:TYPE-PRESCRIPTION LEN))
 (6328 242 (:REWRITE BCV::MERGEDCODEISTYPESAFE-IMPLIES-INSTRUCTIONISTYPESAFE))
 (4560 912 (:DEFINITION LEN))
 (3648 3648 (:LINEAR SUBSET-NODUP-SET-SIZE))
 (2054 1142 (:REWRITE DEFAULT-+-2))
 (1824 1824 (:TYPE-PRESCRIPTION BCV::COLLECT-SIG-FRAME-VECTOR))
 (1808 1808 (:TYPE-PRESCRIPTION BCV::STACK-MAP-WRAP))
 (1808 904 (:DEFINITION BCV::ISSTACKMAPFRAME))
 (1476 108 (:DEFINITION BCV::WFF-MERGED-CODE-WEAK))
 (1380 130 (:REWRITE BCV::IS-SUFFIX-WFF-MERGED-CODE-INSTR-2))
 (1148 133 (:DEFINITION BCV::EXTRACT-FRAMES))
 (1142 1142 (:REWRITE DEFAULT-+-1))
 (993 356 (:DEFINITION BCV::IS-SUFFIX))
 (955 84 (:DEFINITION BCV::WFF-MERGEDCODE-INSTR))
 (912 912 (:REWRITE DEL-SET-LEN))
 (905 59 (:REWRITE BCV::EXTRACT-CODE-FORWARD-NEXT-INST-REDUCE))
 (460 230 (:DEFINITION NTH))
 (410 19 (:REWRITE BCV::MERGEDCODEISTYPESAFE-IMPLIES-MERGEDCODEISTYPESAFE-SPECIFIC))
 (342 57 (:DEFINITION BCV::NEXT-INST))
 (288 18 (:DEFINITION BCV::NEVER-AFTER-GOTO))
 (115 115 (:REWRITE DEFAULT-<-2))
 (115 115 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE BCV::PC-WFF-MERGEDCODE1-NEVER-END-ON-A-STACKMAP))
 (19 19 (:REWRITE BCV::MERGEDCODEISTYPESAFE-IMPLIES-MERGEDCODEISTYPESAFE-2))
 (11 2 (:DEFINITION TRUE-LISTP))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(BCV::MERGEDCODEISTYPESAFE-IMPLIES-BCV-SIMPLE-METHOD1
 (184 8 (:DEFINITION BCV::STACK-MAP-WRAP))
 (158 152 (:REWRITE DEFAULT-CAR))
 (144 8 (:DEFINITION BCV::MAKESTACKMAP))
 (136 8 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (111 105 (:REWRITE DEFAULT-CDR))
 (56 56 (:TYPE-PRESCRIPTION LEN))
 (40 8 (:DEFINITION LEN))
 (40 4 (:DEFINITION BCV::EXTRACT-CODE))
 (32 32 (:LINEAR SUBSET-NODUP-SET-SIZE))
 (30 8 (:DEFINITION BCV::FORWARD-TO-NEXT-INST))
 (22 2 (:REWRITE BCV::MERGECODEISTYPESAFE-IMPLIES-COLLECT-SIG-VECTOR-COMPATIBLE-1))
 (20 12 (:REWRITE DEFAULT-+-2))
 (20 2 (:DEFINITION BCV::EXTRACT-FRAMES))
 (16 16 (:TYPE-PRESCRIPTION BCV::STACK-MAP-WRAP))
 (16 16 (:TYPE-PRESCRIPTION BCV::COLLECT-SIG-FRAME-VECTOR))
 (16 8 (:DEFINITION BCV::ISSTACKMAPFRAME))
 (12 12 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEL-SET-LEN))
 (8 4 (:DEFINITION NTH))
 (7 7 (:REWRITE BCV::IS-SUFFIX-IMPLIES-MEMBER-CODE))
 (6 6 (:REWRITE BCV::IS-SUFFIX-PC-EQUAL))
 (2 2 (:REWRITE BCV::MERGEDCODEISTYPESAFE-IMPLIES-BCV-SIMPLE-METHOD1-LEMMA))
 (2 2 (:REWRITE BCV::FRAMEISASSIGNABLE-TRANSITIVE-SPECIFIC))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
