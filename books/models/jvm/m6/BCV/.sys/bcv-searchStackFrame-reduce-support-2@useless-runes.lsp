(BCV::PC-WFF-MERGEDCODE1-STRICTLY-ORDERED-EXTRACT-PC-EXTRACT-CODE
 (241 236 (:REWRITE DEFAULT-CAR))
 (106 103 (:REWRITE DEFAULT-CDR))
 (35 23 (:REWRITE DEFAULT-<-1))
 (35 5 (:DEFINITION BCV::ALL-STRICTLY-LESS-THAN))
 (28 23 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (18 9 (:DEFINITION NTH))
 (17 10 (:REWRITE DEFAULT-+-2))
 (12 10 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 )
(BCV::STRICTLY-ORDERED-NEXT-INST
 (362 347 (:REWRITE DEFAULT-CAR))
 (212 205 (:REWRITE DEFAULT-CDR))
 (64 64 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (64 32 (:REWRITE DEFAULT-<-2))
 (64 32 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE BCV::PC-WFF-MERGEDCODE1-STRICTLY-ORDERED-EXTRACT-PC-EXTRACT-CODE))
 (5 5 (:REWRITE BCV::PC-WFF-MERGEDCODE1-ISINSTRUCTION-THEN-NEXT-PC-IS-GREATER))
 )
(BCV::NEXT-INST-NEVER-OCCUR-BEFORE
 (39 1 (:DEFINITION BCV::PC-WFF-MERGEDCODE1))
 (25 25 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (13 1 (:DEFINITION BCV::EXTRACT-PC))
 (12 2 (:DEFINITION BCV::NEXT-INST))
 (10 1 (:DEFINITION BCV::EXTRACT-CODE))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:TYPE-PRESCRIPTION JVM::INST-SIZE))
 (3 2 (:REWRITE DEFAULT-<-1))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (3 1 (:DEFINITION BCV::MAPFRAME))
 (2 2 (:TYPE-PRESCRIPTION BCV::EXTRACT-CODE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 1 (:DEFINITION NTH))
 )
(BCV::MEMBER-INST-PC-NO-LESS-THAN
 (311 311 (:REWRITE DEFAULT-CAR))
 (99 56 (:REWRITE DEFAULT-<-1))
 (75 75 (:REWRITE DEFAULT-CDR))
 (71 56 (:REWRITE DEFAULT-<-2))
 (47 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (31 17 (:REWRITE DEFAULT-+-2))
 (28 14 (:DEFINITION NTH))
 (19 17 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 )
(BCV::MEMBER-INST-PC-NO-LESS-THAN-SPECIFIC)
(BCV::STRICTLY-ORDERED-NEXT-INST-SPECIFIC
 (1594 1434 (:REWRITE DEFAULT-CAR))
 (825 740 (:REWRITE DEFAULT-CDR))
 (250 250 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (250 125 (:REWRITE DEFAULT-<-2))
 (250 125 (:REWRITE DEFAULT-<-1))
 (58 58 (:REWRITE BCV::PC-WFF-MERGEDCODE1-STRICTLY-ORDERED-EXTRACT-PC-EXTRACT-CODE))
 (32 32 (:LINEAR BCV::MEMBER-INST-PC-NO-LESS-THAN))
 (8 8 (:REWRITE BCV::PC-WFF-MERGEDCODE1-ISINSTRUCTION-THEN-NEXT-PC-IS-GREATER))
 )
(BCV::PC-WFF-MERGEDCODE1-ALL-GREATER-THAN)
(BCV::NOT-PC-WFF-MERGECODE1-IF-MEMBER
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 4 (:REWRITE DEFAULT-<-1))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION NTH))
 )
(BCV::MERGECODEISTYPESAFE-IMPLIES-COLLECT-SIG-VECTOR-COMPATIBLE-1
 (14578 13160 (:REWRITE DEFAULT-CAR))
 (9228 8146 (:REWRITE DEFAULT-CDR))
 (4200 210 (:REWRITE JVM::TRUE-LISTP-LEN-1-IS-LIST-CAR))
 (1470 1470 (:TYPE-PRESCRIPTION LEN))
 (1470 210 (:DEFINITION LEN))
 (1270 724 (:REWRITE DEFAULT-+-2))
 (968 513 (:REWRITE DEFAULT-<-1))
 (840 840 (:LINEAR SUBSET-NODUP-SET-SIZE))
 (749 724 (:REWRITE DEFAULT-+-1))
 (513 513 (:REWRITE DEFAULT-<-2))
 (361 361 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (210 210 (:REWRITE DEL-SET-LEN))
 (116 58 (:DEFINITION NTH))
 (100 25 (:REWRITE COMMUTATIVITY-OF-+))
 (65 65 (:LINEAR BCV::MEMBER-INST-PC-NO-LESS-THAN))
 (26 26 (:LINEAR BCV::NEXT-INST-NEVER-OCCUR-BEFORE))
 )
