(ADE::FIX-BREADTH-TREE-STACK
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(ADE::TRUE-LIST-LISTP-FIX-BREADTH-TREE-STACK
 (42 14 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (39 3 (:DEFINITION BINARY-APPEND))
 (35 7 (:DEFINITION TRUE-LISTP))
 (28 28 (:TYPE-PRESCRIPTION ADE::BVP))
 (28 18 (:REWRITE DEFAULT-CDR))
 (24 14 (:REWRITE DEFAULT-CAR))
 (15 9 (:REWRITE CONSP-OF-REPEAT))
 (12 3 (:REWRITE REPEAT-WHEN-ZP))
 (6 6 (:TYPE-PRESCRIPTION ZP))
 (6 6 (:REWRITE ZP-OPEN))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(ADE::BREADTH-TREE)
(ADE::TRUE-LIST-LISTP-BREADTH-TREE
 (72 24 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (68 12 (:DEFINITION TRUE-LISTP))
 (65 54 (:REWRITE DEFAULT-CDR))
 (61 5 (:DEFINITION ADE::FIX-BREADTH-TREE-STACK))
 (58 49 (:REWRITE DEFAULT-CAR))
 (48 48 (:TYPE-PRESCRIPTION ADE::BVP))
 (44 15 (:DEFINITION BINARY-APPEND))
 (44 9 (:REWRITE REPEAT-WHEN-ZP))
 (27 20 (:REWRITE DEFAULT-*-2))
 (20 20 (:REWRITE DEFAULT-*-1))
 (19 9 (:REWRITE ZP-OPEN))
 (16 16 (:TYPE-PRESCRIPTION ZP))
 (11 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 (10 2 (:REWRITE DISTRIBUTIVITY))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ADE::COLLECT-BREADTH-TREE
 (6 2 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION ADE::BVP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ADE::TREE-NUMBER)
(ADE::NATP-TREE-NUMBER)
