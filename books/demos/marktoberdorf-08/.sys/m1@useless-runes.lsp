(M1::PUSH)
(M1::TOP)
(M1::POP)
(M1::OPCODE)
(M1::ARG1)
(M1::ARG2)
(M1::ARG3)
(M1::MAKE-STATE)
(M1::PC)
(M1::LOCALS)
(M1::STACK)
(M1::PROGRAM)
(M1::NEXT-INST)
(M1::EXECUTE-PUSH)
(M1::EXECUTE-LOAD)
(M1::EXECUTE-ADD)
(M1::EXECUTE-STORE
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(M1::EXECUTE-SUB)
(M1::EXECUTE-MUL)
(M1::EXECUTE-GOTO)
(M1::EXECUTE-IFLE)
(M1::EXECUTE-IFLT)
(M1::EXECUTE-IFNE)
(M1::EXECUTE-IFANE)
(M1::EXECUTE-ALOAD)
(M1::DO-INST)
(M1::STEP
 (1 1 (:TYPE-PRESCRIPTION M1::STEP))
 )
(M1::HALTEDP
 (5 5 (:TYPE-PRESCRIPTION M1::STEP))
 )
(M1::RUN
 (6 6 (:TYPE-PRESCRIPTION M1::STEP))
 )
(M1::REPEAT)
(M1::STACKS)
(M1::STATES)
(M1::STEP-OPENER
 (170 49 (:DEFINITION NTH))
 (113 63 (:REWRITE DEFAULT-+-2))
 (92 92 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (89 63 (:REWRITE DEFAULT-+-1))
 (55 11 (:REWRITE ZP-OPEN))
 (35 35 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE DEFAULT-CDR))
 (28 28 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (28 28 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (22 2 (:DEFINITION UPDATE-NTH))
 (21 17 (:REWRITE DEFAULT-<-1))
 (19 19 (:TYPE-PRESCRIPTION M1::STEP))
 (19 19 (:TYPE-PRESCRIPTION M1::DO-INST))
 (19 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:META CANCEL_PLUS-LESSP-CORRECT))
 (16 2 (:REWRITE DEFAULT-CHAR-CODE))
 (14 2 (:REWRITE CHARACTERP-NTH))
 (8 4 (:REWRITE DEFAULT-*-2))
 (8 4 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE CHARACTER-LISTP-COERCE))
 )
(M1::RUN-OPENER
 (60 5 (:REWRITE M1::STEP-OPENER))
 (55 5 (:DEFINITION M1::NEXT-INST))
 (50 5 (:DEFINITION NTH))
 (25 5 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 5 (:DEFINITION NOT))
 )
(M1::RUN-APPEND
 (168 14 (:REWRITE M1::STEP-OPENER))
 (154 14 (:DEFINITION M1::NEXT-INST))
 (140 14 (:DEFINITION NTH))
 (70 14 (:REWRITE ZP-OPEN))
 (28 28 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-CAR))
 (16 8 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-+-1))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(M1::NTH-ADD1!
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(M1::UPDATE-NTH-ADD1!
 (7 7 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NATP-RW))
 )
