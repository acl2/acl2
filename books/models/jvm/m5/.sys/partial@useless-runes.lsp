(M5::UPDATE-NTH-OPENER
 (25 25 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (17 3 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 7 (:REWRITE DEFAULT-+-2))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(M5::INT-EVENP-INV-A
 (1141 144 (:REWRITE M5::INT-LEMMA0))
 (465 17 (:REWRITE FLOOR-=-X/Y . 3))
 (418 197 (:REWRITE DEFAULT-*-2))
 (408 2 (:REWRITE <-*-/-LEFT-COMMUTED))
 (397 397 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (397 397 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (397 397 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (289 17 (:REWRITE FLOOR-=-X/Y . 2))
 (286 197 (:REWRITE DEFAULT-*-1))
 (276 90 (:REWRITE DEFAULT-+-2))
 (232 34 (:REWRITE CANCEL-FLOOR-+-BASIC))
 (230 110 (:REWRITE DEFAULT-<-1))
 (200 200 (:META CANCEL_PLUS-LESSP-CORRECT))
 (176 44 (:REWRITE <-0-+-NEGATIVE-1))
 (176 44 (:REWRITE <-+-NEGATIVE-0-1))
 (136 17 (:REWRITE FLOOR-TYPE-4 . 3))
 (136 17 (:REWRITE FLOOR-TYPE-4 . 2))
 (136 17 (:REWRITE FLOOR-TYPE-3 . 3))
 (136 17 (:REWRITE FLOOR-TYPE-3 . 2))
 (110 110 (:REWRITE DEFAULT-<-2))
 (91 90 (:REWRITE DEFAULT-+-1))
 (91 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 4 (:LINEAR FLOOR-TYPE-2 . 2))
 (32 4 (:LINEAR FLOOR-TYPE-2 . 1))
 (32 4 (:LINEAR FLOOR-TYPE-1 . 2))
 (32 4 (:LINEAR FLOOR-TYPE-1 . 1))
 (28 1 (:REWRITE MOD-=-0 . 2))
 (14 2 (:REWRITE CANCEL-MOD-+-BASIC))
 (8 1 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (8 1 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (8 1 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (8 1 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 )
(M5::INT-EVENP-INV-B
 (30 8 (:REWRITE M5::INT-LEMMA0))
 (8 7 (:REWRITE DEFAULT-*-2))
 (8 7 (:REWRITE DEFAULT-*-1))
 (7 1 (:REWRITE M5::INT-LEMMA3))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(M5::INT-LEMMA2A
 (29 29 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (10 3 (:REWRITE M5::INT-LEMMA0))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(M5::INT-LEMMA2B
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (10 3 (:REWRITE M5::INT-LEMMA0))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(M5::HALFA
 (28 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (15 2 (:REWRITE O<=-O-FINP-DEF))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (5 1 (:REWRITE O-FIRST-EXPT-<))
 (4 2 (:REWRITE O-INFP-O-FINP-O<=))
 (4 2 (:REWRITE AC-<))
 (3 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (3 1 (:REWRITE M5::INT-LEMMA0))
 (2 2 (:TYPE-PRESCRIPTION M5::INTP))
 (2 2 (:REWRITE |a < b & b < c  =>  a < c|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE O-FIRST-COEFF-<))
 )
(M5::HALF-ASSERTION)
(M5::|HALF-INV-arity-1-defpun-test|)
(M5::|HALF-INV-arity-1-defpun-base|)
(M5::|HALF-INV-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::|HALF-INV-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(M5::|HALF-INV-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE M5::INT-LEMMA0))
 (2 2 (:TYPE-PRESCRIPTION M5::INTP))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(M5::|HALF-INV-arity-1|
 (1 1 (:TYPE-PRESCRIPTION M5::|HALF-INV-arity-1-defpun-stn|))
 )
(M5::|HALF-INV-arity-1-DEF|)
(M5::HALF-INV)
(M5::HALF-INV-DEF
 (1122 102 (:DEFINITION ASSOC-EQUAL))
 (896 2 (:REWRITE M5::STEP-OPENER))
 (894 2 (:DEFINITION M5::NEXT-INST))
 (877 461 (:REWRITE DEFAULT-CAR))
 (824 2 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (794 2 (:DEFINITION M5::INST-LENGTH))
 (517 517 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (517 517 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (416 104 (:REWRITE O-P-O-INFP-CAR))
 (234 234 (:REWRITE DEFAULT-CDR))
 (104 104 (:REWRITE O-P-DEF-O-FINP-1))
 (39 24 (:REWRITE DEFAULT-<-1))
 (27 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 24 (:META CANCEL_PLUS-LESSP-CORRECT))
 (19 16 (:REWRITE DEFAULT-+-2))
 (19 16 (:REWRITE DEFAULT-+-1))
 (12 2 (:REWRITE O-INFP->NEQ-0))
 (12 2 (:DEFINITION M5::OP-CODE))
 (9 3 (:REWRITE M5::INT-LEMMA6))
 (6 6 (:TYPE-PRESCRIPTION O-FINP))
 (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::HALF-INV-MAKE-STATE-OPENER
 (2246 5 (:REWRITE M5::STEP-OPENER))
 (2241 5 (:DEFINITION M5::NEXT-INST))
 (2060 5 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1985 5 (:DEFINITION M5::INST-LENGTH))
 (1048 1048 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1048 1048 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (692 6 (:DEFINITION M5::HALF-ASSERTION))
 (572 52 (:DEFINITION ASSOC-EQUAL))
 (463 235 (:REWRITE DEFAULT-CAR))
 (228 57 (:REWRITE O-P-O-INFP-CAR))
 (115 115 (:REWRITE DEFAULT-CDR))
 (58 11 (:REWRITE ZP-OPEN))
 (57 57 (:REWRITE O-P-DEF-O-FINP-1))
 (56 6 (:DEFINITION M5::HALFA))
 (30 5 (:DEFINITION M5::OP-CODE))
 (20 20 (:TYPE-PRESCRIPTION M5::INTP))
 (19 13 (:REWRITE DEFAULT-<-1))
 (18 3 (:REWRITE O-INFP->NEQ-0))
 (17 15 (:REWRITE DEFAULT-+-2))
 (17 15 (:REWRITE DEFAULT-+-1))
 (17 7 (:REWRITE M5::INT-LEMMA0))
 (15 13 (:REWRITE DEFAULT-<-2))
 (14 14 (:TYPE-PRESCRIPTION EVENP))
 (14 6 (:DEFINITION IFF))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:TYPE-PRESCRIPTION M5::HALFA))
 (9 9 (:TYPE-PRESCRIPTION O-FINP))
 (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (6 2 (:REWRITE M5::INT-LEMMA6))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(M5::HALF-INV-STEP
 (3322 302 (:DEFINITION ASSOC-EQUAL))
 (3192 1828 (:REWRITE DEFAULT-CAR))
 (2472 6 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (2382 6 (:DEFINITION M5::INST-LENGTH))
 (1608 1608 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1608 1608 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1364 341 (:REWRITE O-P-O-INFP-CAR))
 (1248 1248 (:REWRITE DEFAULT-CDR))
 (396 33 (:DEFINITION M5::BIND))
 (341 341 (:REWRITE O-P-DEF-O-FINP-1))
 (97 79 (:REWRITE DEFAULT-+-2))
 (94 79 (:REWRITE DEFAULT-+-1))
 (79 64 (:REWRITE DEFAULT-<-1))
 (70 64 (:REWRITE DEFAULT-<-2))
 (67 67 (:META CANCEL_PLUS-LESSP-CORRECT))
 (58 13 (:REWRITE O-INFP->NEQ-0))
 (55 17 (:REWRITE M5::INT-LEMMA6))
 (47 47 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (36 6 (:DEFINITION M5::OP-CODE))
 (30 14 (:REWRITE M5::INT-LEMMA0))
 (27 27 (:TYPE-PRESCRIPTION O-FINP))
 (27 9 (:REWRITE O-FIRST-EXPT-O-INFP))
 (18 9 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (8 2 (:REWRITE M5::INT-LEMMA5A))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(M5::MONO-THREADEDP)
(M5::HALF-INV-RUN
 (1792 4 (:REWRITE M5::STEP-OPENER))
 (1788 4 (:DEFINITION M5::NEXT-INST))
 (1648 4 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1588 4 (:DEFINITION M5::INST-LENGTH))
 (794 794 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (794 794 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (136 8 (:DEFINITION M5::TOP-FRAME))
 (128 8 (:DEFINITION M5::CALL-STACK))
 (104 8 (:DEFINITION M5::BINDING))
 (103 55 (:REWRITE DEFAULT-CAR))
 (88 8 (:DEFINITION ASSOC-EQUAL))
 (48 12 (:REWRITE O-P-O-INFP-CAR))
 (32 4 (:REWRITE ZP-OPEN))
 (24 24 (:TYPE-PRESCRIPTION O-P))
 (24 24 (:REWRITE DEFAULT-CDR))
 (24 4 (:DEFINITION M5::OP-CODE))
 (16 8 (:REWRITE M5::NTH-OPENER))
 (12 12 (:REWRITE O-P-DEF-O-FINP-1))
 (12 4 (:REWRITE M5::INT-LEMMA0))
 (8 8 (:TYPE-PRESCRIPTION M5::INTP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(M5::HALF-MAIN
 (748 68 (:DEFINITION ASSOC-EQUAL))
 (614 314 (:REWRITE DEFAULT-CAR))
 (448 1 (:REWRITE M5::STEP-OPENER))
 (447 1 (:DEFINITION M5::NEXT-INST))
 (412 1 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (397 1 (:DEFINITION M5::INST-LENGTH))
 (300 75 (:REWRITE O-P-O-INFP-CAR))
 (285 285 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (285 285 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (182 182 (:REWRITE DEFAULT-CDR))
 (75 75 (:REWRITE O-P-DEF-O-FINP-1))
 (72 6 (:DEFINITION M5::BIND))
 (36 5 (:DEFINITION M5::HALFA))
 (19 6 (:REWRITE ZP-OPEN))
 (13 1 (:REWRITE M5::HALF-INV-MAKE-STATE-OPENER))
 (9 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (8 7 (:REWRITE DEFAULT-<-2))
 (8 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
 (7 3 (:DEFINITION IFF))
 (6 1 (:REWRITE O-INFP->NEQ-0))
 (6 1 (:DEFINITION M5::OP-CODE))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE M5::INT-LEMMA0))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:TYPE-PRESCRIPTION O-FINP))
 (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
 (3 1 (:REWRITE M5::INT-LEMMA6))
 (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:REWRITE M5::HALF-INV-STEP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(M5::INT-BACK
 (23 7 (:REWRITE M5::INT-LEMMA0))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(M5::HALFA-IS-HALF
 (50 48 (:REWRITE DEFAULT-+-2))
 (48 48 (:REWRITE DEFAULT-+-1))
 (43 43 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (27 9 (:REWRITE M5::INT-LEMMA0))
 (24 21 (:REWRITE DEFAULT-*-2))
 (21 21 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE EQUAL-CONSTANT-+))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(M5::INTP-HALF-N
 (11 4 (:REWRITE M5::INT-LEMMA0))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(M5::HALF-IS-PARTIALLY-CORRECT
 (275 25 (:DEFINITION ASSOC-EQUAL))
 (231 115 (:REWRITE DEFAULT-CAR))
 (116 29 (:REWRITE O-P-O-INFP-CAR))
 (73 73 (:REWRITE DEFAULT-CDR))
 (48 4 (:DEFINITION M5::BIND))
 (37 37 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (37 37 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (29 29 (:REWRITE O-P-DEF-O-FINP-1))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(M5::SUMA
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(M5::SUM-ASSERTION)
(M5::|SUM-INV-arity-1-defpun-test|)
(M5::|SUM-INV-arity-1-defpun-base|)
(M5::|SUM-INV-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::|SUM-INV-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(M5::|SUM-INV-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE M5::INT-LEMMA0))
 (2 2 (:TYPE-PRESCRIPTION M5::INTP))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(M5::|SUM-INV-arity-1|
 (1 1 (:TYPE-PRESCRIPTION M5::|SUM-INV-arity-1-defpun-stn|))
 )
(M5::|SUM-INV-arity-1-DEF|)
(M5::SUM-INV)
(M5::SUM-INV-DEF
 (896 2 (:REWRITE M5::STEP-OPENER))
 (894 2 (:DEFINITION M5::NEXT-INST))
 (847 77 (:DEFINITION ASSOC-EQUAL))
 (824 2 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (794 2 (:DEFINITION M5::INST-LENGTH))
 (667 351 (:REWRITE DEFAULT-CAR))
 (489 489 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (489 489 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (316 79 (:REWRITE O-P-O-INFP-CAR))
 (179 179 (:REWRITE DEFAULT-CDR))
 (85 6 (:DEFINITION M5::SUMA))
 (79 79 (:REWRITE O-P-DEF-O-FINP-1))
 (33 8 (:REWRITE ZP-OPEN))
 (22 14 (:REWRITE DEFAULT-<-1))
 (20 18 (:REWRITE DEFAULT-+-2))
 (20 4 (:REWRITE COMMUTATIVITY-OF-+))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 14 (:REWRITE DEFAULT-<-2))
 (16 6 (:REWRITE M5::INT-LEMMA6))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 2 (:REWRITE O-INFP->NEQ-0))
 (12 2 (:DEFINITION M5::OP-CODE))
 (8 4 (:REWRITE UNICITY-OF-0))
 (8 4 (:REWRITE M5::INT-LEMMA0))
 (6 6 (:TYPE-PRESCRIPTION O-FINP))
 (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
 (4 4 (:DEFINITION FIX))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (2 2 (:REWRITE M5::INT-BACK))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::SUM-INV-MAKE-STATE-OPENER
 (2246 5 (:REWRITE M5::STEP-OPENER))
 (2241 5 (:DEFINITION M5::NEXT-INST))
 (2060 5 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1985 5 (:DEFINITION M5::INST-LENGTH))
 (1048 1048 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1048 1048 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (700 6 (:DEFINITION M5::SUM-ASSERTION))
 (572 52 (:DEFINITION ASSOC-EQUAL))
 (463 235 (:REWRITE DEFAULT-CAR))
 (228 57 (:REWRITE O-P-O-INFP-CAR))
 (115 115 (:REWRITE DEFAULT-CDR))
 (86 6 (:DEFINITION M5::SUMA))
 (58 11 (:REWRITE ZP-OPEN))
 (57 57 (:REWRITE O-P-DEF-O-FINP-1))
 (30 5 (:DEFINITION M5::OP-CODE))
 (24 24 (:TYPE-PRESCRIPTION M5::INTP))
 (23 21 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-+-1))
 (20 4 (:REWRITE COMMUTATIVITY-OF-+))
 (19 13 (:REWRITE DEFAULT-<-1))
 (18 3 (:REWRITE O-INFP->NEQ-0))
 (17 13 (:REWRITE DEFAULT-<-2))
 (17 7 (:REWRITE M5::INT-LEMMA0))
 (16 6 (:REWRITE M5::INT-LEMMA6))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:TYPE-PRESCRIPTION O-FINP))
 (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (8 4 (:REWRITE UNICITY-OF-0))
 (6 6 (:TYPE-PRESCRIPTION M5::SUMA))
 (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:DEFINITION FIX))
 (2 2 (:REWRITE M5::INT-BACK))
 )
(M5::SUM-INV-STEP
 (2332 212 (:DEFINITION ASSOC-EQUAL))
 (2159 1219 (:REWRITE DEFAULT-CAR))
 (1648 4 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1588 4 (:DEFINITION M5::INST-LENGTH))
 (1079 1079 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1079 1079 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (940 235 (:REWRITE O-P-O-INFP-CAR))
 (797 797 (:REWRITE DEFAULT-CDR))
 (235 235 (:REWRITE O-P-DEF-O-FINP-1))
 (228 19 (:DEFINITION M5::BIND))
 (113 94 (:REWRITE DEFAULT-+-2))
 (96 94 (:REWRITE DEFAULT-+-1))
 (55 45 (:REWRITE DEFAULT-<-1))
 (54 45 (:REWRITE DEFAULT-<-2))
 (48 48 (:META CANCEL_PLUS-LESSP-CORRECT))
 (44 9 (:REWRITE O-INFP->NEQ-0))
 (38 19 (:REWRITE UNICITY-OF-0))
 (29 29 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 10 (:REWRITE M5::INT-LEMMA0))
 (24 4 (:DEFINITION M5::OP-CODE))
 (21 21 (:TYPE-PRESCRIPTION O-FINP))
 (21 21 (:REWRITE M5::INT-BACK))
 (21 7 (:REWRITE O-FIRST-EXPT-O-INFP))
 (20 20 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (19 19 (:DEFINITION FIX))
 (16 2 (:REWRITE ASSOCIATIVITY-OF-+))
 (14 7 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (10 2 (:REWRITE M5::INT-LEMMA5A1))
 (8 4 (:REWRITE FOLD-CONSTS-IN-+))
 (8 2 (:REWRITE M5::INT-LEMMA2))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(M5::SUM-INV-RUN
 (1792 4 (:REWRITE M5::STEP-OPENER))
 (1788 4 (:DEFINITION M5::NEXT-INST))
 (1648 4 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1588 4 (:DEFINITION M5::INST-LENGTH))
 (794 794 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (794 794 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (136 8 (:DEFINITION M5::TOP-FRAME))
 (128 8 (:DEFINITION M5::CALL-STACK))
 (104 8 (:DEFINITION M5::BINDING))
 (103 55 (:REWRITE DEFAULT-CAR))
 (88 8 (:DEFINITION ASSOC-EQUAL))
 (48 12 (:REWRITE O-P-O-INFP-CAR))
 (32 4 (:REWRITE ZP-OPEN))
 (24 24 (:TYPE-PRESCRIPTION O-P))
 (24 24 (:REWRITE DEFAULT-CDR))
 (24 4 (:DEFINITION M5::OP-CODE))
 (16 8 (:REWRITE M5::NTH-OPENER))
 (12 12 (:REWRITE O-P-DEF-O-FINP-1))
 (12 4 (:REWRITE M5::INT-LEMMA0))
 (8 8 (:TYPE-PRESCRIPTION M5::INTP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(M5::SUM-MAIN
 (605 55 (:DEFINITION ASSOC-EQUAL))
 (501 257 (:REWRITE DEFAULT-CAR))
 (448 1 (:REWRITE M5::STEP-OPENER))
 (447 1 (:DEFINITION M5::NEXT-INST))
 (412 1 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (397 1 (:DEFINITION M5::INST-LENGTH))
 (270 270 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (270 270 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (244 61 (:REWRITE O-P-O-INFP-CAR))
 (150 150 (:REWRITE DEFAULT-CDR))
 (65 5 (:DEFINITION M5::SUMA))
 (61 61 (:REWRITE O-P-DEF-O-FINP-1))
 (60 5 (:DEFINITION M5::BIND))
 (20 4 (:REWRITE COMMUTATIVITY-OF-+))
 (19 6 (:REWRITE ZP-OPEN))
 (16 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (13 1 (:REWRITE M5::SUM-INV-MAKE-STATE-OPENER))
 (9 7 (:REWRITE DEFAULT-<-2))
 (8 7 (:REWRITE DEFAULT-<-1))
 (8 5 (:REWRITE M5::INT-LEMMA6))
 (8 4 (:REWRITE UNICITY-OF-0))
 (7 7 (:META CANCEL_PLUS-LESSP-CORRECT))
 (6 1 (:REWRITE O-INFP->NEQ-0))
 (6 1 (:DEFINITION M5::OP-CODE))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:DEFINITION FIX))
 (4 2 (:REWRITE M5::INT-LEMMA0))
 (3 3 (:TYPE-PRESCRIPTION O-FINP))
 (3 1 (:REWRITE O-FIRST-EXPT-O-INFP))
 (2 1 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:REWRITE M5::SUM-INV-STEP))
 (1 1 (:REWRITE M5::INT-BACK))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(M5::FACT-CALLER-FRAMESP
 (34 34 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (31 31 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(M5::STACK-PRODUCT
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(M5::INTEGERP-STACK-PRODUCT
 (43 26 (:REWRITE DEFAULT-+-2))
 (41 27 (:REWRITE DEFAULT-*-2))
 (40 27 (:REWRITE DEFAULT-*-1))
 (30 26 (:REWRITE DEFAULT-+-1))
 (30 10 (:REWRITE M5::INT-LEMMA0))
 (20 20 (:TYPE-PRESCRIPTION M5::INTP))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(M5::SDEPTH)
(M5::FACT-ASSERTION
 (11 11 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(M5::|FACT-INV-arity-1-defpun-test|)
(M5::|FACT-INV-arity-1-defpun-base|)
(M5::|FACT-INV-arity-1-step|
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::|FACT-INV-arity-1-defpun-stn|
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(M5::|FACT-INV-arity-1-defpun-fn|
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 1 (:REWRITE O<=-O-FINP-DEF))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE M5::INT-LEMMA0))
 (2 2 (:TYPE-PRESCRIPTION M5::INTP))
 (2 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 1 (:REWRITE AC-<))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(M5::|FACT-INV-arity-1|
 (1 1 (:TYPE-PRESCRIPTION M5::|FACT-INV-arity-1-defpun-stn|))
 )
(M5::|FACT-INV-arity-1-DEF|)
(M5::FACT-INV)
(M5::FACT-INV-DEF
 (4423 2231 (:REWRITE DEFAULT-CAR))
 (3644 790 (:REWRITE O-P-O-INFP-CAR))
 (1516 1516 (:REWRITE DEFAULT-CDR))
 (1274 790 (:REWRITE O-P-DEF-O-FINP-1))
 (1104 1104 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1104 1104 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (990 99 (:DEFINITION M5::SDEPTH))
 (896 2 (:REWRITE M5::STEP-OPENER))
 (894 2 (:DEFINITION M5::NEXT-INST))
 (890 10 (:DEFINITION M5::STACK-PRODUCT))
 (824 2 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (794 2 (:DEFINITION M5::INST-LENGTH))
 (490 490 (:TYPE-PRESCRIPTION O-FINP))
 (470 292 (:REWRITE DEFAULT-+-2))
 (385 292 (:REWRITE DEFAULT-+-1))
 (360 20 (:REWRITE COMMUTATIVITY-OF-*))
 (308 164 (:REWRITE DEFAULT-<-1))
 (300 10 (:REWRITE DISTRIBUTIVITY))
 (296 27 (:DEFINITION M5::FACTORIAL))
 (289 289 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (253 164 (:REWRITE DEFAULT-<-2))
 (231 87 (:REWRITE DEFAULT-*-2))
 (197 87 (:REWRITE DEFAULT-*-1))
 (187 187 (:META CANCEL_PLUS-LESSP-CORRECT))
 (180 90 (:TYPE-PRESCRIPTION M5::INTEGERP-STACK-PRODUCT))
 (151 151 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (137 87 (:REWRITE DEFAULT-UNARY-MINUS))
 (136 136 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (113 40 (:REWRITE M5::INT-LEMMA0))
 (90 90 (:TYPE-PRESCRIPTION M5::STACK-PRODUCT))
 (81 27 (:REWRITE M5::INT-LEMMA6))
 (59 59 (:REWRITE FOLD-CONSTS-IN-+))
 (50 10 (:REWRITE UNICITY-OF-1))
 (50 10 (:REWRITE COMMUTATIVITY-OF-+))
 (50 10 (:REWRITE COMMUTATIVITY-2-OF-+))
 (37 37 (:TYPE-PRESCRIPTION M5::INTEGERP-FACTORIAL))
 (37 37 (:TYPE-PRESCRIPTION M5::FACTORIAL))
 (23 23 (:REWRITE M5::INT-BACK))
 (20 20 (:REWRITE EQUAL-CONSTANT-+))
 (12 2 (:REWRITE O-INFP->NEQ-0))
 (12 2 (:DEFINITION M5::OP-CODE))
 (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (1 1 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::FACT-INV-MAKE-STATE-OPENER
 (11788 8 (:DEFINITION M5::FACT-ASSERTION))
 (10310 29 (:REWRITE M5::STEP-OPENER))
 (10281 23 (:DEFINITION M5::NEXT-INST))
 (9476 23 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (9264 6 (:DEFINITION M5::LOOKUP-METHOD))
 (9156 12 (:DEFINITION M5::LOOKUP-METHOD-IN-SUPERCLASSES))
 (9131 23 (:DEFINITION M5::INST-LENGTH))
 (4734 4734 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4734 4734 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2036 172 (:DEFINITION ASSOC-EQUAL))
 (1549 769 (:REWRITE DEFAULT-CAR))
 (1068 243 (:REWRITE O-P-O-INFP-CAR))
 (534 6 (:DEFINITION M5::STACK-PRODUCT))
 (451 451 (:REWRITE DEFAULT-CDR))
 (442 53 (:REWRITE ZP-OPEN))
 (432 30 (:DEFINITION M5::BOUND?))
 (339 243 (:REWRITE O-P-DEF-O-FINP-1))
 (330 6 (:DEFINITION M5::FACT-CALLER-FRAMESP))
 (216 12 (:REWRITE COMMUTATIVITY-OF-*))
 (204 18 (:DEFINITION M5::FACTORIAL))
 (203 143 (:REWRITE DEFAULT-+-2))
 (197 143 (:REWRITE DEFAULT-+-1))
 (180 18 (:DEFINITION M5::SDEPTH))
 (180 6 (:REWRITE DISTRIBUTIVITY))
 (156 12 (:DEFINITION M5::CLASS-DECL-METHODS))
 (144 54 (:REWRITE DEFAULT-*-2))
 (140 140 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (138 23 (:DEFINITION M5::OP-CODE))
 (127 45 (:REWRITE M5::INT-LEMMA0))
 (124 124 (:TYPE-PRESCRIPTION M5::INTP))
 (120 54 (:REWRITE DEFAULT-*-1))
 (108 54 (:TYPE-PRESCRIPTION M5::INTEGERP-STACK-PRODUCT))
 (107 69 (:REWRITE DEFAULT-<-2))
 (105 105 (:TYPE-PRESCRIPTION O-FINP))
 (105 69 (:REWRITE DEFAULT-<-1))
 (96 12 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (95 65 (:REWRITE DEFAULT-UNARY-MINUS))
 (81 81 (:META CANCEL_PLUS-LESSP-CORRECT))
 (78 78 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (72 72 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (72 12 (:REWRITE <-0-+-NEGATIVE-2))
 (60 30 (:DEFINITION FIX))
 (54 54 (:TYPE-PRESCRIPTION M5::STACK-PRODUCT))
 (54 18 (:REWRITE M5::INT-LEMMA6))
 (36 12 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
 (34 34 (:TYPE-PRESCRIPTION M5::INT-FIX))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (30 6 (:REWRITE UNICITY-OF-1))
 (30 6 (:REWRITE COMMUTATIVITY-OF-+))
 (30 6 (:REWRITE COMMUTATIVITY-2-OF-+))
 (30 6 (:DEFINITION M5::CLASS-DECL-SUPERCLASSES))
 (24 24 (:TYPE-PRESCRIPTION M5::INTEGERP-FACTORIAL))
 (24 24 (:TYPE-PRESCRIPTION M5::FACTORIAL))
 (24 12 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (18 3 (:REWRITE O-INFP->NEQ-0))
 (12 12 (:REWRITE M5::INT-BACK))
 (12 12 (:REWRITE EQUAL-CONSTANT-+))
 (9 3 (:REWRITE O-FIRST-EXPT-O-INFP))
 (6 6 (:TYPE-PRESCRIPTION M5::FACT-CALLER-FRAMESP))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (6 3 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 )
(M5::KB-HACK1
 (23 23 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (22 2 (:DEFINITION ASSOC-EQUAL))
 (20 12 (:REWRITE DEFAULT-CAR))
 (16 10 (:REWRITE DEFAULT-+-2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 2 (:REWRITE O-P-O-INFP-CAR))
 (7 7 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (7 7 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE M5::INT-LEMMA0))
 (2 2 (:REWRITE O-P-DEF-O-FINP-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE M5::INT-BACK))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(M5::KB-HACK2
 (102 2 (:DEFINITION M5::STACK-PRODUCT))
 (40 40 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (33 24 (:REWRITE DEFAULT-+-2))
 (29 24 (:REWRITE DEFAULT-+-1))
 (29 3 (:REWRITE ZP-OPEN))
 (28 7 (:REWRITE DEFAULT-*-2))
 (14 7 (:TYPE-PRESCRIPTION M5::INTEGERP-STACK-PRODUCT))
 (10 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 2 (:REWRITE <-0-+-NEGATIVE-1))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 7 (:REWRITE DEFAULT-*-1))
 (8 2 (:REWRITE M5::INT-LEMMA0))
 (7 7 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (7 7 (:TYPE-PRESCRIPTION M5::STACK-PRODUCT))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
 (4 2 (:REWRITE M5::INT-LEMMA6))
 (4 2 (:REWRITE FUNCTIONAL-SELF-INVERSION-OF-MINUS))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 1 (:REWRITE M5::INT-LEMMA3))
 (3 3 (:REWRITE M5::INT-BACK))
 (3 3 (:REWRITE FOLD-CONSTS-IN-*))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(M5::KB-HACK3
 (10 10 (:TYPE-PRESCRIPTION M5::INTP))
 (10 4 (:REWRITE M5::INT-LEMMA6))
 (6 2 (:REWRITE M5::INT-LEMMA0))
 (5 4 (:REWRITE DEFAULT-*-2))
 (5 4 (:REWRITE DEFAULT-*-1))
 )
(M5::FACT-INV-STEP
 (33521 17717 (:REWRITE DEFAULT-CAR))
 (18300 4367 (:REWRITE O-P-O-INFP-CAR))
 (10541 10529 (:REWRITE DEFAULT-CDR))
 (8958 8958 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8958 8958 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7416 18 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (7146 18 (:DEFINITION M5::INST-LENGTH))
 (5199 4367 (:REWRITE O-P-DEF-O-FINP-1))
 (4952 3173 (:REWRITE DEFAULT-+-2))
 (3479 3173 (:REWRITE DEFAULT-+-1))
 (2604 908 (:REWRITE DEFAULT-*-2))
 (2532 211 (:DEFINITION M5::BIND))
 (1491 908 (:REWRITE DEFAULT-*-1))
 (1439 1067 (:REWRITE DEFAULT-<-1))
 (1299 1067 (:REWRITE DEFAULT-<-2))
 (1135 821 (:REWRITE DEFAULT-UNARY-MINUS))
 (1134 42 (:REWRITE DISTRIBUTIVITY))
 (922 922 (:TYPE-PRESCRIPTION O-FINP))
 (882 882 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (708 260 (:REWRITE M5::INT-LEMMA0))
 (222 222 (:TYPE-PRESCRIPTION M5::STACK-PRODUCT))
 (188 34 (:REWRITE O-INFP->NEQ-0))
 (164 34 (:REWRITE <-0-+-NEGATIVE-1))
 (112 112 (:REWRITE M5::INT-BACK))
 (108 18 (:DEFINITION M5::OP-CODE))
 (90 30 (:REWRITE O-FIRST-EXPT-O-INFP))
 (60 30 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (32 32 (:REWRITE FOLD-CONSTS-IN-*))
 (4 4 (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
 )
(M5::RUN-TO-RETURN
 (6 6 (:TYPE-PRESCRIPTION M5::STEP))
 )
(M5::FACT-INV-RUN
 (1792 4 (:REWRITE M5::STEP-OPENER))
 (1788 4 (:DEFINITION M5::NEXT-INST))
 (1648 4 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (1588 4 (:DEFINITION M5::INST-LENGTH))
 (822 822 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (822 822 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (374 34 (:DEFINITION ASSOC-EQUAL))
 (374 22 (:DEFINITION M5::TOP-FRAME))
 (314 162 (:REWRITE DEFAULT-CAR))
 (252 14 (:REWRITE M5::FACT-INV-MAKE-STATE-OPENER))
 (224 50 (:REWRITE O-P-O-INFP-CAR))
 (120 12 (:DEFINITION M5::SDEPTH))
 (100 100 (:TYPE-PRESCRIPTION O-P))
 (76 76 (:REWRITE DEFAULT-CDR))
 (74 50 (:REWRITE O-P-DEF-O-FINP-1))
 (32 21 (:REWRITE DEFAULT-<-1))
 (32 4 (:REWRITE ZP-OPEN))
 (30 10 (:REWRITE M5::INT-LEMMA0))
 (28 16 (:REWRITE DEFAULT-+-2))
 (24 24 (:TYPE-PRESCRIPTION O-FINP))
 (24 4 (:DEFINITION M5::OP-CODE))
 (21 21 (:REWRITE DEFAULT-<-2))
 (21 21 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 20 (:TYPE-PRESCRIPTION M5::INTP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(M5::FACT-MAIN
 (480 1 (:DEFINITION M5::RUN-TO-RETURN))
 (448 1 (:REWRITE M5::STEP-OPENER))
 (447 1 (:DEFINITION M5::NEXT-INST))
 (424 212 (:REWRITE DEFAULT-CAR))
 (412 1 (:DEFINITION M5::INDEX-INTO-PROGRAM))
 (397 1 (:DEFINITION M5::INST-LENGTH))
 (344 75 (:REWRITE O-P-O-INFP-CAR))
 (258 258 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (258 258 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (132 132 (:REWRITE DEFAULT-CDR))
 (130 13 (:DEFINITION M5::SDEPTH))
 (119 75 (:REWRITE O-P-DEF-O-FINP-1))
 (63 2 (:REWRITE M5::FACT-INV-MAKE-STATE-OPENER))
 (50 50 (:TYPE-PRESCRIPTION O-FINP))
 (36 23 (:REWRITE DEFAULT-+-2))
 (32 4 (:DEFINITION M5::FACTORIAL))
 (23 23 (:REWRITE DEFAULT-+-1))
 (16 6 (:REWRITE DEFAULT-*-2))
 (14 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 5 (:REWRITE ZP-OPEN))
 (12 2 (:REWRITE O-INFP->NEQ-0))
 (10 4 (:REWRITE M5::INT-LEMMA6))
 (8 6 (:REWRITE DEFAULT-*-1))
 (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
 (6 1 (:DEFINITION M5::OP-CODE))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
 (3 1 (:REWRITE M5::INT-LEMMA0))
 )
