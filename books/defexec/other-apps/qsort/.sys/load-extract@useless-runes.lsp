(EXTRACT-N
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(EXTRACT-N-UPDATE-REDUCTION
 (39 3 (:REWRITE NTH-UPDATE-NTH-SAME-OBJSI))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 16 (:META CANCEL_PLUS-LESSP-CORRECT))
 (8 8 (:REWRITE NATP-RW))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(OBJSI-LOAD-REDUCTION
 (13 1 (:REWRITE NTH-UPDATE-NTH-SAME-OBJSI))
 (8 8 (:REWRITE NATP-RW))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(LOAD-EXTRACT-N-REDUCTION
 (53 6 (:REWRITE FIRST-N-LENGTH-IS-X))
 (36 7 (:DEFINITION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE NATP-RW))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE APPEND-FIRST-REDUCTION-LEN))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(FIRST-N-EXTRACT-N-REDUCTION
 (85 7 (:REWRITE FIRST-N-LENGTH-IS-X))
 (42 42 (:TYPE-PRESCRIPTION LEN))
 (38 38 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (11 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE NATP-RW))
 (10 10 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (10 10 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 3 (:REWRITE DEFAULT-CDR))
 (10 3 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE APPEND-FIRST-REDUCTION-LEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 )
(EXTRACT-QS-N-REDUCTION
 (60 46 (:REWRITE DEFAULT-+-2))
 (46 46 (:REWRITE DEFAULT-+-1))
 (13 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE <-0-+-NEGATIVE-2))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE NATP-RW))
 (3 2 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (2 2 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(ARITH-001
 (30 30 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (3 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(LOAD-ALLOC-EXTRACT-QS-SAME
 (55 55 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (9 6 (:REWRITE DEFAULT-+-2))
 (8 1 (:REWRITE FIRST-N-LENGTH-IS-X))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 1 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE APPEND-FIRST-REDUCTION-LEN))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(ARITH-002)
(FIRST-N-EXTRACT-QS-REDUCTION
 (27 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (15 1 (:REWRITE FIRST-N-LENGTH-IS-X))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE APPEND-FIRST-REDUCTION-LEN))
 )
(LAST-N-EXTRACT-QS-REDUCTION
 (8 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 1 (:DEFINITION BINARY-APPEND))
 (4 4 (:REWRITE NATP-RW))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
