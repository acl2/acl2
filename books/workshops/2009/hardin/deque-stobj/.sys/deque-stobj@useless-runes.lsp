(TAIL-HEAD-RELATION)
(SUB1)
(ADD1)
(SIZE-OF)
(IS-EMPTY)
(GET-ARR-LIST-FIRST-N
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 3 (:REWRITE DEFAULT-+-2))
 (4 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:DEFINITION NTH))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(PD)
(GET-FIRST)
(GET-LAST
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ARRP))
 )
(IS-FULL)
(IS-FULL-FRONT)
(IS-FULL-BACK)
(INDEX-OF--FROM-FRONT
 (31 31 (:REWRITE DEFAULT-CDR))
 (23 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE DEFAULT-<-2))
 (20 15 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION LEN))
 (16 15 (:REWRITE DEFAULT-+-1))
 (7 4 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 2 (:DEFINITION ARRP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(IOFF-NAT--THM
 (233 233 (:REWRITE DEFAULT-CDR))
 (164 135 (:REWRITE DEFAULT-+-2))
 (135 135 (:REWRITE DEFAULT-+-1))
 (115 115 (:REWRITE DEFAULT-<-2))
 (115 115 (:REWRITE DEFAULT-<-1))
 (59 59 (:REWRITE DEFAULT-CAR))
 (45 45 (:REWRITE DEFAULT-UNARY-MINUS))
 (45 18 (:REWRITE ZP-OPEN))
 (22 11 (:DEFINITION TRUE-LISTP))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE NTH-0-CONS))
 )
(INDEX-OF--FROM-BACK
 (31 31 (:REWRITE DEFAULT-CDR))
 (27 22 (:REWRITE DEFAULT-+-2))
 (23 22 (:REWRITE DEFAULT-<-1))
 (23 22 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE DEFAULT-<-2))
 (20 4 (:DEFINITION LEN))
 (8 6 (:REWRITE FOLD-CONSTS-IN-+))
 (7 4 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 2 (:DEFINITION ARRP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(IOFB-NAT--THM
 (197 168 (:REWRITE DEFAULT-+-2))
 (185 185 (:REWRITE DEFAULT-CDR))
 (168 168 (:REWRITE DEFAULT-+-1))
 (99 99 (:REWRITE DEFAULT-<-2))
 (99 99 (:REWRITE DEFAULT-<-1))
 (67 49 (:REWRITE FOLD-CONSTS-IN-+))
 (53 53 (:REWRITE DEFAULT-CAR))
 (45 18 (:REWRITE ZP-OPEN))
 (29 29 (:REWRITE DEFAULT-UNARY-MINUS))
 (22 11 (:DEFINITION TRUE-LISTP))
 (2 2 (:REWRITE NTH-0-CONS))
 )
(CONTAINS
 (14 14 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ARRP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(SHIFT-UP-TO
 (28 28 (:REWRITE DEFAULT-CDR))
 (23 18 (:REWRITE DEFAULT-+-2))
 (20 4 (:DEFINITION LEN))
 (19 18 (:REWRITE DEFAULT-<-2))
 (19 18 (:REWRITE DEFAULT-+-1))
 (18 18 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 2 (:DEFINITION ARRP))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(SHIFT-DOWN-TO
 (19 16 (:REWRITE DEFAULT-+-2))
 (17 16 (:REWRITE DEFAULT-+-1))
 (15 15 (:REWRITE DEFAULT-CDR))
 (12 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (10 2 (:DEFINITION LEN))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ARRP))
 )
(ADD-FIRST
 (84 84 (:REWRITE DEFAULT-CDR))
 (40 32 (:REWRITE DEFAULT-+-2))
 (40 8 (:DEFINITION LEN))
 (34 34 (:REWRITE DEFAULT-<-2))
 (34 34 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 4 (:DEFINITION UPDATE-NTH))
 (8 4 (:DEFINITION TRUE-LISTP))
 (8 4 (:DEFINITION ARRP))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ADD-LAST
 (64 64 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION UPDATE-NTH))
 (30 6 (:DEFINITION LEN))
 (26 20 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE ZP-OPEN))
 (6 3 (:DEFINITION TRUE-LISTP))
 (6 3 (:DEFINITION ARRP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(REMOVE-FIRST
 (20 20 (:REWRITE DEFAULT-CDR))
 (12 2 (:DEFINITION UPDATE-NTH))
 (10 2 (:DEFINITION LEN))
 (9 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE ZP-OPEN))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ARRP))
 (1 1 (:TYPE-PRESCRIPTION REMOVE-FIRST))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(REMOVE-LAST
 (31 31 (:REWRITE DEFAULT-CDR))
 (20 4 (:DEFINITION LEN))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 2 (:DEFINITION ARRP))
 (3 1 (:DEFINITION UPDATE-NTH))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION REMOVE-LAST))
 )
(REMOVE-FRONT)
(REMOVE-BACK)
(REMOVE-FIRST-OCCURRENCE
 (84 84 (:REWRITE DEFAULT-CDR))
 (37 25 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 4 (:DEFINITION TRUE-LISTP))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(REMOVE-LAST-OCCURRENCE
 (64 64 (:REWRITE DEFAULT-CDR))
 (29 17 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 4 (:DEFINITION TRUE-LISTP))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ADD-ELEMENT)
(REMOVE-ELEMENT)
(CLEAR-HELPER
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 2 (:DEFINITION LEN))
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:DEFINITION TRUE-LISTP))
 (2 1 (:DEFINITION ARRP))
 )
(CLEAR)
