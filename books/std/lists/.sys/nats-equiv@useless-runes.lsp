(NATS-EQUIV
 (543 267 (:REWRITE DEFAULT-+-2))
 (340 267 (:REWRITE DEFAULT-+-1))
 (74 30 (:REWRITE DEFAULT-<-1))
 (72 30 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATS-EQUIV-REFLEXIVE
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 )
(NATS-EQUIV-SYMMETRIC
 (151 149 (:REWRITE DEFAULT-<-1))
 (149 149 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATS-EQUIV-TRANSITIVE)
(NATS-EQUIV-IS-AN-EQUIVALENCE
 (1957 1938 (:REWRITE DEFAULT-<-1))
 (1938 1938 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LIST-EQUIV-REFINES-NATS-EQUIV
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 )
(NATS-EQUIV-IMPLIES-NAT-EQUIV-CAR-1
 (48 46 (:REWRITE DEFAULT-<-1))
 (46 46 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-CDR-1
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-CONS-2
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(NATS-EQUIV-OF-CONS
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(MY-IND)
(NATS-EQUIV-IMPLIES-NAT-EQUIV-NTH-2
 (567 159 (:REWRITE ZP-OPEN))
 (436 436 (:REWRITE DEFAULT-+-2))
 (436 436 (:REWRITE DEFAULT-+-1))
 (408 136 (:REWRITE FOLD-CONSTS-IN-+))
 (309 300 (:REWRITE DEFAULT-<-1))
 (300 300 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-UPDATE-NTH-3
 (126 42 (:REWRITE ZP-OPEN))
 (113 111 (:REWRITE DEFAULT-<-1))
 (111 111 (:REWRITE DEFAULT-<-2))
 (86 86 (:REWRITE DEFAULT-+-2))
 (86 86 (:REWRITE DEFAULT-+-1))
 (84 28 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NAT-EQUIV-IMPLIES-NATS-EQUIV-UPDATE-NTH-2
 (335 200 (:REWRITE DEFAULT-CDR))
 (279 144 (:REWRITE DEFAULT-CAR))
 (132 130 (:REWRITE DEFAULT-<-1))
 (130 130 (:REWRITE DEFAULT-<-2))
 (118 34 (:REWRITE ZP-OPEN))
 (110 110 (:REWRITE DEFAULT-+-2))
 (110 110 (:REWRITE DEFAULT-+-1))
 (84 28 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-APPEND-2
 (92 46 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (62 32 (:REWRITE DEFAULT-CAR))
 (60 30 (:REWRITE DEFAULT-CDR))
 (46 46 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (46 46 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (27 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (7 7 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-REVAPPEND-2
 (63 33 (:REWRITE DEFAULT-CAR))
 (61 31 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-TAKE-2
 (897 68 (:REWRITE TAKE-OF-LEN-FREE))
 (496 92 (:DEFINITION LEN))
 (206 105 (:REWRITE DEFAULT-+-2))
 (173 173 (:REWRITE DEFAULT-<-2))
 (173 173 (:REWRITE DEFAULT-<-1))
 (105 105 (:REWRITE DEFAULT-+-1))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-NTHCDR-2
 (134 95 (:REWRITE DEFAULT-CAR))
 (83 83 (:REWRITE DEFAULT-<-2))
 (83 83 (:REWRITE DEFAULT-<-1))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (11 11 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 )
(NATS-EQUIV-IMPLIES-NATS-EQUIV-MAKE-LIST-AC-3
 (37 27 (:REWRITE DEFAULT-CDR))
 (37 27 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(NAT-EQUIV-IMPLIES-NATS-EQUIV-REPLICATE-2
 (122 71 (:REWRITE DEFAULT-CDR))
 (122 71 (:REWRITE DEFAULT-CAR))
 (100 98 (:REWRITE DEFAULT-<-1))
 (98 98 (:REWRITE DEFAULT-<-2))
 (46 34 (:REWRITE ZP-OPEN))
 (44 44 (:REWRITE DEFAULT-+-2))
 (44 44 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
