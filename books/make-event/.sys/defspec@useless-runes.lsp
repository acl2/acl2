(CONSTRAINT)
(CREATE-ALIST-FROM-FUNC-LIST)
(F
 (1 1 (:TYPE-PRESCRIPTION F))
 )
(FOO-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION F))
 )
(G
 (1 1 (:TYPE-PRESCRIPTION G))
 )
(G-IS-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION G))
 )
(F
 (1 1 (:TYPE-PRESCRIPTION F))
 )
(G)
(G-IS-ARBITRARY)
(F
 (1 1 (:TYPE-PRESCRIPTION F))
 )
(F-IS-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION F))
 )
(G)
(G-IS-IDENTITY)
(F
 (1 1 (:TYPE-PRESCRIPTION F))
 )
(F-IS-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION F))
 )
(G
 (1 1 (:TYPE-PRESCRIPTION G))
 )
(G-IS-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION G))
 )
(F
 (1 1 (:TYPE-PRESCRIPTION F))
 )
(F-IS-IDENTITY
 (3 3 (:TYPE-PRESCRIPTION F))
 )
(BIJ2)
(INV1)
(INV2)
(DOM2)
(RAN2)
(RAN2-BIJ2)
(DOM2-INV1)
(DOM2-INV2)
(BIJ2-IS-INJECTIVE)
(BIJ2-IS-SURJECTIVE
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(LEMMA1
 (88 4 (:DEFINITION SUM))
 (40 24 (:REWRITE DEFAULT-+-2))
 (32 4 (:REWRITE ASSOCIATIVITY-OF-+))
 (24 24 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 4 (:DEFINITION NFIX))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(LEMMA2
 (88 4 (:DEFINITION SUM))
 (40 24 (:REWRITE DEFAULT-+-2))
 (32 4 (:REWRITE ASSOCIATIVITY-OF-+))
 (24 24 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE ZP-OPEN))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 4 (:DEFINITION NFIX))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(LEMMA3
 (488 29 (:DEFINITION SUM))
 (294 136 (:REWRITE DEFAULT-+-2))
 (252 14 (:DEFINITION SUM-INVERSE))
 (179 136 (:REWRITE DEFAULT-+-1))
 (104 13 (:REWRITE ZP-OPEN))
 (88 61 (:REWRITE DEFAULT-<-2))
 (87 29 (:DEFINITION NFIX))
 (66 61 (:REWRITE DEFAULT-<-1))
 (52 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (31 31 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(CANTOR-PAIRING-IS-BIJECTION
 (13533 869 (:DEFINITION SUM))
 (7529 3701 (:REWRITE DEFAULT-+-2))
 (7106 391 (:DEFINITION SUM-INVERSE))
 (4685 3701 (:REWRITE DEFAULT-+-1))
 (2796 444 (:REWRITE ZP-OPEN))
 (2643 1946 (:REWRITE DEFAULT-<-2))
 (2607 869 (:DEFINITION NFIX))
 (2038 1946 (:REWRITE DEFAULT-<-1))
 (1326 527 (:REWRITE DEFAULT-UNARY-MINUS))
 (735 735 (:REWRITE FOLD-CONSTS-IN-+))
 (102 102 (:REWRITE DEFAULT-CAR))
 (94 94 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (51 51 (:REWRITE DEFAULT-CDR))
 )
