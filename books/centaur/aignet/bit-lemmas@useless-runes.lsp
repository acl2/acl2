(AIGNET::B-XOR-LEMMA1 (54 54 (:TYPE-PRESCRIPTION BITP))
                      (52 52
                          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                      (52 26 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                      (52 26 (:REWRITE BFIX-WHEN-BIT->BOOL))
                      (46 20 (:REWRITE BFIX-WHEN-NOT-BITP))
                      (46 4 (:REWRITE BITOPS::B-NOT-EQUAL-1))
                      (27 9 (:REWRITE BFIX-BITP))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV)))
(AIGNET::B-XOR-LEMMA2 (138 20 (:REWRITE BFIX-WHEN-NOT-1))
                      (66 66 (:TYPE-PRESCRIPTION BITP))
                      (48 20 (:REWRITE BFIX-WHEN-NOT-BITP))
                      (42 2 (:REWRITE BITOPS::BXOR-TO-BNOT))
                      (40 40
                          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                      (40 20 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                      (40 20 (:REWRITE BFIX-WHEN-BIT->BOOL))
                      (33 11 (:REWRITE BFIX-BITP))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
                      (4 2 (:REWRITE BITOPS::B-NOT-EQUAL-1)))
(AIGNET::B-XOR-LEMMA3 (54 54 (:TYPE-PRESCRIPTION BITP))
                      (46 4 (:LINEAR BITOPS::BFIX-BOUND))
                      (42 42
                          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                      (42 21 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                      (42 21 (:REWRITE BFIX-WHEN-BIT->BOOL))
                      (37 15 (:REWRITE BFIX-WHEN-NOT-BITP))
                      (27 9 (:REWRITE BFIX-BITP))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
                      (4 2 (:LINEAR BITOPS::B-NOT-BOUND)))
(AIGNET::B-XOR-LEMMA4 (90 90 (:TYPE-PRESCRIPTION BITP))
                      (66 24 (:REWRITE BFIX-WHEN-NOT-1))
                      (60 24 (:REWRITE BFIX-WHEN-NOT-BITP))
                      (48 48
                          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                      (48 24 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                      (48 24 (:REWRITE BFIX-WHEN-BIT->BOOL))
                      (45 15 (:REWRITE BFIX-BITP))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                      (8 8
                         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV)))
(AIGNET::ASSOCIATIVITY-OF-B-XOR
     (96 96
         (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (96 48 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (96 48 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (72 72 (:TYPE-PRESCRIPTION BITP))
     (56 24 (:REWRITE BFIX-WHEN-NOT-BITP))
     (36 12 (:REWRITE BFIX-BITP))
     (16 16
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (16 16
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (16 16
         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV)))
(AIGNET::COMMUTATIVITY-2-OF-B-XOR
     (96 96
         (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (96 48 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (96 48 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (72 72 (:TYPE-PRESCRIPTION BITP))
     (56 24 (:REWRITE BFIX-WHEN-NOT-BITP))
     (36 12 (:REWRITE BFIX-BITP))
     (16 16
         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (16 16
         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (16 16
         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV)))
(AIGNET::B-XOR-SAME-2 (54 54 (:TYPE-PRESCRIPTION BITP))
                      (46 4 (:LINEAR BITOPS::BFIX-BOUND))
                      (42 42
                          (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                      (42 21 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                      (42 21 (:REWRITE BFIX-WHEN-BIT->BOOL))
                      (37 15 (:REWRITE BFIX-WHEN-NOT-BITP))
                      (27 9 (:REWRITE BFIX-BITP))
                      (8 4 (:LINEAR BITOPS::B-NOT-BOUND))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                      (6 6
                         (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV)))
