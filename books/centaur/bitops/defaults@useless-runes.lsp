(BITOPS::LOGBITP-DEFAULT-1
     (8 8 (:TYPE-PRESCRIPTION BITP))
     (6 2 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (4 2
        (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
     (4 2
        (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
     (4 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
     (3 1 (:REWRITE NATP-WHEN-GTE-0))
     (2 2 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
     (1 1
        (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (1 1
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (1 1 (:REWRITE NATP-WHEN-INTEGERP))
     (1 1 (:REWRITE DEFAULT-<-2))
     (1 1 (:REWRITE DEFAULT-<-1)))
(BITOPS::LOGBITP-DEFAULT-2 (7 1 (:REWRITE NFIX-WHEN-NATP))
                           (5 5 (:TYPE-PRESCRIPTION NATP))
                           (5 1 (:REWRITE NFIX-WHEN-NOT-NATP))
                           (4 2 (:REWRITE NATP-WHEN-GTE-0))
                           (3 2 (:REWRITE DEFAULT-<-1))
                           (2 2 (:REWRITE NATP-WHEN-INTEGERP))
                           (2 2 (:REWRITE DEFAULT-<-2))
                           (2 1 (:REWRITE BITOPS::LOGBITP-DEFAULT-1))
                           (1 1
                              (:REWRITE INEQUALITY-WITH-NFIX-HYP-2)))
(BITOPS::LOGNOT-DEFAULT (30 28
                            (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
                        (30 28
                            (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
                        (2 2 (:TYPE-PRESCRIPTION NEGP))
                        (2 2 (:TYPE-PRESCRIPTION NATP)))
(BITOPS::LOGAND-DEFAULT-1
     (23 23
         (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
     (12 1
         (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
     (6 1 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (5 3 (:REWRITE DEFAULT-<-1))
     (4 2
        (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
     (4 1
        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
     (4 1
        (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
     (3 3 (:REWRITE DEFAULT-<-2))
     (3 1 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (2 2
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (2 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
     (1 1 (:TYPE-PRESCRIPTION NEGP))
     (1 1 (:REWRITE NEGP-WHEN-INTEGERP))
     (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (1 1 (:REWRITE IFIX-WHEN-INTEGERP)))
(BITOPS::LOGAND-DEFAULT-2 (88 4 (:DEFINITION LOGAND**))
                          (48 12
                              (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                          (40 1
                              (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                          (20 8 (:REWRITE SIMPLIFY-BIT-FUNCTIONS))
                          (19 7 (:REWRITE BITOPS::LOGNOT-DEFAULT))
                          (16 16 (:TYPE-PRESCRIPTION BITP))
                          (12 4 (:REWRITE BITOPS::LOGCDR-OF-BIT))
                          (12 4 (:REWRITE BITOPS::LOGCAR-OF-BIT))
                          (12 2 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
                          (12 1
                              (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                          (12 1 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                          (8 8 (:REWRITE BITOPS::LOGAND-DEFAULT-1))
                          (8 4
                             (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                          (6 4 (:REWRITE DEFAULT-<-1))
                          (6 2 (:REWRITE NEGP-WHEN-LESS-THAN-0))
                          (5 5
                             (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                          (4 4 (:TYPE-PRESCRIPTION NATP))
                          (4 4 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
                          (4 4
                             (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                          (4 4
                             (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
                          (4 4 (:REWRITE DEFAULT-<-2))
                          (4 1
                             (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
                          (2 2 (:TYPE-PRESCRIPTION NEGP))
                          (2 2
                             (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-1))
                          (2 2
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (2 2 (:REWRITE NEGP-WHEN-INTEGERP))
                          (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                          (2 2 (:REWRITE IFIX-WHEN-INTEGERP)))
(BITOPS::LOGIOR-DEFAULT-1 (32 32
                              (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE))
                          (26 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
                          (24 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
                          (24 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
                          (12 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
                          (11 1 (:REWRITE BFIX-WHEN-NOT-1))
                          (10 7 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                          (6 6 (:TYPE-PRESCRIPTION BITP))
                          (6 2 (:REWRITE BITOPS::LOGCAR-OF-BIT))
                          (5 1 (:LINEAR BITOPS::LOGCAR-BOUND))
                          (4 4 (:TYPE-PRESCRIPTION NEGP))
                          (4 4 (:REWRITE NEGP-WHEN-INTEGERP))
                          (4 4 (:REWRITE DEFAULT-<-2))
                          (4 4 (:REWRITE DEFAULT-<-1))
                          (4 2
                             (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                          (4 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
                          (3 1 (:REWRITE BITOPS::LOGCDR-OF-BIT))
                          (2 2 (:TYPE-PRESCRIPTION NATP))
                          (2 2 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
                          (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
                          (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
                          (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL)))
(BITOPS::LOGIOR-DEFAULT-2
     (50 50
         (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE))
     (44 4 (:REWRITE BFIX-WHEN-NOT-1))
     (24 24 (:TYPE-PRESCRIPTION BITP))
     (24 8 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (24 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (24 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
     (24 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
     (20 4 (:LINEAR BITOPS::LOGCAR-BOUND))
     (14 8 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (12 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (12 4 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (8 8 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (8 4
        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BITP))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (8 4 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (4 4 (:TYPE-PRESCRIPTION NEGP))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE NEGP-WHEN-INTEGERP))
     (4 4 (:REWRITE BITOPS::LOGIOR-DEFAULT-1))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
     (1 1
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV)))
(BITOPS::LOGCAR-DEFAULT)
(BITOPS::LOGCDR-DEFAULT (21 19
                            (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
                        (4 4 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
                        (2 2 (:TYPE-PRESCRIPTION NATP)))
(BITOPS::INTEGER-LENGTH-DEFAULT)
(BITOPS::ASH-DEFAULT-1)
(BITOPS::ASH-DEFAULT-2 (28 28
                           (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE))
                       (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                       (2 2 (:REWRITE IFIX-WHEN-INTEGERP))
                       (1 1 (:REWRITE BITOPS::ASH-DEFAULT-1)))
(BITOPS::LOGXOR-DEFAULT-1
     (32 32
         (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-2))
     (32 32
         (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-1))
     (26 2
         (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-2))
     (24 4 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (24 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (12 4 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (12 1 (:REWRITE BFIX-WHEN-NOT-1))
     (10 7 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (6 6 (:TYPE-PRESCRIPTION BITP))
     (6 2 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (6 1 (:LINEAR BITOPS::LOGCAR-BOUND))
     (4 4 (:TYPE-PRESCRIPTION NEGP))
     (4 4 (:REWRITE NEGP-WHEN-INTEGERP))
     (4 4 (:REWRITE DEFAULT-<-2))
     (4 4 (:REWRITE DEFAULT-<-1))
     (4 2
        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (4 2
        (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (4 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (3 1 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (2 2 (:TYPE-PRESCRIPTION NATP))
     (2 2 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (2 2 (:REWRITE BITOPS::LOGCAR-DEFAULT))
     (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
     (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (1 1 (:REWRITE BITOPS::LOGCDR-DEFAULT)))
(BITOPS::LOGXOR-DEFAULT-2
     (50 50
         (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-2))
     (50 50
         (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-1))
     (48 4 (:REWRITE BFIX-WHEN-NOT-1))
     (44 2
         (:REWRITE BITOPS::COMMUTATIVITY-OF-B-XOR))
     (36 6 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (24 24 (:TYPE-PRESCRIPTION BITP))
     (24 8 (:REWRITE BITOPS::LOGCAR-OF-BIT))
     (24 4 (:LINEAR BITOPS::LOGCAR-BOUND))
     (24 2
         (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-2))
     (24 2
         (:LINEAR BITOPS::LOGXOR->=-0-LINEAR-1))
     (24 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-1))
     (18 6 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (16 10 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (12 4 (:REWRITE BITOPS::LOGCDR-OF-BIT))
     (8 8 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
     (8 8 (:REWRITE BITOPS::LOGCAR-DEFAULT))
     (8 4
        (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BITP))
     (8 4 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
     (8 4 (:REWRITE BFIX-WHEN-BIT->BOOL))
     (6 6 (:TYPE-PRESCRIPTION NEGP))
     (6 6 (:REWRITE NEGP-WHEN-INTEGERP))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (4 4 (:TYPE-PRESCRIPTION NATP))
     (4 4 (:REWRITE BITOPS::LOGXOR-DEFAULT-1))
     (4 4 (:REWRITE BITOPS::LOGCDR-DEFAULT))
     (4 2 (:LINEAR BITOPS::LOGXOR-<-0-LINEAR-2))
     (1 1
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV)))
