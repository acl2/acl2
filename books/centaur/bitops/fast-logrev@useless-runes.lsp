(FAST-LOGREV-U8$INLINE)
(BITOPS::CROCK (13 13 (:REWRITE DEFAULT-<-2))
               (13 13 (:REWRITE DEFAULT-<-1))
               (9 3
                  (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-*))
               (4 4 (:REWRITE DEFAULT-*-2))
               (4 4 (:REWRITE DEFAULT-*-1)))
(BITOPS::TEST (6 6
                 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)))
(BITOPS::CONSEQUENCE (3574 18 (:DEFINITION UNSIGNED-BYTE-P))
                     (3556 18 (:DEFINITION INTEGER-RANGE-P))
                     (1961 9 (:REWRITE LOGHEAD-IDENTITY))
                     (1943 9 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
                     (1832 9 (:REWRITE LOGTAIL-IDENTITY))
                     (1530 918
                           (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                     (1120 18
                           (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
                     (1120 18
                           (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
                     (953 171
                          (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE))
                     (588 588
                          (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-1))
                     (564 18 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
                     (420 36
                          (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                     (388 36
                          (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                     (360 117 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                     (360 117 (:REWRITE IFIX-WHEN-INTEGERP))
                     (348 36
                          (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
                     (300 36
                          (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                     (296 162
                          (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                     (296 162
                          (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
                     (268 268
                          (:TYPE-PRESCRIPTION BITMASKP$INLINE))
                     (249 39 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
                     (246 60 (:REWRITE DEFAULT-<-1))
                     (114 39 (:REWRITE ZIP-OPEN))
                     (102 39 (:REWRITE DEFAULT-*-2))
                     (72 36 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                     (60 60 (:TYPE-PRESCRIPTION ZIP))
                     (60 60 (:REWRITE DEFAULT-<-2))
                     (55 55
                         (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                     (39 39 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
                     (39 39 (:REWRITE DEFAULT-*-1))
                     (36 18
                         (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-*))
                     (29 29 (:REWRITE DEFAULT-+-2))
                     (29 29 (:REWRITE DEFAULT-+-1))
                     (27 27
                         (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                     (21 21 (:REWRITE EQUAL-CONSTANT-+))
                     (18 18
                         (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                     (12 4 (:REWRITE NATP-WHEN-GTE-0))
                     (4 4 (:REWRITE NATP-WHEN-INTEGERP))
                     (4 4 (:REWRITE NATP-RW)))
(BITOPS::CROCK2 (145 1 (:REWRITE LOGHEAD-IDENTITY))
                (143 1 (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL))
                (136 1 (:REWRITE LOGTAIL-IDENTITY))
                (102 102
                     (:TYPE-PRESCRIPTION BITOPS::LOGAND-NATP-TYPE-2))
                (88 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
                (88 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
                (57 19
                    (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE))
                (36 36 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
                (36 18
                    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                (36 18
                    (:REWRITE BITOPS::LOGAND-WITH-BITMASK))
                (36 4
                    (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                (36 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
                (28 4
                    (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                (28 4
                    (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
                (28 4
                    (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                (24 13 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                (24 13 (:REWRITE IFIX-WHEN-INTEGERP))
                (19 9 (:REWRITE DEFAULT-<-1))
                (16 4 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
                (9 9 (:REWRITE DEFAULT-<-2))
                (8 8 (:TYPE-PRESCRIPTION ZIP))
                (8 4 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                (6 6
                   (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                (6 3 (:REWRITE DEFAULT-*-2))
                (4 4 (:REWRITE ZIP-OPEN))
                (4 4 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
                (4 2
                   (:REWRITE BITOPS::BASIC-UNSIGNED-BYTE-P-OF-*))
                (3 3
                   (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                (3 3
                   (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                (3 3 (:REWRITE DEFAULT-*-1)))
(FAST-LOGREV-U8$INLINE (143 3 (:REWRITE LOGHEAD-IDENTITY))
                       (134 3 (:REWRITE LOGTAIL-IDENTITY))
                       (84 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
                       (84 2 (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
                       (51 30
                           (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                       (50 50
                           (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                       (37 27 (:REWRITE DEFAULT-<-1))
                       (36 2 (:LINEAR BITOPS::LOGIOR->=-0-LINEAR))
                       (32 23 (:REWRITE DEFAULT-*-2))
                       (29 23 (:REWRITE DEFAULT-*-1))
                       (28 14 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
                       (28 4
                           (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 2))
                       (28 4
                           (:LINEAR BITOPS::UPPER-BOUND-OF-LOGAND . 1))
                       (28 4
                           (:LINEAR BITOPS::LOGAND->=-0-LINEAR-2))
                       (28 4
                           (:LINEAR BITOPS::LOGAND->=-0-LINEAR-1))
                       (27 27 (:REWRITE DEFAULT-<-2))
                       (13 13
                           (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                       (8 4 (:LINEAR BITOPS::LOGAND-<-0-LINEAR))
                       (3 3
                          (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV)))
(FAST-LOGREV-U16)
(BITOPS::CROCK (2550 234 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
               (2000 19
                     (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
               (1933 235 (:REWRITE ZIP-OPEN))
               (1164 582
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
               (965 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
               (902 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
               (898 19
                    (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
               (670 19 (:REWRITE BITOPS::ASH-<-0))
               (582 582 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
               (522 15 (:REWRITE ASH-0))
               (383 383 (:TYPE-PRESCRIPTION ZIP))
               (242 99 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
               (239 1
                    (:LINEAR BITOPS::LOGBITP-MISMATCH-UPPER-BOUND))
               (237 1
                    (:REWRITE BITOPS::LOGBITP-MISMATCH-UNDER-IFF))
               (234 234 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
               (164 113 (:REWRITE DEFAULT-<-1))
               (156 28 (:REWRITE BITOPS::LOGBITP-WHEN-BIT))
               (142 142
                    (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
               (140 26 (:REWRITE NFIX-WHEN-NOT-NATP))
               (135 15 (:REWRITE LOGTAIL-IDENTITY))
               (126 6 (:REWRITE BFIX-WHEN-NOT-1))
               (116 113 (:REWRITE DEFAULT-<-2))
               (90 15 (:DEFINITION UNSIGNED-BYTE-P))
               (88 88 (:TYPE-PRESCRIPTION BITP))
               (75 15 (:DEFINITION INTEGER-RANGE-P))
               (72 72
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
               (69 13 (:REWRITE NATP-WHEN-INTEGERP))
               (66 22
                   (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
               (64 64
                   (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
               (48 16
                   (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
               (44 44 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
               (37 13 (:REWRITE NATP-WHEN-GTE-0))
               (36 34 (:REWRITE DEFAULT-+-2))
               (36 34 (:REWRITE DEFAULT-+-1))
               (36 12 (:REWRITE <-+-NEGATIVE-0-2))
               (30 15 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-MASK))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-CONST))
               (28 28
                   (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
               (15 15
                   (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-OUT-OF-RANGE))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-IN-RANGE))
               (12 12
                   (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BITP))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
               (12 6 (:REWRITE BFIX-WHEN-BIT->BOOL))
               (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
               (8 8 (:TYPE-PRESCRIPTION NFIX))
               (4 4
                  (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
               (2 2
                  (:REWRITE BITOPS::B-IOR-EQUAL-1-IN-CONCL))
               (1 1
                  (:TYPE-PRESCRIPTION LOGBITP-MISMATCH)))
(FAST-LOGREV-U16 (45 7 (:REWRITE ZIP-OPEN))
                 (42 10 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
                 (38 5 (:REWRITE ASH-0))
                 (18 18
                     (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                 (16 16
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
                 (11 11 (:TYPE-PRESCRIPTION ZIP))
                 (10 10 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
                 (9 3 (:REWRITE LOGTAIL-IDENTITY))
                 (8 8
                    (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                 (8 8 (:REWRITE DEFAULT-<-2))
                 (8 8 (:REWRITE DEFAULT-<-1))
                 (8 2 (:REWRITE LOGHEAD-IDENTITY))
                 (8 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
                 (7 7
                    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                 (7 4
                    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                 (7 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
                 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(FAST-LOGREV-U32)
(BITOPS::CROCK (2550 234 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
               (2000 19
                     (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
               (1933 235 (:REWRITE ZIP-OPEN))
               (1164 582
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
               (965 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
               (902 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
               (898 19
                    (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
               (670 19 (:REWRITE BITOPS::ASH-<-0))
               (582 582 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
               (522 15 (:REWRITE ASH-0))
               (383 383 (:TYPE-PRESCRIPTION ZIP))
               (242 99 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
               (239 1
                    (:LINEAR BITOPS::LOGBITP-MISMATCH-UPPER-BOUND))
               (237 1
                    (:REWRITE BITOPS::LOGBITP-MISMATCH-UNDER-IFF))
               (234 234 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
               (164 113 (:REWRITE DEFAULT-<-1))
               (156 28 (:REWRITE BITOPS::LOGBITP-WHEN-BIT))
               (142 142
                    (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
               (140 26 (:REWRITE NFIX-WHEN-NOT-NATP))
               (135 15 (:REWRITE LOGTAIL-IDENTITY))
               (126 6 (:REWRITE BFIX-WHEN-NOT-1))
               (116 113 (:REWRITE DEFAULT-<-2))
               (90 15 (:DEFINITION UNSIGNED-BYTE-P))
               (88 88 (:TYPE-PRESCRIPTION BITP))
               (75 15 (:DEFINITION INTEGER-RANGE-P))
               (72 72
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
               (69 13 (:REWRITE NATP-WHEN-INTEGERP))
               (66 22
                   (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
               (64 64
                   (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
               (48 16
                   (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
               (44 44 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
               (37 13 (:REWRITE NATP-WHEN-GTE-0))
               (36 34 (:REWRITE DEFAULT-+-2))
               (36 34 (:REWRITE DEFAULT-+-1))
               (36 12 (:REWRITE <-+-NEGATIVE-0-2))
               (30 15 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-MASK))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-CONST))
               (28 28
                   (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
               (15 15
                   (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-OUT-OF-RANGE))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-IN-RANGE))
               (12 12
                   (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BITP))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
               (12 6 (:REWRITE BFIX-WHEN-BIT->BOOL))
               (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
               (8 8 (:TYPE-PRESCRIPTION NFIX))
               (4 4
                  (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
               (2 2
                  (:REWRITE BITOPS::B-IOR-EQUAL-1-IN-CONCL))
               (1 1
                  (:TYPE-PRESCRIPTION LOGBITP-MISMATCH)))
(FAST-LOGREV-U32 (45 7 (:REWRITE ZIP-OPEN))
                 (42 10 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
                 (38 5 (:REWRITE ASH-0))
                 (18 18
                     (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                 (16 16
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
                 (11 11 (:TYPE-PRESCRIPTION ZIP))
                 (10 10 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
                 (9 3 (:REWRITE LOGTAIL-IDENTITY))
                 (8 8
                    (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                 (8 8 (:REWRITE DEFAULT-<-2))
                 (8 8 (:REWRITE DEFAULT-<-1))
                 (8 2 (:REWRITE LOGHEAD-IDENTITY))
                 (8 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
                 (7 7
                    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                 (7 4
                    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                 (7 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
                 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
(FAST-LOGREV-U64)
(BITOPS::CROCK (2550 234 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
               (2000 19
                     (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2))
               (1933 235 (:REWRITE ZIP-OPEN))
               (1164 582
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
               (965 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
               (902 63
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
               (898 19
                    (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1))
               (670 19 (:REWRITE BITOPS::ASH-<-0))
               (582 582 (:TYPE-PRESCRIPTION LOGTAIL-TYPE))
               (522 15 (:REWRITE ASH-0))
               (383 383 (:TYPE-PRESCRIPTION ZIP))
               (242 99 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
               (239 1
                    (:LINEAR BITOPS::LOGBITP-MISMATCH-UPPER-BOUND))
               (237 1
                    (:REWRITE BITOPS::LOGBITP-MISMATCH-UNDER-IFF))
               (234 234 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
               (164 113 (:REWRITE DEFAULT-<-1))
               (156 28 (:REWRITE BITOPS::LOGBITP-WHEN-BIT))
               (142 142
                    (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
               (140 26 (:REWRITE NFIX-WHEN-NOT-NATP))
               (135 15 (:REWRITE LOGTAIL-IDENTITY))
               (126 6 (:REWRITE BFIX-WHEN-NOT-1))
               (116 113 (:REWRITE DEFAULT-<-2))
               (90 15 (:DEFINITION UNSIGNED-BYTE-P))
               (88 88 (:TYPE-PRESCRIPTION BITP))
               (75 15 (:DEFINITION INTEGER-RANGE-P))
               (72 72
                   (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
               (69 13 (:REWRITE NATP-WHEN-INTEGERP))
               (66 22
                   (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
               (64 64
                   (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
               (48 16
                   (:REWRITE BITOPS::LOGBITP-NONZERO-OF-BIT))
               (44 44 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
               (37 13 (:REWRITE NATP-WHEN-GTE-0))
               (36 34 (:REWRITE DEFAULT-+-2))
               (36 34 (:REWRITE DEFAULT-+-1))
               (36 12 (:REWRITE <-+-NEGATIVE-0-2))
               (30 15 (:REWRITE RIGHT-SHIFT-TO-LOGTAIL))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-NEGATIVE-CONST))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-MASK))
               (28 28
                   (:REWRITE BITOPS::LOGBITP-OF-CONST-SPLIT))
               (28 28 (:REWRITE BITOPS::LOGBITP-OF-CONST))
               (28 28
                   (:META BITOPS::OPEN-LOGBITP-OF-CONST-LITE-META))
               (15 15
                   (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-OUT-OF-RANGE))
               (14 2
                   (:REWRITE BITOPS::LOGBITP-OF-ASH-IN-RANGE))
               (12 12
                   (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BITP))
               (12 6 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
               (12 6 (:REWRITE BFIX-WHEN-BIT->BOOL))
               (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
               (8 8 (:TYPE-PRESCRIPTION NFIX))
               (4 4
                  (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
               (2 2
                  (:REWRITE BITOPS::B-IOR-EQUAL-1-IN-CONCL))
               (1 1
                  (:TYPE-PRESCRIPTION LOGBITP-MISMATCH)))
(FAST-LOGREV-U64 (45 7 (:REWRITE ZIP-OPEN))
                 (42 10 (:REWRITE BITOPS::LOGREV-WHEN-ZIP))
                 (38 5 (:REWRITE ASH-0))
                 (18 18
                     (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
                 (16 16
                     (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP))
                 (11 11 (:TYPE-PRESCRIPTION ZIP))
                 (10 10 (:REWRITE BITOPS::LOGREV-WHEN-ZP))
                 (9 3 (:REWRITE LOGTAIL-IDENTITY))
                 (8 8
                    (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
                 (8 8 (:REWRITE DEFAULT-<-2))
                 (8 8 (:REWRITE DEFAULT-<-1))
                 (8 2 (:REWRITE LOGHEAD-IDENTITY))
                 (8 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 2))
                 (7 7
                    (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
                 (7 4
                    (:REWRITE BITOPS::LOGAND-WITH-NEGATED-BITMASK))
                 (7 1
                    (:LINEAR BITOPS::LOGREV-UPPER-BOUND . 1))
                 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP)))
