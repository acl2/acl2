(STR::STRRPOS-FAST (760 40 (:DEFINITION LEN))
                   (616 6 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (435 80 (:REWRITE LEN-WHEN-ATOM))
                   (360 5 (:REWRITE LEN-OF-NTHCDR))
                   (236 46 (:REWRITE DEFAULT-CDR))
                   (214 127 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (186 6
                        (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (182 6 (:DEFINITION NTHCDR))
                   (173 173 (:REWRITE CONSP-BY-LEN))
                   (160 5 (:REWRITE CONSP-OF-NTHCDR))
                   (135 7 (:REWRITE NATP-RW))
                   (110 65 (:REWRITE DEFAULT-+-2))
                   (81 12 (:REWRITE NTHCDR-WHEN-ZP))
                   (70 65 (:REWRITE DEFAULT-+-1))
                   (67 12 (:REWRITE NTHCDR-WHEN-ATOM))
                   (55 13 (:REWRITE ZP-OPEN))
                   (54 54 (:LINEAR LEN-WHEN-PREFIXP))
                   (46 46 (:REWRITE CONSP-OF-CDR-BY-LEN))
                   (45 33 (:REWRITE DEFAULT-<-1))
                   (39 33 (:REWRITE DEFAULT-<-2))
                   (38 11 (:REWRITE COMMUTATIVITY-OF-+))
                   (37 37
                       (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (31 6
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                   (27 27
                       (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                   (18 6 (:REWRITE <-0-+-NEGATIVE-1))
                   (6 6 (:REWRITE PREFIXP-TRANSITIVE . 2))
                   (6 6 (:REWRITE PREFIXP-TRANSITIVE . 1))
                   (6 6
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                   (6 6
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                   (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                   (4 4 (:REWRITE EQUAL-CONSTANT-+)))
(STR::STRRPOS-FAST-TYPE)
(STR::STRRPOS-FAST-UPPER-BOUND
     (1983 16
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (1065 13 (:REWRITE LEN-OF-NTHCDR))
     (893 47 (:DEFINITION LEN))
     (656 656 (:TYPE-PRESCRIPTION LEN))
     (495 15 (:REWRITE CONSP-OF-NTHCDR))
     (492 492
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (484 94 (:REWRITE LEN-WHEN-ATOM))
     (452 15
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (391 12 (:DEFINITION NTHCDR))
     (319 16 (:REWRITE NATP-RW))
     (307 59 (:REWRITE DEFAULT-CDR))
     (285 166 (:REWRITE STR::CONSP-OF-EXPLODE))
     (225 225 (:REWRITE CONSP-BY-LEN))
     (201 24 (:REWRITE NTHCDR-WHEN-ZP))
     (179 113 (:REWRITE DEFAULT-+-2))
     (169 34 (:REWRITE ZP-OPEN))
     (152 15
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (144 24 (:REWRITE NTHCDR-WHEN-ATOM))
     (143 86 (:REWRITE DEFAULT-<-2))
     (140 20 (:REWRITE <-+-NEGATIVE-0-1))
     (129 113 (:REWRITE DEFAULT-+-1))
     (125 86 (:REWRITE DEFAULT-<-1))
     (98 98 (:LINEAR LEN-WHEN-PREFIXP))
     (91 25 (:REWRITE COMMUTATIVITY-OF-+))
     (72 2 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
     (66 30
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (63 21 (:REWRITE <-0-+-NEGATIVE-1))
     (59 59 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (59 18
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (49 49
         (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (39 3 (:REWRITE COMMUTATIVITY-2-OF-+))
     (37 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (37 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (28 28
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (24 12 (:REWRITE FOLD-CONSTS-IN-+))
     (24 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (16 16 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 3
         (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
     (1 1 (:TYPE-PRESCRIPTION LIST-EQUIV)))
(STR::STRRPOS-FAST-WHEN-EMPTY
     (432 4 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (398 2
          (:LINEAR STR::STRRPOS-FAST-UPPER-BOUND))
     (320 4 (:REWRITE LEN-OF-NTHCDR))
     (217 13 (:DEFINITION LEN))
     (193 193 (:TYPE-PRESCRIPTION LEN))
     (148 4
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (128 4 (:REWRITE CONSP-OF-NTHCDR))
     (124 4 (:DEFINITION NTHCDR))
     (116 64
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (115 26 (:REWRITE LEN-WHEN-ATOM))
     (102 6 (:REWRITE NATP-RW))
     (77 17 (:REWRITE DEFAULT-CDR))
     (64 8 (:REWRITE NTHCDR-WHEN-ZP))
     (58 58 (:REWRITE CONSP-BY-LEN))
     (56 8 (:REWRITE <-+-NEGATIVE-0-1))
     (48 8 (:REWRITE NTHCDR-WHEN-ATOM))
     (46 29 (:REWRITE DEFAULT-+-2))
     (40 12 (:REWRITE ZP-OPEN))
     (33 29 (:REWRITE DEFAULT-+-1))
     (28 20 (:REWRITE DEFAULT-<-1))
     (28 8 (:REWRITE COMMUTATIVITY-OF-+))
     (24 24 (:LINEAR LEN-WHEN-PREFIXP))
     (24 20 (:REWRITE DEFAULT-<-2))
     (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 8
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (12 12 (:TYPE-PRESCRIPTION ZP))
     (12 12
         (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (12 4 (:REWRITE <-0-+-NEGATIVE-1))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (4 4 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (4 4
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
     (4 4 (:REWRITE DEFAULT-UNARY-MINUS)))
(STR::STRRPOS$INLINE (133 7 (:DEFINITION LEN))
                     (84 14 (:REWRITE LEN-WHEN-ATOM))
                     (60 60
                         (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
                     (39 23 (:REWRITE STR::CONSP-OF-EXPLODE))
                     (35 7 (:REWRITE DEFAULT-CDR))
                     (30 30 (:REWRITE CONSP-BY-LEN))
                     (14 7 (:REWRITE DEFAULT-+-2))
                     (7 7
                        (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                     (7 7 (:REWRITE DEFAULT-+-1))
                     (7 7 (:REWRITE CONSP-OF-CDR-BY-LEN))
                     (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                     (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                     (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                     (1 1
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                     (1 1
                        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1)))
(STR::STRRPOS-TYPE)
(STR::LEMMA (22009 152
                   (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
            (17445 58
                   (:LINEAR STR::STRRPOS-FAST-UPPER-BOUND))
            (15429 235 (:REWRITE LEN-OF-NTHCDR))
            (10944 576 (:DEFINITION LEN))
            (8384 140 (:REWRITE CONSP-OF-NTHCDR))
            (7654 160 (:REWRITE NATP-RW))
            (6692 155 (:REWRITE PREFIXP-TRANSITIVE . 1))
            (5715 109 (:REWRITE NTHCDR-WHEN-ZP))
            (5633 126 (:REWRITE ZP-OPEN))
            (5500 489 (:LINEAR LEN-WHEN-PREFIXP))
            (5402 1152 (:REWRITE LEN-WHEN-ATOM))
            (5044 5044
                  (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
            (4327 143
                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
            (4189 145
                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
            (4074 52 (:DEFINITION NTHCDR))
            (3192 628 (:REWRITE DEFAULT-CDR))
            (3002 112 (:REWRITE <-+-NEGATIVE-0-2))
            (2872 1724 (:REWRITE STR::CONSP-OF-EXPLODE))
            (2352 2352 (:REWRITE CONSP-BY-LEN))
            (1914 1171 (:REWRITE DEFAULT-+-2))
            (1282 816
                  (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
            (1229 1171 (:REWRITE DEFAULT-+-1))
            (806 7 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
            (784 7 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
            (784 7 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
            (711 288
                 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
            (654 109 (:REWRITE NTHCDR-WHEN-ATOM))
            (650 116
                 (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
            (628 628 (:REWRITE CONSP-OF-CDR-BY-LEN))
            (612 490 (:REWRITE DEFAULT-<-1))
            (579 490 (:REWRITE DEFAULT-<-2))
            (570 171 (:REWRITE COMMUTATIVITY-OF-+))
            (452 44 (:REWRITE COMMUTATIVITY-2-OF-+))
            (330 235 (:REWRITE DEFAULT-UNARY-MINUS))
            (318 106 (:REWRITE <-0-+-NEGATIVE-1))
            (258 39 (:REWRITE <-+-NEGATIVE-0-1))
            (256 256
                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
            (256 165
                 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
            (248 248
                 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
            (196 124 (:REWRITE FOLD-CONSTS-IN-+))
            (176 44
                 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
            (98 88 (:REWRITE EQUAL-CONSTANT-+))
            (7 7 (:TYPE-PRESCRIPTION LIST-EQUIV)))
(STR::PREFIXP-OF-STRRPOS (2122 97
                               (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                         (1256 20 (:REWRITE NTHCDR-WHEN-ZP))
                         (1184 266 (:REWRITE DEFAULT-CDR))
                         (1168 1168 (:REWRITE CONSP-BY-LEN))
                         (996 9 (:DEFINITION NTHCDR))
                         (874 4
                              (:LINEAR STR::STRRPOS-FAST-UPPER-BOUND))
                         (684 387 (:REWRITE DEFAULT-+-2))
                         (404 387 (:REWRITE DEFAULT-+-1))
                         (279 279 (:REWRITE CONSP-OF-CDR-BY-LEN))
                         (196 196 (:LINEAR LEN-WHEN-PREFIXP))
                         (130 113 (:REWRITE DEFAULT-<-2))
                         (126 21 (:REWRITE NATP-RW))
                         (117 113 (:REWRITE DEFAULT-<-1))
                         (90 90 (:REWRITE PREFIXP-TRANSITIVE . 2))
                         (90 90 (:REWRITE PREFIXP-TRANSITIVE . 1))
                         (90 90
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                         (90 90
                             (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                         (84 84
                             (:REWRITE LENGTH-ZERO-WHEN-STRINGP-ALT))
                         (83 83 (:REWRITE OPEN-SMALL-NTHCDR))
                         (63 63 (:TYPE-PRESCRIPTION NATP))
                         (39 13
                             (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                         (34 9 (:REWRITE COMMUTATIVITY-OF-+))
                         (24 24
                             (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                         (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
                         (15 2 (:REWRITE <-+-NEGATIVE-0-2))
                         (8 8 (:REWRITE CONSP-OF-CDDR-BY-LEN))
                         (6 2 (:DEFINITION TRUE-LISTP))
                         (6 1
                            (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                         (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
                         (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
                         (3 1 (:REWRITE |(equal 0 (len x))|))
                         (2 1 (:DEFINITION ATOM)))
(STR::MY-INDUCTION (131 1 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
                   (80 1 (:REWRITE LEN-OF-NTHCDR))
                   (57 3 (:DEFINITION LEN))
                   (46 46 (:TYPE-PRESCRIPTION LEN))
                   (37 1
                       (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                   (32 1 (:REWRITE CONSP-OF-NTHCDR))
                   (31 6 (:REWRITE LEN-WHEN-ATOM))
                   (30 2 (:REWRITE NATP-RW))
                   (30 1 (:DEFINITION NTHCDR))
                   (21 4 (:REWRITE DEFAULT-CDR))
                   (19 11 (:REWRITE STR::CONSP-OF-EXPLODE))
                   (15 15 (:REWRITE CONSP-BY-LEN))
                   (14 2 (:REWRITE <-+-NEGATIVE-0-1))
                   (13 2 (:REWRITE NTHCDR-WHEN-ZP))
                   (12 8 (:REWRITE DEFAULT-+-2))
                   (12 2 (:REWRITE NTHCDR-WHEN-ATOM))
                   (11 9 (:DEFINITION NOT))
                   (11 8 (:REWRITE DEFAULT-<-1))
                   (9 8 (:REWRITE DEFAULT-<-2))
                   (9 8 (:REWRITE DEFAULT-+-1))
                   (9 2 (:REWRITE ZP-OPEN))
                   (7 2 (:REWRITE COMMUTATIVITY-OF-+))
                   (6 6 (:TYPE-PRESCRIPTION NATP))
                   (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                   (6 1
                      (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
                   (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
                   (3 3
                      (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
                   (3 1 (:REWRITE <-0-+-NEGATIVE-1))
                   (2 2
                      (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
                   (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
                   (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
                   (1 1
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                   (1 1
                      (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                   (1 1 (:REWRITE OPEN-SMALL-NTHCDR))
                   (1 1 (:REWRITE DEFAULT-UNARY-MINUS)))
(STR::LEMMA (17428 137
                   (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
            (11956 223 (:REWRITE LEN-OF-NTHCDR))
            (9956 524 (:DEFINITION LEN))
            (5290 137 (:REWRITE PREFIXP-TRANSITIVE . 1))
            (4773 1048 (:REWRITE LEN-WHEN-ATOM))
            (4542 630 (:LINEAR LEN-WHEN-PREFIXP))
            (4333 4333
                  (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
            (3419 117 (:REWRITE CONSP-OF-NTHCDR))
            (2854 563 (:REWRITE DEFAULT-CDR))
            (2460 202 (:REWRITE NATP-RW))
            (2410 1467 (:REWRITE STR::CONSP-OF-EXPLODE))
            (2292 123
                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
            (2204 123
                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
            (2030 2030 (:REWRITE CONSP-BY-LEN))
            (1791 1167 (:REWRITE DEFAULT-+-2))
            (1252 39 (:DEFINITION NTHCDR))
            (1226 1167 (:REWRITE DEFAULT-+-1))
            (934 154 (:REWRITE <-+-NEGATIVE-0-1))
            (829 258 (:REWRITE COMMUTATIVITY-OF-+))
            (629 78 (:REWRITE NTHCDR-WHEN-ZP))
            (578 438 (:REWRITE DEFAULT-<-1))
            (563 563 (:REWRITE CONSP-OF-CDR-BY-LEN))
            (528 85 (:REWRITE ZP-OPEN))
            (516 234
                 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
            (478 438 (:REWRITE DEFAULT-<-2))
            (464 44 (:REWRITE COMMUTATIVITY-2-OF-+))
            (463 78 (:REWRITE NTHCDR-WHEN-ATOM))
            (361 157
                 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
            (317 317
                 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
            (266 14 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
            (227 223 (:REWRITE DEFAULT-UNARY-MINUS))
            (226 46
                 (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
            (198 66 (:REWRITE <-0-+-NEGATIVE-1))
            (177 177
                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
            (176 44
                 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
            (156 52
                 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
            (154 110 (:REWRITE FOLD-CONSTS-IN-+))
            (94 94 (:REWRITE EQUAL-CONSTANT-+))
            (84 14
                (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
            (84 14 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
            (60 10 (:REWRITE RIGHT-CANCELLATION-FOR-+))
            (60 8 (:REWRITE <-+-NEGATIVE-0-2))
            (40 40 (:DEFINITION FIX))
            (39 39 (:REWRITE OPEN-SMALL-NTHCDR))
            (30 10 (:REWRITE EQUAL-MINUS-MINUS))
            (14 14 (:TYPE-PRESCRIPTION LIST-EQUIV)))
(STR::COMPLETENESS-OF-STRRPOS
     (1177 12
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (953 56 (:DEFINITION LEN))
     (712 14
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (683 13 (:REWRITE LEN-OF-NTHCDR))
     (348 14
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (322 11 (:REWRITE CONSP-OF-NTHCDR))
     (272 68 (:LINEAR LEN-WHEN-PREFIXP))
     (271 62 (:REWRITE DEFAULT-CDR))
     (234 234 (:REWRITE CONSP-BY-LEN))
     (233 6 (:DEFINITION NTHCDR))
     (199 14 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (162 91 (:REWRITE DEFAULT-+-2))
     (158 12 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (142 13 (:REWRITE NATP-RW))
     (141 83
          (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (138 12 (:REWRITE NTHCDR-WHEN-ZP))
     (105 91 (:REWRITE DEFAULT-+-1))
     (70 10 (:REWRITE <-+-NEGATIVE-0-1))
     (67 15 (:REWRITE COMMUTATIVITY-OF-+))
     (62 62 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (56 39 (:REWRITE DEFAULT-<-1))
     (52 21
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (50 25
         (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (46 39 (:REWRITE DEFAULT-<-2))
     (19 6 (:REWRITE <-0-+-NEGATIVE-1))
     (14 14 (:REWRITE OPEN-SMALL-NTHCDR))
     (13 13 (:TYPE-PRESCRIPTION ZP))
     (13 9 (:REWRITE DEFAULT-UNARY-MINUS))
     (12 4 (:REWRITE UNICITY-OF-0))
     (12 4 (:REWRITE |(equal 0 (len x))|))
     (8 4 (:DEFINITION FIX))
     (8 4 (:DEFINITION ATOM))
     (6 6
        (:REWRITE LENGTH-ZERO-WHEN-STRINGP-ALT))
     (4 4 (:REWRITE STR-FIX-WHEN-STRINGP))
     (4 4 (:REWRITE STR-FIX-DEFAULT))
     (4 4
        (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (4 4 (:REWRITE INVERSE-OF-+)))
(STR::STRRPOS-UPPER-BOUND-WEAK
     (491 2 (:DEFINITION STR::STRRPOS-FAST))
     (302 16 (:DEFINITION LEN))
     (160 2 (:DEFINITION NTHCDR))
     (155 32 (:REWRITE LEN-WHEN-ATOM))
     (142 8 (:REWRITE ZP-OPEN))
     (128 4 (:REWRITE NTHCDR-WHEN-ZP))
     (94 59 (:REWRITE STR::CONSP-OF-EXPLODE))
     (90 18 (:REWRITE DEFAULT-CDR))
     (78 2
         (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (77 77 (:REWRITE CONSP-BY-LEN))
     (69 2 (:REWRITE LEN-OF-NTHCDR))
     (54 4
         (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (54 2 (:REWRITE CONSP-OF-NTHCDR))
     (46 24 (:REWRITE DEFAULT-+-2))
     (32 8 (:DEFINITION NFIX))
     (30 6 (:REWRITE DEFAULT-<-2))
     (30 6 (:REWRITE |(< 0 (len x))|))
     (28 24 (:REWRITE DEFAULT-+-1))
     (24 4 (:REWRITE NTHCDR-WHEN-ATOM))
     (20 4 (:DEFINITION LNFIX$INLINE))
     (18 18
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (18 18 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (16 8 (:REWRITE NEGATIVE-WHEN-NATP))
     (12 6
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (12 4
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (11 2
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (8 8 (:LINEAR LEN-WHEN-PREFIXP))
     (8 6 (:REWRITE DEFAULT-<-1))
     (8 2 (:REWRITE COMMUTATIVITY-OF-+))
     (8 2 (:REWRITE <-0-+-NEGATIVE-1))
     (6 6
        (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (6 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (4 4 (:TYPE-PRESCRIPTION ZP))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
     (2 2
        (:REWRITE LENGTH-ZERO-WHEN-STRINGP-ALT))
     (2 2 (:REWRITE INVERSE-OF-+))
     (1 1 (:REWRITE STR-FIX-DEFAULT)))
(STR::LEMMA (2711 147 (:DEFINITION LEN))
            (1490 294 (:REWRITE LEN-WHEN-ATOM))
            (821 163 (:REWRITE DEFAULT-CDR))
            (696 16 (:DEFINITION NTHCDR))
            (653 653 (:REWRITE CONSP-BY-LEN))
            (488 32 (:REWRITE NTHCDR-WHEN-ZP))
            (393 228 (:REWRITE DEFAULT-+-2))
            (245 228 (:REWRITE DEFAULT-+-1))
            (184 32 (:REWRITE NTHCDR-WHEN-ATOM))
            (181 16
                 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
            (172 4 (:REWRITE POSP-RW))
            (163 163 (:REWRITE CONSP-OF-CDR-BY-LEN))
            (132 132
                 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
            (125 18 (:REWRITE <-+-NEGATIVE-0-1))
            (118 29
                 (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
            (116 91 (:REWRITE DEFAULT-<-2))
            (110 4 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
            (93 32
                (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
            (64 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
            (64 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
            (29 29 (:TYPE-PRESCRIPTION ZP))
            (27 27 (:REWRITE PREFIXP-TRANSITIVE . 1))
            (25 21 (:REWRITE DEFAULT-UNARY-MINUS))
            (24 5
                (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
            (11 11
                (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
            (5 5
               (:REWRITE MINUS-CANCELLATION-ON-RIGHT))
            (5 5 (:REWRITE INVERSE-OF-+))
            (4 1
               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(STR::STRRPOS-UPPER-BOUND-STRONG
     (707 3 (:DEFINITION STR::STRRPOS-FAST))
     (468 26 (:DEFINITION LEN))
     (278 3 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (254 52 (:REWRITE LEN-WHEN-ATOM))
     (228 228
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (222 3 (:DEFINITION NTHCDR))
     (174 6 (:REWRITE NTHCDR-WHEN-ZP))
     (159 12 (:REWRITE ZP-OPEN))
     (145 29 (:REWRITE DEFAULT-CDR))
     (111 111 (:REWRITE CONSP-BY-LEN))
     (108 3
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (101 3 (:REWRITE LEN-OF-NTHCDR))
     (82 82 (:REWRITE STR::CONSP-OF-EXPLODE))
     (78 3 (:REWRITE CONSP-OF-NTHCDR))
     (73 38 (:REWRITE DEFAULT-+-2))
     (44 38 (:REWRITE DEFAULT-+-1))
     (36 9 (:DEFINITION NFIX))
     (33 6 (:REWRITE NTHCDR-WHEN-ATOM))
     (29 29 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (26 26
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (21 6
         (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
     (18 9
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (18 9 (:REWRITE NEGATIVE-WHEN-NATP))
     (18 6
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (15 3 (:DEFINITION LNFIX$INLINE))
     (12 12 (:LINEAR LEN-WHEN-PREFIXP))
     (12 6 (:REWRITE DEFAULT-<-2))
     (12 3 (:REWRITE COMMUTATIVITY-OF-+))
     (12 3 (:REWRITE <-0-+-NEGATIVE-1))
     (9 9
        (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (6 6 (:TYPE-PRESCRIPTION ZP))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (3 3 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (3 3
        (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (3 3 (:REWRITE OPEN-SMALL-NTHCDR))
     (3 3
        (:REWRITE LENGTH-ZERO-WHEN-STRINGP-ALT))
     (3 3 (:REWRITE INVERSE-OF-+)))
(STR::LENS-SAME-WHEN-LIST-EQUIV)
(STR::LEN-OF-NTHCDR (54 9 (:REWRITE NEGATIVE-WHEN-NATP))
                    (33 5 (:REWRITE NATP-RW))
                    (27 3 (:DEFINITION LEN))
                    (14 14 (:TYPE-PRESCRIPTION NATP))
                    (13 10 (:REWRITE DEFAULT-<-1))
                    (11 10 (:REWRITE DEFAULT-<-2))
                    (10 10 (:REWRITE CONSP-BY-LEN))
                    (8 5 (:REWRITE DEFAULT-+-2))
                    (6 6 (:LINEAR LEN-WHEN-PREFIXP))
                    (6 5 (:REWRITE DEFAULT-+-1))
                    (3 3 (:REWRITE DEFAULT-CDR))
                    (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
                    (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
                    (1 1
                       (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
(STR::LEN-BOUNDED-BY-PREFIXP (18 2 (:DEFINITION LEN))
                             (10 4 (:REWRITE LEN-WHEN-ATOM))
                             (6 6 (:REWRITE CONSP-BY-LEN))
                             (4 2 (:REWRITE DEFAULT-+-2))
                             (2 2 (:REWRITE DEFAULT-CDR))
                             (2 2 (:REWRITE DEFAULT-+-1))
                             (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN)))
(STR::PREFIXP-OF-SELF-AND-CDR (20 20 (:REWRITE CONSP-BY-LEN))
                              (16 8 (:REWRITE DEFAULT-+-2))
                              (13 13 (:REWRITE CONSP-OF-CDR-BY-LEN))
                              (8 8 (:REWRITE DEFAULT-+-1))
                              (4 4 (:REWRITE CONSP-OF-CDDR-BY-LEN))
                              (3 1
                                 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
                              (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
                              (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
                              (2 2
                                 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
                              (2 2
                                 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
                              (2 2 (:LINEAR LEN-WHEN-PREFIXP))
                              (2 1
                                 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT)))
(STR::PREFIXP-OF-NTHCDR-BOUNDS-N
     (1965 34
           (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (890 34
          (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (773 412 (:REWRITE DEFAULT-+-2))
     (573 34 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (507 242 (:REWRITE DEFAULT-CDR))
     (496 496 (:REWRITE CONSP-BY-LEN))
     (450 412 (:REWRITE DEFAULT-+-1))
     (450 18 (:REWRITE CONSP-OF-NTHCDR))
     (362 34 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (351 351 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (302 5 (:REWRITE CAR-OF-NTHCDR))
     (274 34
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (259 10 (:REWRITE NTH-WHEN-BIGGER))
     (187 132 (:REWRITE DEFAULT-<-2))
     (175 5 (:DEFINITION NTH))
     (172 132 (:REWRITE DEFAULT-<-1))
     (138 34
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
     (134 18 (:REWRITE NATP-RW))
     (107 29 (:REWRITE ZP-OPEN))
     (88 88 (:REWRITE CONSP-OF-CDDR-BY-LEN))
     (54 54 (:TYPE-PRESCRIPTION NATP))
     (43 35 (:REWRITE DEFAULT-UNARY-MINUS))
     (36 34
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (36 12 (:REWRITE <-0-+-NEGATIVE-1))
     (34 34 (:REWRITE DEFAULT-CAR))
     (33 16 (:REWRITE NTHCDR-WHEN-ATOM))
     (11 11 (:REWRITE CONSP-OF-CDDDR-BY-LEN))
     (6 1 (:REWRITE NATP-POSP--1))
     (5 5 (:REWRITE NTH-WHEN-PREFIXP))
     (3 1 (:REWRITE POSP-RW))
     (1 1 (:TYPE-PRESCRIPTION POSP))
     (1 1
        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (1 1 (:REWRITE NATP-POSP))
     (1 1 (:REWRITE EQUAL-CONSTANT-+)))
(STR::LEMMA1 (5682 56
                   (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
             (5092 268 (:DEFINITION LEN))
             (2651 536 (:REWRITE LEN-WHEN-ATOM))
             (1616 314 (:REWRITE DEFAULT-CDR))
             (1590 50
                   (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
             (1510 46 (:DEFINITION NTHCDR))
             (1394 46 (:REWRITE CONSP-OF-NTHCDR))
             (1218 1218 (:REWRITE CONSP-BY-LEN))
             (800 507 (:REWRITE DEFAULT-+-2))
             (789 92 (:REWRITE NTHCDR-WHEN-ZP))
             (552 92 (:REWRITE NTHCDR-WHEN-ATOM))
             (531 507 (:REWRITE DEFAULT-+-1))
             (384 50
                  (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
             (371 53
                  (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
             (350 268 (:REWRITE DEFAULT-<-2))
             (337 268 (:REWRITE DEFAULT-<-1))
             (314 314 (:REWRITE CONSP-OF-CDR-BY-LEN))
             (219 219
                  (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
             (210 92
                  (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
             (132 19 (:REWRITE POSP-RW))
             (125 65
                  (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
             (114 6 (:REWRITE PREFIXP-NTHCDR-NTHCDR))
             (106 19 (:REWRITE NATP-POSP))
             (79 59 (:REWRITE DEFAULT-UNARY-MINUS))
             (70 7 (:REWRITE COMMUTATIVITY-2-OF-+))
             (56 56 (:REWRITE PREFIXP-TRANSITIVE . 1))
             (53 53
                 (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
             (53 53
                 (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
             (48 12 (:REWRITE <-+-NEGATIVE-0-1))
             (36 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
             (36 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
             (28 7
                 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
             (16 4
                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
             (7 7 (:REWRITE EQUAL-CONSTANT-+))
             (6 6 (:TYPE-PRESCRIPTION LIST-EQUIV))
             (4 4 (:REWRITE NATP-RW)))
(STR::STRRPOS-UPPER-BOUND-STRONGER
     (2189 6 (:DEFINITION STR::STRRPOS-FAST))
     (1072 6 (:DEFINITION NTHCDR))
     (1018 24 (:REWRITE ZP-OPEN))
     (1002 54 (:DEFINITION LEN))
     (976 12 (:REWRITE NTHCDR-WHEN-ZP))
     (564 108 (:REWRITE LEN-WHEN-ATOM))
     (550 550
          (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
     (531 12
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
     (440 17
          (:LINEAR STR::STRRPOS-UPPER-BOUND-STRONG))
     (314 218 (:REWRITE STR::CONSP-OF-EXPLODE))
     (300 60 (:REWRITE DEFAULT-CDR))
     (290 6 (:REWRITE STR::LEN-OF-NTHCDR))
     (278 278 (:REWRITE CONSP-BY-LEN))
     (234 6
          (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
     (163 13
          (:LINEAR LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (162 6 (:REWRITE CONSP-OF-NTHCDR))
     (146 76 (:REWRITE DEFAULT-+-2))
     (126 20
          (:REWRITE STR::STRRPOS-FAST-WHEN-EMPTY))
     (120 6 (:REWRITE LEN-WHEN-PREFIXP))
     (109 24 (:DEFINITION NFIX))
     (90 18 (:REWRITE |(< 0 (len x))|))
     (86 76 (:REWRITE DEFAULT-+-1))
     (73 12 (:DEFINITION LNFIX$INLINE))
     (72 12 (:REWRITE NTHCDR-WHEN-ATOM))
     (68 68
         (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
     (60 60 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (46 23 (:REWRITE NEGATIVE-WHEN-NATP))
     (36 12
         (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
     (36 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
     (36 6 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
     (26 26
         (:LINEAR STR::PREFIXP-OF-NTHCDR-BOUNDS-N))
     (26 26 (:LINEAR LEN-WHEN-PREFIXP))
     (26 26
         (:LINEAR STR::LEN-BOUNDED-BY-PREFIXP))
     (26 14 (:REWRITE DEFAULT-<-2))
     (24 6 (:REWRITE <-0-+-NEGATIVE-1))
     (18 18
         (:REWRITE LEN-OF-NONEMPTY-STRING-IS-POSITIVE))
     (18 14 (:REWRITE DEFAULT-<-1))
     (12 12 (:TYPE-PRESCRIPTION ZP))
     (12 12 (:REWRITE PREFIXP-TRANSITIVE . 2))
     (12 12 (:REWRITE PREFIXP-TRANSITIVE . 1))
     (12 12
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
     (12 12
         (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
     (6 6 (:TYPE-PRESCRIPTION PREFIXP))
     (6 6 (:TYPE-PRESCRIPTION LIST-EQUIV))
     (6 6 (:REWRITE OPEN-SMALL-NTHCDR))
     (6 6
        (:REWRITE LENGTH-ZERO-WHEN-STRINGP-ALT))
     (4 2 (:REWRITE DEFAULT-UNARY-MINUS)))
