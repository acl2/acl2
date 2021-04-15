(|LACK-base|)
(LACK-DEFAULT)
(|LACK-test| (2 2
                (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X)))
(|iLACK| (10 10
             (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X)))
(|iLACK-DOMAIN| (4 4
                   (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X)))
(|ARB-iLACK-INDEX-THM|)
(|iLACK-MONO-DETERM| (110 110
                          (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                     (17 17
                         (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION)))
(|iLACK-DOMAIN-MONOTONE|)
(|iLACK-DOMAIN-MONOTONE-CONTRAPOSITIVE|)
(|iLACK-DOMAIN-LOWER-BOUND|)
(|iLACK-MIN-INDEX|)
(|NATP-iLACK-MIN-INDEX|)
(|iLACK-DOMAIN-MIN-INDEX|)
(|iLACK-MIN-INDEX-BOUND|)
(|iLACK-MIN-INDEX-SMALLEST|)
(LACK-MEASURE)
(LACK-MEASURE-TYPE)
(LACK-MEASURE-PROPERTY)
(LACK-MEASURE-SMALLEST)
(|REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE|
     (4 4
        (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
     (4 4
        (:TYPE-PRESCRIPTION DEFUNG::NOT-TRUE-FROM-NOT-X))
     (4 4
        (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
     (4 1 (:LINEAR LACK-MEASURE-SMALLEST)))
(|REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE-2|)
(|REPLACE-iLACK-DOMAIN-INDEX-BY-LACK-MEASURE|
     (2 2 (:REWRITE |iLACK-DOMAIN-MONOTONE|)))
(LACK)
(LACK-DOMAIN)
(NOT-LACK-DOMAIN-IMPLIES-ZERO-LACK-MEASURE
     (2 1
        (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION)))
(LACK-MEASURE-BODY (4 4
                      (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X)))
(LACK-MEASURE-DEFINITION (469 469
                              (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                         (129 85 (:LINEAR LACK-MEASURE-SMALLEST))
                         (119 119
                              (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                         (57 21 (:REWRITE DEFUNG::TRUE-FROM-X))
                         (57 21
                             (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                         (21 21 (:REWRITE DEFUNG::QUOTED-TRUE)))
(LACK-DOMAIN-DEFINITION (482 482
                             (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                        (66 33 (:REWRITE DEFUNG::TRUE-FROM-X))
                        (66 33
                            (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                        (33 33 (:REWRITE DEFUNG::QUOTED-TRUE)))
(LACK-DEFINITION (189 189
                      (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                 (81 66
                     (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                 (64 26
                     (:REWRITE |REPLACE-ARB-iLACK-INDEX-BY-LACK-MEASURE|))
                 (41 9 (:REWRITE |iLACK-DOMAIN-MONOTONE|))
                 (26 13 (:REWRITE DEFUNG::TRUE-FROM-X))
                 (26 13
                     (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                 (13 13 (:REWRITE DEFUNG::QUOTED-TRUE)))
(LACK-INDUCTION (713 23 (:DEFINITION LACK-DEFINITION))
                (569 569
                     (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                (172 172
                     (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                (90 30
                    (:TYPE-PRESCRIPTION DEFUNG::NATP-MAX))
                (76 38 (:REWRITE DEFUNG::TRUE-FROM-X))
                (76 38
                    (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                (38 38 (:REWRITE DEFUNG::QUOTED-TRUE))
                (23 23
                    (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS)))
(LACK-INDUCTION-IS-LACK-DOMAIN
     (183 183
          (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
     (172 10 (:DEFINITION LACK-DEFINITION))
     (18 18
         (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
     (18 9 (:REWRITE DEFUNG::TRUE-FROM-X))
     (18 9
         (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
     (9 9 (:REWRITE DEFUNG::QUOTED-TRUE))
     (8 4 (:DEFINITION NOT)))
(LACK-INDUCTION-RULE)
(OPEN-LACK-DOMAIN (32 2 (:DEFINITION LACK-DEFINITION))
                  (17 17
                      (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                  (4 4
                     (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                  (2 2
                     (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS)))
(LACK-DOMAIN-TRUE (1 1 (:REWRITE OPEN-LACK-DOMAIN)))
(OPEN-LACK-BASE)
(OPEN-LACK-INDUCTION (24 24
                         (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                     (20 8 (:REWRITE LACK-DOMAIN-TRUE))
                     (9 9
                        (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                     (8 8
                        (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
                     (2 1 (:REWRITE DEFUNG::TRUE-FROM-X))
                     (2 1
                        (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                     (1 1 (:REWRITE DEFUNG::QUOTED-TRUE)))
(OPEN-LACK-MEASURE-BASE)
(OPEN-LACK-MEASURE-INDUCTION
     (44 2 (:DEFINITION LACK-DEFINITION))
     (27 27
         (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
     (8 4 (:REWRITE LACK-DOMAIN-TRUE))
     (4 4
        (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
     (2 2
        (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS)))
(INTEGERP-INTEGERP-IMPLIES-INTEGERP-LACK
     (175 175
          (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
     (63 54
         (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
     (54 54 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (54 54 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (54 45 (:REWRITE O-INFP->NEQ-0))
     (45 45 (:META *META*-UNHIDE-HIDE))
     (41 41
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (36 9 (:REWRITE EQUAL-CONSTANT-+))
     (28 28 (:REWRITE DEFAULT-+-2))
     (28 28 (:REWRITE DEFAULT-+-1)))
(ACK-DEFAULT)
(XACK)
(XACK (1137 65 (:REWRITE OPEN-LACK-INDUCTION))
      (988 247 (:REWRITE EQUAL-CONSTANT-+))
      (915 915 (:META CANCEL_TIMES-EQUAL-CORRECT))
      (915 915 (:META CANCEL_PLUS-EQUAL-CORRECT))
      (848 591 (:REWRITE O-INFP->NEQ-0))
      (763 763
           (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
      (570 570 (:REWRITE DEFAULT-+-2))
      (570 570 (:REWRITE DEFAULT-+-1))
      (500 500 (:META *META*-UNHIDE-HIDE))
      (247 73 (:REWRITE DEFUNG::TRUE-FROM-X))
      (195 65
           (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
      (73 73 (:REWRITE DEFUNG::QUOTED-TRUE))
      (42 31 (:REWRITE DEFAULT-CAR))
      (40 29 (:REWRITE DEFAULT-CDR))
      (6 6 (:TYPE-PRESCRIPTION O-FINP))
      (6 2 (:REWRITE O-FIRST-EXPT-O-INFP))
      (4 2 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
(ACK-DOMAIN)
(ACK)
(ACK-MEASURE)
(ACK-DEFINITION (2094 520 (:REWRITE O-INFP->NEQ-0))
                (1511 753
                      (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                (1018 206 (:REWRITE EQUAL-CONSTANT-+))
                (856 856
                     (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                (822 822 (:TYPE-PRESCRIPTION O-FINP))
                (822 274 (:REWRITE O-FIRST-EXPT-O-INFP))
                (753 753 (:META CANCEL_TIMES-EQUAL-CORRECT))
                (619 619
                     (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                (554 554 (:TYPE-PRESCRIPTION BOOLEANP))
                (548 274 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                (529 529 (:REWRITE DEFAULT-+-1))
                (486 486 (:META *META*-UNHIDE-HIDE))
                (433 433
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                (120 24
                     (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                (96 24 (:REWRITE DEFUNG::TRUE-FROM-X))
                (24 24 (:REWRITE DEFUNG::QUOTED-TRUE))
                (13 3 (:REWRITE DEFUNG::NATP-FIX))
                (6 6 (:TYPE-PRESCRIPTION NATP))
                (4 3 (:REWRITE NATP-RW))
                (1 1
                   (:REWRITE INTEGERP-INTEGERP-IMPLIES-INTEGERP-LACK)))
(ACK-DOMAIN-DEFINITION (1049 265 (:REWRITE O-INFP->NEQ-0))
                       (769 389
                            (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                       (558 558
                            (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                       (520 104 (:REWRITE EQUAL-CONSTANT-+))
                       (408 408 (:TYPE-PRESCRIPTION O-FINP))
                       (408 136 (:REWRITE O-FIRST-EXPT-O-INFP))
                       (389 389 (:META CANCEL_TIMES-EQUAL-CORRECT))
                       (389 389 (:META CANCEL_PLUS-EQUAL-CORRECT))
                       (320 320
                            (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                       (276 276 (:TYPE-PRESCRIPTION BOOLEANP))
                       (272 136 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                       (262 262 (:REWRITE DEFAULT-+-1))
                       (240 240
                            (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                       (235 235 (:META *META*-UNHIDE-HIDE))
                       (90 18
                           (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                       (72 18 (:REWRITE DEFUNG::TRUE-FROM-X))
                       (18 18 (:REWRITE DEFUNG::QUOTED-TRUE))
                       (8 2 (:REWRITE DEFUNG::NATP-FIX))
                       (4 4 (:TYPE-PRESCRIPTION NATP))
                       (2 2 (:REWRITE NATP-RW)))
(ACK-MEASURE-DEFINITION (5919 214 (:REWRITE OPEN-LACK-BASE))
                        (2764 149 (:REWRITE LACK-DOMAIN-TRUE))
                        (2181 530 (:REWRITE O-INFP->NEQ-0))
                        (1556 756
                              (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
                        (1031 1031
                              (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
                        (1005 201 (:REWRITE EQUAL-CONSTANT-+))
                        (870 870 (:TYPE-PRESCRIPTION O-FINP))
                        (870 290 (:REWRITE O-FIRST-EXPT-O-INFP))
                        (756 756 (:META CANCEL_TIMES-EQUAL-CORRECT))
                        (756 756 (:META CANCEL_PLUS-EQUAL-CORRECT))
                        (735 27 (:REWRITE OPEN-LACK-MEASURE-BASE))
                        (607 607
                             (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
                        (580 580 (:TYPE-PRESCRIPTION BOOLEANP))
                        (580 290 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
                        (524 524 (:REWRITE DEFAULT-+-1))
                        (489 489 (:META *META*-UNHIDE-HIDE))
                        (450 450
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (440 27
                             (:REWRITE OPEN-LACK-MEASURE-INDUCTION))
                        (120 24
                             (:REWRITE DEFUNG::NOT-TRUE-FROM-NOT-X))
                        (96 24 (:REWRITE DEFUNG::TRUE-FROM-X))
                        (25 7 (:DEFINITION |LACK-base|))
                        (24 24 (:REWRITE DEFUNG::QUOTED-TRUE))
                        (20 10 (:REWRITE DEFAULT-<-1))
                        (18 10 (:REWRITE DEFAULT-<-2))
                        (2 2 (:TYPE-PRESCRIPTION NATP))
                        (1 1 (:REWRITE NATP-RW)))
(ACK-INDUCTION (12869 194 (:DEFINITION ACK-DEFINITION))
               (4056 2316 (:REWRITE DEFAULT-+-2))
               (3377 779
                     (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
               (2316 2316 (:REWRITE DEFAULT-+-1))
               (2280 456 (:REWRITE EQUAL-CONSTANT-+))
               (2131 2131
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (1524 964
                     (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
               (1376 1376
                     (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
               (1224 508 (:REWRITE O-INFP->NEQ-0))
               (964 964 (:META CANCEL_TIMES-EQUAL-CORRECT))
               (964 964 (:META CANCEL_PLUS-EQUAL-CORRECT))
               (641 74 (:DEFINITION ACK-DEFAULT))
               (287 41 (:REWRITE UNICITY-OF-0))
               (178 9 (:REWRITE O<=-O-FINP-DEF))
               (164 41 (:REWRITE DEFUNG::NATP-FIX))
               (156 156 (:TYPE-PRESCRIPTION O-FINP))
               (156 52 (:REWRITE O-FIRST-EXPT-O-INFP))
               (132 60 (:REWRITE O-FIRST-EXPT-DEF-O-FINP))
               (121 49 (:REWRITE DEFAULT-<-2))
               (104 104 (:TYPE-PRESCRIPTION BOOLEANP))
               (98 49 (:REWRITE DEFAULT-<-1))
               (82 82 (:TYPE-PRESCRIPTION NATP))
               (82 41 (:DEFINITION FIX))
               (41 41 (:REWRITE NATP-RW))
               (36 9 (:REWRITE AC-<))
               (36 4 (:REWRITE O-FIRST-EXPT-<))
               (32 32
                   (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
               (20 4 (:REWRITE O-FIRST-COEFF-<))
               (17 9 (:REWRITE O-INFP-O-FINP-O<=))
               (9 9
                  (:REWRITE |a < b & b < c  =>  a < c|)))
(ACK-INDUCTION-REDUCTION
     (591 15 (:DEFINITION ACK-DEFINITION))
     (217 123 (:REWRITE DEFAULT-+-2))
     (123 123 (:REWRITE DEFAULT-+-1))
     (122 31
          (:REWRITE DEFUNG::COMBINE-AND-EVALUATE-CONSTANTS))
     (120 24 (:REWRITE EQUAL-CONSTANT-+))
     (118 118
          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (114 35 (:REWRITE O-INFP->NEQ-0))
     (72 72
         (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
     (59 59 (:META CANCEL_TIMES-EQUAL-CORRECT))
     (59 59 (:META CANCEL_PLUS-EQUAL-CORRECT))
     (33 33 (:TYPE-PRESCRIPTION O-FINP))
     (33 11 (:REWRITE O-FIRST-EXPT-O-INFP))
     (27 27
         (:TYPE-PRESCRIPTION DEFUNG::TRUE-FROM-X))
     (22 22 (:TYPE-PRESCRIPTION BOOLEANP))
     (22 11 (:REWRITE O-FIRST-EXPT-DEF-O-FINP)))
