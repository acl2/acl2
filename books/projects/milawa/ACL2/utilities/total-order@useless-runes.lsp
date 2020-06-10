(MILAWA::<< (14 6 (:REWRITE MILAWA::NATP-WHEN-ZP-CHEAP))
            (14 6
                (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP))
            (12 2
                (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
            (12 2
                (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
            (10 6
                (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
            (10 4
                (:REWRITE MILAWA::RANK-WHEN-NOT-CONSP))
            (8 8
               (:REWRITE MILAWA::ZP-WHEN-NOT-NATP-CHEAP))
            (8 8 (:REWRITE MILAWA::ZP-WHEN-NATP-CHEAP))
            (5 5 (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
            (4 4 (:REWRITE MILAWA::TRICHOTOMY-OF-<))
            (4 4
               (:REWRITE MILAWA::TRANSITIVITY-OF-<-TWO))
            (4 4
               (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
            (4 4 (:REWRITE MILAWA::TRANSITIVITY-OF-<))
            (4 4
               (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
            (4 4
               (:REWRITE MILAWA::LESS-WHEN-ZP-LEFT-CHEAP))
            (2 2
               (:REWRITE MILAWA::EQUAL-OF-BOOLEANS-REWRITE))
            (1 1
               (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP)))
(MILAWA::BOOLEANP-OF-ACL2-LEXORDER
     (13 2 (:REWRITE <<-IMPLIES-LEXORDER))
     (8 2 (:REWRITE <<-TRICHOTOMY))
     (6 6 (:TYPE-PRESCRIPTION <<))
     (3 1
        (:REWRITE MILAWA::BOOLEANP-WHEN-NATP-CHEAP))
     (2 2 (:REWRITE LEXORDER-TRANSITIVE))
     (2 2 (:REWRITE <<-TRANSITIVE))
     (2 1
        (:REWRITE MILAWA::BOOLEANP-WHEN-CONSP-CHEAP))
     (2 1 (:REWRITE <<-ASYMMETRIC))
     (1 1 (:REWRITE MILAWA::NATP-WHEN-ZP-CHEAP))
     (1 1
        (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP)))
(MILAWA::BOOLEANP-OF-<< (411 108 (:REWRITE MILAWA::TRICHOTOMY-OF-<))
                        (357 63
                             (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
                        (315 63
                             (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
                        (208 8 (:REWRITE MILAWA::ANTISYMMETRY-OF-<))
                        (163 60
                             (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP))
                        (114 10 (:REWRITE <<-IMPLIES-LEXORDER))
                        (108 108
                             (:REWRITE MILAWA::TRANSITIVITY-OF-<-TWO))
                        (108 108
                             (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
                        (108 108
                             (:REWRITE MILAWA::TRANSITIVITY-OF-<))
                        (96 30
                            (:REWRITE MILAWA::TRICHOTOMY-OF-SYMBOL-<))
                        (90 18
                            (:REWRITE MILAWA::ANTISYMMETRY-OF-SYMBOL-<))
                        (74 19 (:REWRITE <<-TRICHOTOMY))
                        (70 28
                            (:REWRITE MILAWA::NFIX-WHEN-ZP-CHEAP))
                        (68 22 (:REWRITE MILAWA::LESS-OF-ZERO-LEFT))
                        (56 56 (:TYPE-PRESCRIPTION <<))
                        (51 51
                            (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
                        (48 16
                            (:REWRITE MILAWA::BOOLEANP-WHEN-NATP-CHEAP))
                        (39 39
                            (:REWRITE MILAWA::SYMBOLP-WHEN-NATP-CHEAP))
                        (30 30
                            (:REWRITE MILAWA::TRANSITIVITY-OF-SYMBOL-<))
                        (30 30
                            (:REWRITE MILAWA::SYMBOL-<-COMPLETION-RIGHT))
                        (30 30
                            (:REWRITE MILAWA::SYMBOL-<-COMPLETION-LEFT))
                        (28 28
                            (:REWRITE MILAWA::NFIX-WHEN-NOT-NATP-CHEAP))
                        (28 28
                            (:REWRITE MILAWA::NFIX-WHEN-NATP-CHEAP))
                        (28 28
                            (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
                        (27 27
                            (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
                        (25 25
                            (:REWRITE MILAWA::LESS-OF-ZERO-RIGHT))
                        (19 19 (:REWRITE <<-TRANSITIVE))
                        (18 9 (:REWRITE <<-ASYMMETRIC))
                        (16 16
                            (:REWRITE MILAWA::BOOLEANP-WHEN-CONSP-CHEAP))
                        (10 10
                            (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP))
                        (8 8
                           (:REWRITE MILAWA::TRANSITIVITY-OF-<-FOUR))
                        (1 1 (:REWRITE <<-IRREFLEXIVE)))
(MILAWA::IRREFLEXIVITY-OF-<<
     (76 41
         (:REWRITE MILAWA::ZP-WHEN-NATP-CHEAP))
     (55 14
         (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP))
     (53 11
         (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
     (52 22
         (:REWRITE MILAWA::LESS-WHEN-ZP-LEFT-CHEAP))
     (50 5 (:REWRITE MILAWA::ANTISYMMETRY-OF-<))
     (47 11
         (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
     (31 31
         (:REWRITE MILAWA::EQUAL-OF-BOOLEANS-REWRITE))
     (30 5 (:REWRITE <<-IMPLIES-LEXORDER))
     (22 22 (:REWRITE MILAWA::TRICHOTOMY-OF-<))
     (22 22
         (:REWRITE MILAWA::TRANSITIVITY-OF-<-TWO))
     (22 22
         (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
     (22 22 (:REWRITE MILAWA::TRANSITIVITY-OF-<))
     (21 21
         (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
     (20 5
         (:REWRITE MILAWA::LESS-WHEN-ZP-RIGHT-CHEAP))
     (18 18
         (:REWRITE MILAWA::SYMBOLP-WHEN-NATP-CHEAP))
     (12 6 (:REWRITE MILAWA::LESS-OF-ZERO-LEFT))
     (10 10 (:TYPE-PRESCRIPTION <<))
     (10 10
         (:REWRITE MILAWA::SYMBOL-<-COMPLETION-RIGHT))
     (10 10
         (:REWRITE MILAWA::SYMBOL-<-COMPLETION-LEFT))
     (10 10
         (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
     (10 5 (:REWRITE <<-TRICHOTOMY))
     (8 8 (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP))
     (6 6 (:REWRITE MILAWA::LESS-OF-ZERO-RIGHT))
     (6 6
        (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
     (5 5
        (:REWRITE MILAWA::TRANSITIVITY-OF-SYMBOL-<))
     (5 5
        (:REWRITE MILAWA::TRANSITIVITY-OF-<-FOUR))
     (5 5 (:REWRITE LEXORDER-TRANSITIVE))
     (5 5 (:REWRITE <<-TRANSITIVE))
     (5 5 (:REWRITE <<-IRREFLEXIVE)))
(MILAWA::ASYMMETRY-OF-<< (670 169 (:REWRITE MILAWA::TRICHOTOMY-OF-<))
                         (528 94
                              (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
                         (471 94
                              (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
                         (222 66
                              (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP))
                         (204 18 (:REWRITE <<-IMPLIES-LEXORDER))
                         (177 56
                              (:REWRITE MILAWA::TRICHOTOMY-OF-SYMBOL-<))
                         (169 169
                              (:REWRITE MILAWA::TRANSITIVITY-OF-<-TWO))
                         (169 169
                              (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
                         (168 168
                              (:REWRITE MILAWA::TRANSITIVITY-OF-<))
                         (162 162
                              (:REWRITE MILAWA::EQUAL-OF-BOOLEANS-REWRITE))
                         (132 34 (:REWRITE <<-TRICHOTOMY))
                         (128 50
                              (:REWRITE MILAWA::NFIX-WHEN-ZP-CHEAP))
                         (100 100 (:TYPE-PRESCRIPTION <<))
                         (88 88
                             (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
                         (78 27 (:REWRITE MILAWA::LESS-OF-ZERO-LEFT))
                         (63 63
                             (:REWRITE MILAWA::SYMBOLP-WHEN-NATP-CHEAP))
                         (60 60
                             (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
                         (56 56
                             (:REWRITE MILAWA::TRANSITIVITY-OF-SYMBOL-<))
                         (56 56
                             (:REWRITE MILAWA::SYMBOL-<-COMPLETION-RIGHT))
                         (56 56
                             (:REWRITE MILAWA::SYMBOL-<-COMPLETION-LEFT))
                         (50 50
                             (:REWRITE MILAWA::NFIX-WHEN-NOT-NATP-CHEAP))
                         (50 50
                             (:REWRITE MILAWA::NFIX-WHEN-NATP-CHEAP))
                         (46 46
                             (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
                         (34 34 (:REWRITE <<-TRANSITIVE))
                         (32 16 (:REWRITE <<-ASYMMETRIC))
                         (30 30
                             (:REWRITE MILAWA::LESS-OF-ZERO-RIGHT))
                         (20 20
                             (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP))
                         (14 14
                             (:REWRITE MILAWA::TRANSITIVITY-OF-<-FOUR))
                         (2 2 (:REWRITE <<-IRREFLEXIVE)))
(MILAWA::TRANSITIVITY-OF-<<
     (3909 965 (:REWRITE MILAWA::TRICHOTOMY-OF-<))
     (3069 575
           (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
     (2911 577
           (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
     (1053 297
           (:REWRITE MILAWA::NATP-WHEN-NOT-ZP-CHEAP))
     (1027 98 (:REWRITE <<-IMPLIES-LEXORDER))
     (967 967
          (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
     (963 963
          (:REWRITE MILAWA::TRANSITIVITY-OF-<))
     (682 256
          (:REWRITE MILAWA::NFIX-WHEN-ZP-CHEAP))
     (674 177
          (:REWRITE MILAWA::LESS-OF-ZERO-LEFT))
     (674 169 (:REWRITE <<-TRICHOTOMY))
     (506 506 (:TYPE-PRESCRIPTION <<))
     (479 479
          (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
     (454 454
          (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
     (331 331
          (:REWRITE MILAWA::SYMBOLP-WHEN-NATP-CHEAP))
     (256 256
          (:REWRITE MILAWA::SYMBOL-<-COMPLETION-RIGHT))
     (256 256
          (:REWRITE MILAWA::SYMBOL-<-COMPLETION-LEFT))
     (256 256
          (:REWRITE MILAWA::NFIX-WHEN-NOT-NATP-CHEAP))
     (256 256
          (:REWRITE MILAWA::NFIX-WHEN-NATP-CHEAP))
     (194 194
          (:REWRITE MILAWA::LESS-OF-ZERO-RIGHT))
     (188 188
          (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
     (169 169 (:REWRITE <<-TRANSITIVE))
     (168 84 (:REWRITE <<-ASYMMETRIC))
     (146 146
          (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP))
     (58 58
         (:REWRITE MILAWA::TRANSITIVITY-OF-<-FOUR))
     (1 1 (:REWRITE LEXORDER-REFLEXIVE))
     (1 1 (:REWRITE <<-IRREFLEXIVE)))
(MILAWA::FORCING-TRICHOTOMY-OF-<<
     (464 80
          (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS-TWO))
     (457 56 (:REWRITE MILAWA::ASYMMETRY-OF-<<))
     (437 80
          (:REWRITE MILAWA::NOT-EQUAL-WHEN-LESS))
     (228 31 (:REWRITE <<-IMPLIES-LEXORDER))
     (222 206
          (:REWRITE MILAWA::TRANSITIVITY-OF-<-THREE))
     (206 206
          (:REWRITE MILAWA::TRANSITIVITY-OF-<-TWO))
     (200 200
          (:REWRITE MILAWA::TRANSITIVITY-OF-<))
     (195 107
          (:REWRITE MILAWA::NFIX-WHEN-ZP-CHEAP))
     (170 34
          (:REWRITE MILAWA::ANTISYMMETRY-OF-SYMBOL-<))
     (140 36 (:REWRITE <<-TRICHOTOMY))
     (109 109
          (:REWRITE MILAWA::SYMBOLP-WHEN-BOOLEANP-CHEAP))
     (107 107
          (:REWRITE MILAWA::NFIX-WHEN-NOT-NATP-CHEAP))
     (106 106 (:TYPE-PRESCRIPTION <<))
     (90 90
         (:REWRITE MILAWA::TRANSITIVITY-OF-<<))
     (89 89
         (:REWRITE MILAWA::CAR-WHEN-NOT-CONSP))
     (71 71
         (:REWRITE MILAWA::SYMBOLP-WHEN-NATP-CHEAP))
     (61 61
         (:REWRITE MILAWA::SYMBOL-<-COMPLETION-RIGHT))
     (61 61
         (:REWRITE MILAWA::SYMBOL-<-COMPLETION-LEFT))
     (60 60
         (:REWRITE MILAWA::CONSP-WHEN-NATP-CHEAP))
     (59 59
         (:REWRITE MILAWA::TRANSITIVITY-OF-SYMBOL-<))
     (44 22 (:REWRITE MILAWA::LESS-OF-ZERO-LEFT))
     (41 41
         (:REWRITE MILAWA::TRANSITIVITY-OF-<-FOUR))
     (41 41
         (:REWRITE MILAWA::CDR-WHEN-NOT-CONSP))
     (36 36 (:REWRITE <<-TRANSITIVE))
     (34 17 (:REWRITE <<-ASYMMETRIC))
     (23 23
         (:REWRITE MILAWA::LESS-OF-ZERO-RIGHT))
     (2 2 (:REWRITE MILAWA::IRREFLEXIVITY-OF-<))
     (2 2 (:REWRITE <<-IRREFLEXIVE)))
