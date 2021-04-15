(SB::STUPID-P)
(SB::BOOLEANP-OF-STUPID-P)
(SB::STARTING-STATE-P)
(SB::BOOLEANP-OF-STARTING-STATE-P)
(SB::INV-OLD)
(SB::INV)
(SB::STEP-INV (137 5 (:REWRITE SB::SB-LATEST-NO-PENDING-2))
              (74 4
                  (:REWRITE SB::NO-PENDING-WHEN-NOT-CONSP))
              (66 3
                  (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
              (50 11
                  (:REWRITE SB::SB-LATEST-SB-NEXT-FLUSH))
              (42 2
                  (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
              (39 10 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
              (39 10
                  (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
              (19 3
                  (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
              (18 18 (:TYPE-PRESCRIPTION SB::SB-P))
              (18 18 (:REWRITE SB::SB-P-OF-PROC->SB))
              (15 3
                  (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
              (12 2
                  (:REWRITE SB::RETURN-TYPE-OF-SB-LATEST))
              (12 1 (:REWRITE SB::LOOKUP-ADDR-NO-PENDING))
              (9 9 (:TYPE-PRESCRIPTION SB::FLUSH-SB))
              (9 3 (:REWRITE SB::RETURN-TYPE-OF-READ-SB))
              (6 6
                 (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
              (6 6
                 (:REWRITE SB::CONSP-WHEN-NOT-NO-PENDING))
              (6 3 (:REWRITE SB::LEN-CONSP))
              (5 3 (:REWRITE SB::SB-LATEST-NO-PENDING))
              (5 3 (:REWRITE SB::MACHINE-P-OF-FLUSH-SB))
              (2 2 (:TYPE-PRESCRIPTION SB::SB-ELEMENT-P))
              (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-2))
              (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-1)))
(SB::FLUSH-SB-INV (137 5 (:REWRITE SB::SB-LATEST-NO-PENDING-2))
                  (74 4
                      (:REWRITE SB::NO-PENDING-WHEN-NOT-CONSP))
                  (66 3
                      (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
                  (54 54
                      (:TYPE-PRESCRIPTION SB::PROC->SB$INLINE))
                  (50 11
                      (:REWRITE SB::SB-LATEST-SB-NEXT-FLUSH))
                  (42 2
                      (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
                  (39 10 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
                  (39 10
                      (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
                  (19 3
                      (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
                  (18 18 (:TYPE-PRESCRIPTION SB::SB-P))
                  (18 18 (:REWRITE SB::SB-P-OF-PROC->SB))
                  (15 3
                      (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
                  (12 2
                      (:REWRITE SB::RETURN-TYPE-OF-SB-LATEST))
                  (9 3 (:REWRITE SB::RETURN-TYPE-OF-READ-SB))
                  (6 6
                     (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
                  (6 6
                     (:REWRITE SB::CONSP-WHEN-NOT-NO-PENDING))
                  (6 3 (:REWRITE SB::LEN-CONSP))
                  (5 3 (:REWRITE SB::SB-LATEST-NO-PENDING))
                  (5 3 (:REWRITE SB::MACHINE-P-OF-FLUSH-SB))
                  (2 2 (:TYPE-PRESCRIPTION SB::SB-ELEMENT-P))
                  (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-2))
                  (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-1)))
(SB::INV-STARTING-STATE)
(SB::RUN-INV (1125 45 (:DEFINITION LEN))
             (813 129
                  (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
             (698 26 (:REWRITE SB::INV-STARTING-STATE))
             (646 26 (:DEFINITION SB::STARTING-STATE-P))
             (540 540
                  (:TYPE-PRESCRIPTION SB::MACHINE->PROCS$INLINE))
             (444 78 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
             (312 129 (:REWRITE SB::LEN-CONSP))
             (250 26 (:DEFINITION SB::STUPID-P))
             (194 97 (:REWRITE DEFAULT-<-1))
             (170 97 (:REWRITE DEFAULT-<-2))
             (158 158
                  (:TYPE-PRESCRIPTION SB::PROC->PC$INLINE))
             (132 132
                  (:TYPE-PRESCRIPTION SB::PROC->PHASE$INLINE))
             (106 106
                  (:TYPE-PRESCRIPTION SB::PROC->PROGRAM$INLINE))
             (90 45 (:REWRITE DEFAULT-+-2))
             (79 79 (:REWRITE DEFAULT-CDR))
             (45 45 (:REWRITE DEFAULT-+-1))
             (44 11 (:REWRITE SB::SB-P-OF-CDR-WHEN-SB-P))
             (34 2 (:DEFINITION TRUE-LISTP))
             (33 33 (:REWRITE DEFAULT-CAR))
             (26 26
                 (:TYPE-PRESCRIPTION SB::STARTING-STATE-P))
             (24 4
                 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
             (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
             (12 6 (:REWRITE SB::STEP-NUM-PROCS))
             (12 6 (:REWRITE SB::FLUSH-SB-NUM-PROCS))
             (9 3 (:REWRITE SB::NOT-BLOCKED-FLUSH-SB))
             (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
             (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
             (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
             (4 4 (:REWRITE SET::IN-SET))
             (2 2 (:TYPE-PRESCRIPTION SB::STUPID-P)))
(SB::INV-PC-1)
(SB::STUPID-CORRECT (45 1 (:REWRITE SB::READ-SB-NO-PENDING-2))
                    (37 3
                        (:REWRITE SB::PROC-NUM-<-LEN-NUM-PROCS))
                    (25 1 (:DEFINITION LEN))
                    (18 3
                        (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
                    (16 16 (:TYPE-PRESCRIPTION SB::NUM-PROCS))
                    (12 12
                        (:TYPE-PRESCRIPTION SB::MACHINE->PROCS$INLINE))
                    (11 1 (:REWRITE SB::SB-LATEST-NO-PENDING-2))
                    (11 1
                        (:REWRITE SB::NO-PENDING-WHEN-NOT-CONSP))
                    (9 2 (:REWRITE SB::SB-P-WHEN-NOT-CONSP))
                    (8 4 (:REWRITE DEFAULT-<-2))
                    (6 3 (:REWRITE SB::LEN-CONSP))
                    (6 1
                       (:REWRITE SB::ORACLE-P-WHEN-NOT-CONSP))
                    (5 5 (:TYPE-PRESCRIPTION SB::SB-P))
                    (4 4 (:REWRITE DEFAULT-<-1))
                    (3 3 (:TYPE-PRESCRIPTION SB::MACHINE-P))
                    (2 1
                       (:REWRITE SB::PROC-NUM-<-NUM-PROCS-LEN))
                    (2 1 (:REWRITE DEFAULT-+-2))
                    (1 1 (:REWRITE DEFAULT-CDR))
                    (1 1 (:REWRITE DEFAULT-+-1)))
