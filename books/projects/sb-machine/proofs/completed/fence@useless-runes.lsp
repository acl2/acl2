(SB::FENCE-P)
(SB::BOOLEANP-OF-FENCE-P)
(SB::STARTING-STATE-P)
(SB::BOOLEANP-OF-STARTING-STATE-P)
(SB::INV)
(SB::STEP-INV (743 20
                   (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
              (467 101
                   (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
              (302 14
                   (:REWRITE SB::NO-PENDING-WHEN-NOT-CONSP))
              (287 101 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
              (213 105
                   (:REWRITE SB::SB-LATEST-SB-NEXT-FLUSH))
              (129 6
                   (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
              (111 111 (:TYPE-PRESCRIPTION SB::SB-P))
              (111 111 (:REWRITE SB::SB-P-OF-PROC->SB))
              (63 8
                  (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
              (44 20 (:REWRITE SB::LEN-CONSP))
              (36 8
                  (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
              (34 6
                  (:REWRITE SB::RETURN-TYPE-OF-SB-LATEST))
              (27 2 (:REWRITE SB::LOOKUP-ADDR-NO-PENDING))
              (19 10 (:REWRITE SB::SB-LATEST-NO-PENDING))
              (19 7 (:REWRITE SB::RETURN-TYPE-OF-READ-SB))
              (16 16
                  (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
              (9 9 (:TYPE-PRESCRIPTION SB::FLUSH-SB))
              (6 6 (:TYPE-PRESCRIPTION SB::SB-ELEMENT-P))
              (5 3 (:REWRITE SB::MACHINE-P-OF-FLUSH-SB))
              (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-2))
              (1 1 (:REWRITE SB::NO-PENDING-FLUSH-SB-1)))
(SB::FLUSH-SB-INV (210 7
                       (:REWRITE SB::SB-LATEST-IMPLIES-NOT-EMPTY))
                  (201 8 (:REWRITE SB::SB-LATEST-NO-PENDING-2))
                  (141 6
                       (:REWRITE SB::NO-PENDING-WHEN-NOT-CONSP))
                  (123 123
                       (:TYPE-PRESCRIPTION SB::PROC->SB$INLINE))
                  (105 27
                       (:REWRITE SB::NO-PENDING-SB-SB-NEXT-DEQ))
                  (96 27 (:REWRITE SB::SB-LATEST-SB-DEQ-3))
                  (86 29
                      (:REWRITE SB::SB-LATEST-SB-NEXT-FLUSH))
                  (83 1
                      (:REWRITE SB::LOOKUP-ADDR-MEM-FLUSH-SB-PENDING))
                  (68 3
                      (:REWRITE SB::NO-PENDING-SB-SB-LATEST))
                  (40 40 (:TYPE-PRESCRIPTION SB::SB-P))
                  (40 40 (:REWRITE SB::SB-P-OF-PROC->SB))
                  (33 4
                      (:REWRITE SB::NO-PENDING-SB-NOT-CONSP))
                  (20 4
                      (:REWRITE SB::NO-PENDING-SB-SB-LATEST-2))
                  (18 3
                      (:REWRITE SB::RETURN-TYPE-OF-SB-LATEST))
                  (16 7 (:REWRITE SB::LEN-CONSP))
                  (12 4 (:REWRITE SB::RETURN-TYPE-OF-READ-SB))
                  (10 10
                      (:REWRITE SB::CONSP-WHEN-NOT-NO-PENDING))
                  (9 5 (:REWRITE SB::SB-LATEST-NO-PENDING))
                  (8 8
                     (:TYPE-PRESCRIPTION SB::NO-PENDING-SB))
                  (5 3 (:REWRITE SB::MACHINE-P-OF-FLUSH-SB))
                  (3 3 (:TYPE-PRESCRIPTION SB::SB-ELEMENT-P))
                  (2 2 (:REWRITE SB::NO-PENDING-FLUSH-SB-2)))
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
             (250 26 (:DEFINITION SB::FENCE-P))
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
             (2 2 (:TYPE-PRESCRIPTION SB::FENCE-P)))
(SB::INV-PC-1)
(SB::FENCE-CORRECT)
