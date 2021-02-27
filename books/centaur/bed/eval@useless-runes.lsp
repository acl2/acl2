(BED::BED-ENV-LOOKUP)
(BED::BED-ENV-LOOKUP-OF-NIL)
(BED::BED-ENV-LOOKUP-OF-T)
(BED::BED-EVAL (1406 686 (:REWRITE DEFAULT-+-2))
               (934 686 (:REWRITE DEFAULT-+-1))
               (592 74 (:DEFINITION LENGTH))
               (370 74 (:DEFINITION LEN))
               (242 194 (:REWRITE DEFAULT-<-2))
               (220 194 (:REWRITE DEFAULT-<-1))
               (152 152 (:REWRITE DEFAULT-UNARY-MINUS))
               (74 74 (:TYPE-PRESCRIPTION LEN))
               (74 74 (:REWRITE DEFAULT-REALPART))
               (74 74 (:REWRITE DEFAULT-NUMERATOR))
               (74 74 (:REWRITE DEFAULT-IMAGPART))
               (74 74 (:REWRITE DEFAULT-DENOMINATOR))
               (74 74 (:REWRITE DEFAULT-COERCE-2))
               (74 74 (:REWRITE DEFAULT-COERCE-1)))
(BED::BITP-OF-BED-EVAL (16 16 (:REWRITE DEFAULT-CDR))
                       (13 13 (:REWRITE DEFAULT-CAR))
                       (3 1
                          (:REWRITE BED::BED-OP-FIX-WHEN-BED-OP-P))
                       (2 2 (:TYPE-PRESCRIPTION BED::BED-OP-P))
                       (2 2
                          (:REWRITE BED::BED-OP-EVAL-WHEN-FIX-IS-EXACT)))
(BED::BED-EVAL (28 2 (:DEFINITION BED::BED-EVAL))
               (12 12 (:REWRITE DEFAULT-CDR))
               (12 12 (:REWRITE DEFAULT-CAR))
               (9 3
                  (:REWRITE BED::BED-OP-FIX-WHEN-BED-OP-P))
               (6 6 (:TYPE-PRESCRIPTION BED::BED-OP-P))
               (4 4
                  (:REWRITE BED::BED-OP-EVAL-WHEN-FIX-IS-EXACT))
               (4 2
                  (:REWRITE BED::BED-OP-EVAL-OF-BED-OP-FIX)))
(BED::BED-EVAL-MEMOIZE-CONDITION)
(BED::BED-EVAL-MEMOIZE-CONDITION)
(BED::BED-EVAL-WHEN-ATOM)
(BED::BED-EVAL-OF-VAR (23 23 (:REWRITE BED::BED-EVAL-WHEN-ATOM))
                      (21 21 (:REWRITE DEFAULT-CDR))
                      (18 18 (:REWRITE DEFAULT-CAR))
                      (12 4
                          (:REWRITE BED::BED-OP-FIX-WHEN-BED-OP-P))
                      (8 8 (:TYPE-PRESCRIPTION BED::BED-OP-P))
                      (8 8
                         (:REWRITE BED::BED-OP-EVAL-WHEN-FIX-IS-EXACT))
                      (8 4
                         (:REWRITE BED::BED-OP-EVAL-OF-BED-OP-FIX)))
(BED::BED-EVAL-WHEN-KNOWN-OP
     (23 23 (:REWRITE BED::BED-EVAL-WHEN-ATOM))
     (17 17 (:REWRITE DEFAULT-CDR))
     (16 16 (:REWRITE DEFAULT-CAR))
     (15 5
         (:REWRITE BED::BED-OP-FIX-WHEN-BED-OP-P))
     (12 12
         (:REWRITE BED::BED-OP-EVAL-WHEN-FIX-IS-EXACT))
     (10 10 (:TYPE-PRESCRIPTION BED::BED-OP-P))
     (8 8
        (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
     (8 8
        (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
     (8 8
        (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
     (7 5 (:REWRITE BED::BED-EVAL-OF-VAR))
     (4 4
        (:TYPE-PRESCRIPTION BED::BED-ENV-LOOKUP)))
