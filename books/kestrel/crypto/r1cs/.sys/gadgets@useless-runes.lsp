(R1CS::BITP-IN-FIELD
 (2 2 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 )
(R1CS::NONZERO-CONSTRAINT)
(R1CS::NONZERO-CONSTRAINT-SUFF)
(R1CS::NONZERO-CONSTRAINT-CORRECT-1
 (9 1 (:REWRITE R1CS::BITP-IN-FIELD))
 (7 1 (:DEFINITION BITP))
 (5 1 (:REWRITE PFIELD::FEP-HOLDS))
 (3 1 (:DEFINITION NATP))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (2 2 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE R1CS::NONZERO-CONSTRAINT-SUFF))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (1 1 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (1 1 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(R1CS::NONZERO-CONSTRAINT-CORRECT-2
 (79 4 (:REWRITE R1CS::BITP-IN-FIELD))
 (71 3 (:DEFINITION BITP))
 (45 2 (:REWRITE PFIELD::EQUAL-OF-INV))
 (11 11 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (11 11 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2B))
 (11 11 (:REWRITE PFIELD::EQUAL-OF-ADD-MOVE-NEGATIONS-BIND-FREE-2A))
 (11 11 (:REWRITE PFIELD::EQUAL-OF-ADD-CANCEL-BIND-FREE))
 (11 1 (:REWRITE PFIELD::MUL-OF-1-ARG1-GEN))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (10 10 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (8 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (6 2 (:DEFINITION NATP))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 3 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (3 3 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-WHEN-<-OF-0))
 (2 2 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (2 2 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE POS-FIX-WHEN-POSP))
 (1 1 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (1 1 (:REWRITE R1CS::NONZERO-CONSTRAINT-CORRECT-1))
 (1 1 (:REWRITE PFIELD::MUL-OF-0-ARG1))
 )
(R1CS::NONZERO-CONSTRAINT-CORRECT)
