(SV::SVTV-DATA-COMPUTE-PHASE-FSM
 (10 10 (:REWRITE-QUOTED-CONSTANT SV::SVTV-DATA$C-FIELD-FIX-UNDER-SVTV-DATA$C-FIELD-EQUIV))
 (1 1 (:REWRITE SV::SVTV-DATA$C->FLATNORM-VALIDP-OF-UPDATE))
 )
(SV::SVTV-DATA$C-GET-OF-SVTV-DATA-COMPUTE-PHASE-FSM
 (6 2 (:REWRITE SV::SVTV-DATA$C-FIELD-FIX-IDEMPOTENT))
 (4 4 (:TYPE-PRESCRIPTION SV::SVTV-DATA$C-FIELD-P))
 (1 1 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-SETUP-OF-UPDATE))
 (1 1 (:REWRITE SV::SVTV-DATA$C->FLATNORM-OF-UPDATE))
 )
(SV::PHASE-FSM-VALIDP-OF-SVTV-DATA-COMPUTE-PHASE-FSM
 (1 1 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-SETUP-OF-UPDATE))
 (1 1 (:REWRITE SV::SVTV-DATA$C->FLATNORM-OF-UPDATE))
 )
(SV::SVTV-DATA-MAYBE-COMPUTE-PHASE-FSM
 (10 10 (:REWRITE-QUOTED-CONSTANT SV::SVTV-DATA$C-FIELD-FIX-UNDER-SVTV-DATA$C-FIELD-EQUIV))
 (3 2 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-VALIDP-OF-UPDATE))
 (1 1 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-SETUP-OF-UPDATE))
 )
(SV::SVTV-DATA$C-GET-OF-SVTV-DATA-MAYBE-COMPUTE-PHASE-FSM
 (57 19 (:REWRITE SV::SVTV-DATA$C-FIELD-FIX-IDEMPOTENT))
 (38 38 (:TYPE-PRESCRIPTION SV::SVTV-DATA$C-FIELD-P))
 (20 10 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-CAR))
 (15 5 (:REWRITE SV::PHASE-FSM-CONFIG-FIX-WHEN-PHASE-FSM-CONFIG-P))
 (10 10 (:TYPE-PRESCRIPTION SV::PHASE-FSM-CONFIG-P))
 (5 5 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-VALIDP-OF-UPDATE))
 (5 5 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-SETUP-OF-UPDATE))
 )
(SV::PHASE-FSM-SETUP-OF-SVTV-DATA-MAYBE-COMPUTE-PHASE-FSM
 (17 7 (:REWRITE SV::PHASE-FSM-CONFIG-FIX-WHEN-PHASE-FSM-CONFIG-P))
 (12 6 (:REWRITE DEFAULT-CDR))
 (12 6 (:REWRITE DEFAULT-CAR))
 (10 10 (:TYPE-PRESCRIPTION SV::PHASE-FSM-CONFIG-P))
 (6 4 (:REWRITE SV::UPDATE-SVTV-DATA$C->PHASE-FSM-SETUP-PRESERVES-OTHERS))
 (4 4 (:REWRITE-QUOTED-CONSTANT SV::SVTV-DATA$C-FIELD-FIX-UNDER-SVTV-DATA$C-FIELD-EQUIV))
 (2 2 (:TYPE-PRESCRIPTION SV::SVTV-DATA$C-FIELD-FIX$INLINE))
 (2 2 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-VALIDP-OF-UPDATE))
 )
(SV::PHASE-FSM-VALIDP-OF-SVTV-DATA-MAYBE-COMPUTE-PHASE-FSM
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 1 (:REWRITE SV::PHASE-FSM-CONFIG-FIX-WHEN-PHASE-FSM-CONFIG-P))
 (2 2 (:TYPE-PRESCRIPTION SV::PHASE-FSM-CONFIG-P))
 (2 2 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-VALIDP-OF-UPDATE))
 (1 1 (:REWRITE SV::SVTV-DATA$C->PHASE-FSM-SETUP-OF-UPDATE))
 )
