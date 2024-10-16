(ALEOBFT-DYNAMIC::VALIDATOR-COMMITTEES-IN-SYSTEM-P)
(ALEOBFT-DYNAMIC::VALIDATOR-COMMITTEES-IN-SYSTEM-P-NECC)
(ALEOBFT-DYNAMIC::BOOLEANP-OF-VALIDATOR-COMMITTEES-IN-SYSTEM-P)
(ALEOBFT-DYNAMIC::VALIDATOR-COMMITTEES-IN-SYSTEM-P
 (6 2 (:REWRITE SETP-WHEN-POS-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-MESSAGE-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-CERTIFICATE-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-ADDRESS+POS-SETP))
 (4 4 (:TYPE-PRESCRIPTION POS-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::MESSAGE-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS+POS-SETP))
 (2 2 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::COMMITTEES-IN-SYSTEM-P)
(ALEOBFT-DYNAMIC::COMMITTEES-IN-SYSTEM-P-NECC)
(ALEOBFT-DYNAMIC::BOOLEANP-OF-COMMITTEES-IN-SYSTEM-P)
(ALEOBFT-DYNAMIC::COMMITTEES-IN-SYSTEM-P
 (10 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (9 3 (:REWRITE SET::IN-TAIL))
 (8 1 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SETP-WHEN-POS-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-MESSAGE-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-CERTIFICATE-SETP))
 (3 1 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-ADDRESS+POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION POS-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::MESSAGE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-SETP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS+POS-SETP))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (1 1 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESSP))
 )
(ALEOBFT-DYNAMIC::COMMITTEES-IN-SYSTEM-P-WHEN-GENESIS
 (8 2 (:REWRITE SET::IN-TAIL))
 (7 7 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (3 1 (:REWRITE SET::EMPTYP-SUBSET-2))
 (3 1 (:REWRITE SET::EMPTYP-SUBSET))
 (1 1 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (1 1 (:REWRITE ALEOBFT-DYNAMIC::NOT-EMPTYP-OF-COMMITTEE-MEMBERS))
 )
(ALEOBFT-DYNAMIC::GENESIS-COMMITTEE-MEMBERS-SUBSET-WHEN-INIT)
(ALEOBFT-DYNAMIC::GENESIS-COMMITTEE-MEMBERS-SUBSET-OF-NEXT
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET-2))
 (6 2 (:REWRITE SET::EMPTYP-SUBSET))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (2 2 (:REWRITE ALEOBFT-DYNAMIC::NOT-EMPTYP-OF-COMMITTEE-MEMBERS))
 )
