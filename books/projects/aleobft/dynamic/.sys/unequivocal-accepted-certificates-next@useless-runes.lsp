(ALEOBFT-DYNAMIC::CREATE-CERTIFICATE-LEMMA
 (2926 786 (:REWRITE SET::IN-TAIL))
 (1879 1879 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1342 244 (:LINEAR SET::PROPER-SUBSET-CARDINALITY))
 (1098 122 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-FIX-WHEN-CERTIFICATEP))
 (1027 351 (:REWRITE SET::NEVER-IN-EMPTY))
 (1019 343 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (610 122 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-CERTIFICATE-OPTIONP))
 (528 176 (:REWRITE SET::EMPTYP-SUBSET))
 (526 176 (:REWRITE SET::EMPTYP-SUBSET-2))
 (366 366 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATEP))
 (244 244 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP))
 (244 122 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP-WHEN-CERTIFICATEP))
 (176 176 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (175 175 (:REWRITE ALEOBFT-DYNAMIC::NOT-EMPTYP-OF-COMMITTEE-MEMBERS))
 (122 122 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-IN-CERTIFICATE-SETP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-CREATE-CERTIFICATE-NEXT
 (774 201 (:REWRITE SET::IN-TAIL))
 (402 402 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (279 93 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (279 93 (:REWRITE SET::NEVER-IN-EMPTY))
 (135 15 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-FIX-WHEN-CERTIFICATEP))
 (75 15 (:REWRITE SET::INSERT-IDENTITY))
 (75 15 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-CERTIFICATE-OPTIONP))
 (45 45 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATEP))
 (45 15 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (30 30 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP))
 (30 15 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATE-OPTIONP-WHEN-CERTIFICATEP))
 (30 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (15 15 (:REWRITE ALEOBFT-DYNAMIC::CERTIFICATEP-WHEN-IN-CERTIFICATE-SETP-BINDS-FREE-X))
 (12 12 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (12 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (6 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::RECEIVE-CERTIFICATE-LEMMA
 (1936 538 (:REWRITE SET::IN-TAIL))
 (714 112 (:LINEAR SET::PROPER-SUBSET-CARDINALITY))
 (663 233 (:REWRITE SET::NEVER-IN-EMPTY))
 (651 221 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (313 105 (:REWRITE SET::EMPTYP-SUBSET-2))
 (287 105 (:REWRITE SET::EMPTYP-SUBSET))
 (128 32 (:REWRITE ALEOBFT-DYNAMIC::MESSAGE-FIX-WHEN-MESSAGEP))
 (105 105 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (90 90 (:REWRITE ALEOBFT-DYNAMIC::NOT-EMPTYP-OF-COMMITTEE-MEMBERS))
 (64 64 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::MESSAGEP))
 (32 32 (:REWRITE ALEOBFT-DYNAMIC::MESSAGEP-WHEN-IN-MESSAGE-SETP-BINDS-FREE-X))
 (12 12 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (11 11 (:REWRITE-QUOTED-CONSTANT POS-FIX-UNDER-POS-EQUIV))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-RECEIVE-CERTIFICATE-NEXT
 (774 201 (:REWRITE SET::IN-TAIL))
 (402 402 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (279 93 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (279 93 (:REWRITE SET::NEVER-IN-EMPTY))
 (75 15 (:REWRITE SET::INSERT-IDENTITY))
 (45 15 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (30 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (12 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (6 6 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-STORE-CERTIFICATE-NEXT
 (184 46 (:REWRITE SET::IN-TAIL))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (69 23 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (69 23 (:REWRITE SET::NEVER-IN-EMPTY))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-ADVANCE-ROUND-NEXT
 (184 46 (:REWRITE SET::IN-TAIL))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (69 23 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (69 23 (:REWRITE SET::NEVER-IN-EMPTY))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-COMMIT-ANCHORS-NEXT
 (184 46 (:REWRITE SET::IN-TAIL))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (69 23 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (69 23 (:REWRITE SET::NEVER-IN-EMPTY))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-TIMER-EXPIRES-NEXT
 (184 46 (:REWRITE SET::IN-TAIL))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (69 23 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (69 23 (:REWRITE SET::NEVER-IN-EMPTY))
 )
(ALEOBFT-DYNAMIC::UNEQUIVOCAL-ACCEPTED-CERTIFICATES-P-OF-EVENT-NEXT)
