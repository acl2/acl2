(ALEOBFT-DYNAMIC::SAME-COMMITTEES-P)
(ALEOBFT-DYNAMIC::SAME-COMMITTEES-P-NECC
 (12 12 (:DEFINITION MV-NTH))
 )
(ALEOBFT-DYNAMIC::BOOLEANP-OF-SAME-COMMITTEES-P)
(ALEOBFT-DYNAMIC::SAME-COMMITTEES-P
 (70 22 (:REWRITE SET::IN-TAIL))
 (32 32 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (30 14 (:REWRITE SET::NEVER-IN-EMPTY))
 (24 8 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (20 4 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-ADDRESS-OPTIONP))
 (16 2 (:REWRITE ALEOBFT-DYNAMIC::ADDRESS-OPTIONP-WHEN-ADDRESSP))
 (6 2 (:REWRITE SETP-WHEN-POS-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-MESSAGE-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-CERTIFICATE-SETP))
 (6 2 (:REWRITE ALEOBFT-DYNAMIC::SETP-WHEN-ADDRESS+POS-SETP))
 (5 5 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (4 4 (:TYPE-PRESCRIPTION POS-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::MESSAGE-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::CERTIFICATE-SETP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESS+POS-SETP))
 (4 4 (:REWRITE ALEOBFT-DYNAMIC::ADDRESSP-WHEN-IN-VALIDATORS-STATEP-BINDS-FREE-X))
 (2 2 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::ADDRESSP))
 )
(ALEOBFT-DYNAMIC::SAME-COMMITTEES-LIST-EXTENSION-EQUIVALENCES
 (431 41 (:REWRITE TAKE-OF-LEN-FREE))
 (313 313 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (313 313 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (81 41 (:REWRITE TAKE-WHEN-ATOM))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND
 (8 4 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (3 3 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (1 1 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::BLOCK-LISTP-OF-TRIM-BLOCKS-FOR-ROUND
 (61 11 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (32 8 (:REWRITE POS-FIX-WHEN-POSP))
 (16 16 (:TYPE-PRESCRIPTION POSP))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (8 8 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (4 1 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-OF-POS-FIX-ROUND
 (16 3 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (12 12 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (4 1 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-OF-CDR-WHEN-BLOCK-LISTP))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-POS-EQUIV-CONGRUENCE-ON-ROUND)
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-OF-BLOCK-LIST-FIX-BLOCKS
 (255 66 (:REWRITE POS-FIX-WHEN-POSP))
 (176 34 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-OF-CDR-WHEN-BLOCK-LISTP))
 (126 126 (:TYPE-PRESCRIPTION POSP))
 (94 84 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (63 63 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (61 61 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (61 61 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (3 3 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-UNDER-IFF))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-BLOCK-LIST-EQUIV-CONGRUENCE-ON-BLOCKS)
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-NO-CHANGE
 (11 3 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (8 2 (:REWRITE POS-FIX-WHEN-POSP))
 (5 5 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCK-LISTP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (1 1 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-OF-APPEND-YIELDS-FIRST
 (151 34 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (67 67 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (67 67 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (58 34 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (18 6 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-FIX-WHEN-BLOCKP))
 (12 12 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCKP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE ALEOBFT-DYNAMIC::CONSP-OF-BLOCK-LIST-FIX))
 )
(ALEOBFT-DYNAMIC::BONDED-COMMITTEE-AT-ROUND-LOOP-TO-TRIM-BLOCKS-FOR-ROUND
 (70 19 (:REWRITE POS-FIX-WHEN-POSP))
 (34 34 (:TYPE-PRESCRIPTION POSP))
 (17 17 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (1 1 (:REWRITE-QUOTED-CONSTANT ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-UNDER-BLOCK-LIST-EQUIV))
 )
(ALEOBFT-DYNAMIC::BONDED-COMMITTEE-AT-ROUND-TO-TRIM-BLOCKS-FOR-ROUND)
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-OF-LONGER
 (83 13 (:REWRITE TAKE-OF-LEN-FREE))
 (64 64 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (63 13 (:REWRITE TAKE-OF-TOO-MANY))
 (42 4 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (37 37 (:TYPE-PRESCRIPTION NFIX))
 (33 13 (:REWRITE TAKE-WHEN-ATOM))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (21 4 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (19 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (8 8 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCK-LISTP))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ALEOBFT-DYNAMIC::TRIM-BLOCKS-FOR-ROUND-OF-SHORTER
 (162 22 (:REWRITE TAKE-OF-LEN-FREE))
 (122 22 (:REWRITE TAKE-OF-TOO-MANY))
 (74 74 (:TYPE-PRESCRIPTION NFIX))
 (52 22 (:REWRITE TAKE-WHEN-ATOM))
 (35 35 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (35 35 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (27 6 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (25 3 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCK-LISTP))
 (10 6 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 )
(ALEOBFT-DYNAMIC::LEMMA
 (101 13 (:REWRITE TAKE-OF-LEN-FREE))
 (92 92 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (68 13 (:REWRITE TAKE-OF-TOO-MANY))
 (60 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (44 44 (:TYPE-PRESCRIPTION NFIX))
 (35 13 (:REWRITE TAKE-WHEN-ATOM))
 (27 3 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (22 22 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (22 22 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ALEOBFT-DYNAMIC::SAME-BONDED-COMMITTEES-LONGER-SHORTER
 (288 288 (:TYPE-PRESCRIPTION POSP))
 (260 56 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LIST-FIX-WHEN-BLOCK-LISTP))
 (144 144 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 (104 104 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCK-LISTP))
 (100 56 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-LISTP-WHEN-NOT-CONSP))
 (98 98 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (98 98 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (36 12 (:REWRITE ALEOBFT-DYNAMIC::BLOCK-FIX-WHEN-BLOCKP))
 (24 24 (:TYPE-PRESCRIPTION ALEOBFT-DYNAMIC::BLOCKP))
 )
(ALEOBFT-DYNAMIC::SAME-ACTIVE-COMMITTEES-LONGER-SHORTER
 (29 11 (:REWRITE POS-FIX-WHEN-POSP))
 (12 12 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 )
(ALEOBFT-DYNAMIC::SAME-ACTIVE-COMMITTEES-WHEN-NOFORK)
(ALEOBFT-DYNAMIC::SAME-COMMITTEES-P-WHEN-NONFORKING-ORDERED-EVEN-BLOCKCHAINS
 (16 4 (:REWRITE SET::IN-TAIL))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (6 2 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (1 1 (:REWRITE POSP-WHEN-IN-POS-SETP-BINDS-FREE-X))
 )
