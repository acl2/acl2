(ALT-JS-P)
(ALT-JS-P-PROPERTY
 (183 94 (:REWRITE EQUAL-N-1-REDUCTIONS))
 (88 35 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (36 9 (:REWRITE O-INFP->NEQ-0))
 (35 35 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (35 35 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (35 35 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER))
 (26 3 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (25 25 (:REWRITE UAV-ID-FIX-CONSTANT))
 (21 21 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (21 7 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (18 18 (:META *META*-UNHIDE-HIDE))
 (17 1 (:DEFINITION UAV-LIST-P))
 (16 16 (:REWRITE HELPER-RULE))
 (16 16 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (15 1 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (15 1 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (13 13 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-1))
 (12 4 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (11 2 (:LINEAR LIST::LEN-NON-NEGATIVE-LINEAR))
 (11 1 (:LINEAR EVENLY-SPACED-BOUNDARIES))
 (9 9 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (9 9 (:REWRITE UAV-ID-EQUIV-TO-DOUBLE-CONTAINMENT))
 (7 7 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (4 2 (:REWRITE LIST::LEN-WHEN-AT-MOST-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (2 2 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (2 2 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (2 1 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (2 1 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (1 1 (:TYPE-PRESCRIPTION UAV-P))
 (1 1 (:REWRITE UAV-ID-FIX-PLUS))
 (1 1 (:REWRITE POSITIVE-SUM))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT-ZERO))
 (1 1 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 )
(NOT-JS-P
 (16 16 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(NOT-LEFT-SYNCHRONIZED-P
 (16 16 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(T-T-IMPLIES-BOOLEANP-NOT-LEFT-SYNCHRONIZED-P)
(NOT-LEFT-SYNCHRONIZED-P
 (14 14 (:TYPE-PRESCRIPTION NOT-UAV-ID-P-FROM-NOT-ACL2-NUMBERP))
 )
(UAV-ID-EQUIV-1-IMPLIES-EQUAL-NOT-LEFT-SYNCHRONIZED-P)
(UAV-LIST-EQUIV-2-IMPLIES-EQUAL-NOT-LEFT-SYNCHRONIZED-P)
(NOT-LEFT-SYNCHRONIZED-P-PROPERTY
 (14601 86 (:REWRITE LOCAL-SYNCHRONIZED-DOUBLE-CONTAINMENT))
 (8730 2910 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (7632 768 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (5488 873 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (5214 873 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (5081 5081 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (4082 471 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (3718 2068 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (2672 2456 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (2669 157 (:DEFINITION UAV-LIST-P))
 (2005 141 (:REWRITE ADJACENT-LOCATIONS-NEVER-SMALLER-MINUS))
 (1413 1413 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (1269 1269 (:REWRITE POSITIVE-SUM))
 (1002 28 (:REWRITE AVERAGE-LOWER-BOUND))
 (899 333 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (873 873 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT-ZERO))
 (625 497 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (544 272 (:REWRITE LIST::LEN-WHEN-AT-MOST-1))
 (465 465 (:META *META*-UNHIDE-HIDE))
 (429 429 (:REWRITE DEFAULT-CDR))
 (415 6 (:DEFINITION HAVE-MET-RIGHT-P))
 (314 314 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (314 157 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (314 157 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (272 272 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (255 255 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (255 255 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (244 5 (:DEFINITION RIGHT-SYNCHRONIZED-P))
 (232 232 (:REWRITE OPEN-UAV-LIST-FIX))
 (177 162 (:REWRITE O-INFP->NEQ-0))
 (157 157 (:TYPE-PRESCRIPTION UAV-P))
 (157 157 (:REWRITE DEFAULT-CAR))
 (128 32 (:LINEAR EVENLY-SPACED-BETWEE-PERIMETER-BOUNDARIES))
 (93 93 (:REWRITE HELPER-RULE))
 (49 49 (:REWRITE EQUAL-N-TO-BOUNDED-INEQUALITY-1))
 (6 6 (:TYPE-PRESCRIPTION HAVE-MET-RIGHT-P))
 (5 5 (:TYPE-PRESCRIPTION RIGHT-SYNCHRONIZED-P))
 (1 1 (:REWRITE <-UAV-ID-FIX-N-REWRITE-2))
 )
(ALT-LEFT-SYNCHRONIZED-P
 (16 16 (:TYPE-PRESCRIPTION UAV-ID-FIX))
 )
(ALT-LEFT-SYNCHRONIZED-P-PROPERTY
 (380 11 (:LINEAR AVERAGE-UPPER-BOUND))
 (380 11 (:LINEAR AVERAGE-LOWER-BOUND))
 (257 208 (:REWRITE EQUAL-N-1-REDUCTIONS))
 (256 16 (:REWRITE ADJACENT-LOCATIONS-NEVER-SMALLER-MINUS))
 (251 25 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT))
 (227 25 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-RIGHT))
 (213 71 (:REWRITE UAV-ID-FIX-NOT-UAV-ID-P))
 (210 12 (:LINEAR EVENLY-SPACED-BOUNDARIES))
 (99 51 (:REWRITE DEFUNG::BOOLEAN-EQUAL-REDUCTION))
 (78 9 (:REWRITE BODY-IMPLIES-WF-ENSEMBLE))
 (76 15 (:LINEAR LIST::LEN-NON-NEGATIVE-LINEAR))
 (58 12 (:REWRITE UAV-ID-FIX-PLUS))
 (56 56 (:REWRITE STENGTHEN-INTEGER-LINEAR-UPPER))
 (56 56 (:REWRITE STENGTHEN-INTEGER-LINEAR-LOWER-N))
 (56 56 (:REWRITE RIGHT-PERIMETER-PINCHING))
 (51 3 (:DEFINITION UAV-LIST-P))
 (45 21 (:REWRITE WF-ENSEMBLE-IMPLIES-BODY))
 (30 15 (:REWRITE LIST::LEN-WHEN-AT-MOST-1))
 (27 27 (:TYPE-PRESCRIPTION UAV-LIST-P))
 (25 25 (:LINEAR LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-BOUNDED-BY-LOCATION-LEFT-ZERO))
 (24 24 (:REWRITE NEGATE-DIRECTION-EQUALITY-REWRITE-0))
 (24 2 (:REWRITE LESS-THAN-ZERO-TO-UAV-ID-EQUIV))
 (18 18 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE LIST::LEN-OF-NON-CONSP))
 (15 15 (:LINEAR LIST::LEN-WHEN-CONSP-LINEAR))
 (15 15 (:LINEAR SYN::LEN-IMPLIES-ACL2-LEN))
 (12 12 (:REWRITE POSITIVE-SUM))
 (12 12 (:LINEAR EVENLY-SPACED-BOUNDARIES-CONSTANT))
 (8 8 (:META *META*-UNHIDE-HIDE))
 (8 2 (:REWRITE O-INFP->NEQ-0))
 (8 1 (:REWRITE COMBINE-CONSTANTS-LINEAR))
 (6 6 (:REWRITE UAV-LIST-P-WHEN-NOT-CONSP))
 (6 6 (:REWRITE HELPER-RULE))
 (6 6 (:REWRITE <-C-UAV-ID-FIX-REWRITE-0))
 (6 3 (:REWRITE UAV-P-OF-CAR-WHEN-UAV-LIST-P))
 (6 3 (:REWRITE UAV-LIST-P-OF-CDR-WHEN-UAV-LIST-P))
 (3 3 (:TYPE-PRESCRIPTION UAV-P))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE OPEN-UAV-LIST-FIX))
 (2 2 (:REWRITE <-UAV-ID-FIX-N-REWRITE-1))
 )
