(REWRITE-EQUAL-<-TO-IFF-<
 (10 6 (:REWRITE DEFAULT-<-2))
 (10 6 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(EQUAL-*-1
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(EQUAL-*-2
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(SIMPLIFY-TERMS-SUCH-AS-AX+BX-REL-0-FN)
(SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE BIG-HELPER-1))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON
 (29 29 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16 (:REWRITE BIG-HELPER-1))
 (15 3 (:REWRITE HELPER-14))
 (15 3 (:REWRITE HELPER-13))
 (9 3 (:REWRITE HELPER-16))
 (9 3 (:REWRITE HELPER-15))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 )
(SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11 (:REWRITE BIG-HELPER-1))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (18 3 (:REWRITE HELPER-12))
 (18 3 (:REWRITE HELPER-11))
 (15 15 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (13 13 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 13 (:REWRITE BIG-HELPER-1))
 (12 3 (:REWRITE HELPER-18))
 (12 3 (:REWRITE HELPER-17))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 )
(ADDEND-VAL
 (171 78 (:REWRITE DEFAULT-+-2))
 (126 18 (:DEFINITION INTEGER-ABS))
 (102 78 (:REWRITE DEFAULT-+-1))
 (72 18 (:REWRITE |(+ y x)|))
 (72 9 (:DEFINITION LENGTH))
 (45 9 (:DEFINITION LEN))
 (38 38 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE FOLD-CONSTS-IN-+))
 (26 26 (:REWRITE |(+ c (+ d x))|))
 (22 20 (:REWRITE DEFAULT-<-2))
 (22 20 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (18 18 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:REWRITE BIG-HELPER-1))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (9 9 (:REWRITE DEFAULT-REALPART))
 (9 9 (:REWRITE DEFAULT-NUMERATOR))
 (9 9 (:REWRITE DEFAULT-IMAGPART))
 (9 9 (:REWRITE DEFAULT-DENOMINATOR))
 (9 9 (:REWRITE DEFAULT-COERCE-2))
 (9 9 (:REWRITE DEFAULT-COERCE-1))
 )
(ADDEND-INFO-ENTRY)
(ADDEND-INFO-LIST
 (271 122 (:REWRITE DEFAULT-+-2))
 (182 26 (:DEFINITION INTEGER-ABS))
 (162 122 (:REWRITE DEFAULT-+-1))
 (104 26 (:REWRITE |(+ y x)|))
 (104 13 (:DEFINITION LENGTH))
 (65 13 (:DEFINITION LEN))
 (63 63 (:REWRITE DEFAULT-CDR))
 (43 43 (:REWRITE FOLD-CONSTS-IN-+))
 (43 43 (:REWRITE |(+ c (+ d x))|))
 (41 41 (:REWRITE DEFAULT-CAR))
 (30 28 (:REWRITE DEFAULT-<-2))
 (30 28 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (26 26 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (26 26 (:REWRITE BIG-HELPER-1))
 (13 13 (:TYPE-PRESCRIPTION LEN))
 (13 13 (:REWRITE DEFAULT-REALPART))
 (13 13 (:REWRITE DEFAULT-NUMERATOR))
 (13 13 (:REWRITE DEFAULT-IMAGPART))
 (13 13 (:REWRITE DEFAULT-DENOMINATOR))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(TEMP-1
 (140 130 (:REWRITE DEFAULT-CDR))
 (124 120 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE BIG-HELPER-1))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 )
(ADDEND-INFO-LIST-THM
 (373 360 (:REWRITE DEFAULT-CDR))
 (23 23 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (23 23 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (23 23 (:REWRITE DEFAULT-UNARY-MINUS))
 (23 23 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE BIG-HELPER-1))
 (16 4 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION QUOTEP))
 )
(ASSOC-ADDEND
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (2 1 (:DEFINITION TRUE-LISTP))
 )
(FIRST-MATCH-IN-ADDEND-INFO-LISTS
 (2741 2741 (:REWRITE DEFAULT-CAR))
 (1957 1957 (:REWRITE DEFAULT-CDR))
 (690 230 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 )
(FIND-MATCHING-ADDENDS)
(FIND-MATCHING-ADDENDS)
(SIMPLIFY-SUMS-EQUAL
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(SIMPLIFY-SUMS-<
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(NEGATIVE-ADDEND-P)
(FIND-NEGATIVE-ADDEND1
 (953 428 (:REWRITE DEFAULT-+-2))
 (615 615 (:REWRITE DEFAULT-CDR))
 (560 10 (:DEFINITION NEGATE-MATCH))
 (551 428 (:REWRITE DEFAULT-+-1))
 (532 76 (:DEFINITION INTEGER-ABS))
 (413 413 (:REWRITE DEFAULT-CAR))
 (304 76 (:REWRITE |(+ y x)|))
 (304 38 (:DEFINITION LENGTH))
 (190 38 (:DEFINITION LEN))
 (159 159 (:REWRITE FOLD-CONSTS-IN-+))
 (140 20 (:DEFINITION NUMERIC-CONSTANT-P))
 (122 94 (:REWRITE DEFAULT-<-2))
 (110 94 (:REWRITE DEFAULT-<-1))
 (96 96 (:REWRITE DEFAULT-UNARY-MINUS))
 (78 78 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (78 78 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (78 78 (:REWRITE BIG-HELPER-1))
 (44 22 (:DEFINITION QUOTEP))
 (38 38 (:TYPE-PRESCRIPTION LEN))
 (38 38 (:REWRITE DEFAULT-REALPART))
 (38 38 (:REWRITE DEFAULT-NUMERATOR))
 (38 38 (:REWRITE DEFAULT-IMAGPART))
 (38 38 (:REWRITE DEFAULT-DENOMINATOR))
 (38 38 (:REWRITE DEFAULT-COERCE-2))
 (38 38 (:REWRITE DEFAULT-COERCE-1))
 (22 22 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:DEFINITION KWOTE))
 (14 2 (:DEFINITION RATIONAL-CONSTANT-P))
 (2 2 (:TYPE-PRESCRIPTION QUOTEP))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 )
(FIND-NEGATIVE-ADDEND)
(PREFER-POSITIVE-ADDENDS-EQUAL
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(PREFER-POSITIVE-ADDENDS-<
 (6 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(FIND-DIVISIVE-FACTOR-SCATTER-EXPONENTS2
 (610 276 (:REWRITE DEFAULT-+-2))
 (448 64 (:DEFINITION INTEGER-ABS))
 (364 276 (:REWRITE DEFAULT-+-1))
 (256 64 (:REWRITE |(+ y x)|))
 (256 32 (:DEFINITION LENGTH))
 (160 32 (:DEFINITION LEN))
 (146 146 (:REWRITE DEFAULT-CDR))
 (96 96 (:REWRITE FOLD-CONSTS-IN-+))
 (91 91 (:REWRITE DEFAULT-CAR))
 (79 71 (:REWRITE DEFAULT-<-2))
 (77 71 (:REWRITE DEFAULT-<-1))
 (64 64 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (64 64 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (64 64 (:REWRITE DEFAULT-UNARY-MINUS))
 (64 64 (:REWRITE BIG-HELPER-1))
 (32 32 (:TYPE-PRESCRIPTION LEN))
 (32 32 (:REWRITE DEFAULT-REALPART))
 (32 32 (:REWRITE DEFAULT-NUMERATOR))
 (32 32 (:REWRITE DEFAULT-IMAGPART))
 (32 32 (:REWRITE DEFAULT-DENOMINATOR))
 (32 32 (:REWRITE DEFAULT-COERCE-2))
 (32 32 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 )
(FIND-DIVISIVE-FACTOR-SCATTER-EXPONENTS1
 (4536 2 (:DEFINITION FIND-DIVISIVE-FACTOR-SCATTER-EXPONENTS2))
 (3636 52 (:DEFINITION INVERT-MATCH))
 (2688 48 (:DEFINITION NEGATE-MATCH))
 (1926 1926 (:REWRITE DEFAULT-CDR))
 (1361 1361 (:REWRITE DEFAULT-CAR))
 (828 148 (:DEFINITION NUMERIC-CONSTANT-P))
 (320 160 (:DEFINITION QUOTEP))
 (268 120 (:REWRITE DEFAULT-+-2))
 (232 26 (:DEFINITION STABLE-UNDER-REWRITING-PRODUCTS))
 (196 28 (:DEFINITION INTEGER-ABS))
 (160 120 (:REWRITE DEFAULT-+-1))
 (124 124 (:REWRITE DEFAULT-UNARY-MINUS))
 (112 28 (:REWRITE |(+ y x)|))
 (112 14 (:DEFINITION LENGTH))
 (96 96 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (96 96 (:DEFINITION KWOTE))
 (78 6 (:DEFINITION MEMBER-EQUAL))
 (70 14 (:DEFINITION LEN))
 (66 22 (:DEFINITION FN-SYMB))
 (60 10 (:DEFINITION RATIONAL-CONSTANT-P))
 (48 48 (:REWRITE CAR-CONS))
 (45 41 (:REWRITE DEFAULT-<-2))
 (44 44 (:REWRITE FOLD-CONSTS-IN-+))
 (43 41 (:REWRITE DEFAULT-<-1))
 (38 38 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (38 38 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (38 38 (:REWRITE BIG-HELPER-1))
 (28 28 (:DEFINITION STABLE-UNDER-REWRITING))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (14 14 (:REWRITE DEFAULT-REALPART))
 (14 14 (:REWRITE DEFAULT-IMAGPART))
 (14 14 (:REWRITE DEFAULT-DENOMINATOR))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 )
(FIND-DIVISIVE-FACTOR-SCATTER-EXPONENTS)
(PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(FIND-RATIONAL-DIVISIVE-FACTOR-SCATTER-EXPONENTS2
 (610 276 (:REWRITE DEFAULT-+-2))
 (448 64 (:DEFINITION INTEGER-ABS))
 (364 276 (:REWRITE DEFAULT-+-1))
 (256 64 (:REWRITE |(+ y x)|))
 (256 32 (:DEFINITION LENGTH))
 (160 32 (:DEFINITION LEN))
 (146 146 (:REWRITE DEFAULT-CDR))
 (96 96 (:REWRITE FOLD-CONSTS-IN-+))
 (91 91 (:REWRITE DEFAULT-CAR))
 (79 71 (:REWRITE DEFAULT-<-2))
 (77 71 (:REWRITE DEFAULT-<-1))
 (64 64 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (64 64 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (64 64 (:REWRITE DEFAULT-UNARY-MINUS))
 (64 64 (:REWRITE BIG-HELPER-1))
 (32 32 (:TYPE-PRESCRIPTION LEN))
 (32 32 (:REWRITE DEFAULT-REALPART))
 (32 32 (:REWRITE DEFAULT-NUMERATOR))
 (32 32 (:REWRITE DEFAULT-IMAGPART))
 (32 32 (:REWRITE DEFAULT-DENOMINATOR))
 (32 32 (:REWRITE DEFAULT-COERCE-2))
 (32 32 (:REWRITE DEFAULT-COERCE-1))
 (12 6 (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 )
(FIND-RATIONAL-DIVISIVE-FACTOR-SCATTER-EXPONENTS1
 (5280 2 (:DEFINITION FIND-RATIONAL-DIVISIVE-FACTOR-SCATTER-EXPONENTS2))
 (4116 52 (:DEFINITION INVERT-MATCH))
 (3168 48 (:DEFINITION NEGATE-MATCH))
 (1926 1926 (:REWRITE DEFAULT-CDR))
 (1361 1361 (:REWRITE DEFAULT-CAR))
 (1020 148 (:DEFINITION NUMERIC-CONSTANT-P))
 (722 376 (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
 (536 160 (:DEFINITION QUOTEP))
 (442 442 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (308 26 (:DEFINITION STABLE-UNDER-REWRITING-PRODUCTS))
 (268 120 (:REWRITE DEFAULT-+-2))
 (196 28 (:DEFINITION INTEGER-ABS))
 (160 120 (:REWRITE DEFAULT-+-1))
 (124 124 (:REWRITE DEFAULT-UNARY-MINUS))
 (112 28 (:REWRITE |(+ y x)|))
 (112 14 (:DEFINITION LENGTH))
 (96 96 (:DEFINITION KWOTE))
 (96 6 (:DEFINITION MEMBER-EQUAL))
 (88 22 (:DEFINITION FN-SYMB))
 (84 28 (:DEFINITION STABLE-UNDER-REWRITING))
 (80 10 (:DEFINITION RATIONAL-CONSTANT-P))
 (78 26 (:DEFINITION PROVEABLY-REAL/RATIONAL))
 (70 14 (:DEFINITION LEN))
 (48 48 (:REWRITE CAR-CONS))
 (45 41 (:REWRITE DEFAULT-<-2))
 (44 44 (:REWRITE FOLD-CONSTS-IN-+))
 (43 41 (:REWRITE DEFAULT-<-1))
 (38 38 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (38 38 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (38 38 (:REWRITE BIG-HELPER-1))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (14 14 (:REWRITE DEFAULT-REALPART))
 (14 14 (:REWRITE DEFAULT-IMAGPART))
 (14 14 (:REWRITE DEFAULT-DENOMINATOR))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 )
(FIND-RATIONAL-DIVISIVE-FACTOR-SCATTER-EXPONENTS)
(PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
 )
(PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (7 7 (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE RATIONALP-*))
 (4 4 (:REWRITE HELPER-6))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-EQUAL))
 )
