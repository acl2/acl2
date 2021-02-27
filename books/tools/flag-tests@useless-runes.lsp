(FLAG-PSEUDO-TERMP (629 34 (:DEFINITION INTEGER-ABS))
                   (612 211 (:REWRITE DEFAULT-+-2))
                   (323 17 (:REWRITE |(+ (if a b c) x)|))
                   (286 211 (:REWRITE DEFAULT-+-1))
                   (211 211
                        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (187 17 (:REWRITE NUMERATOR-NEGATIVE))
                   (134 134 (:REWRITE DEFAULT-CDR))
                   (118 42 (:REWRITE DEFAULT-UNARY-MINUS))
                   (103 103 (:REWRITE DEFAULT-CAR))
                   (88 68
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (86 48
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (86 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (77 77 (:REWRITE FOLD-CONSTS-IN-+))
                   (68 68
                       (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                   (68 68
                       (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                   (68 68
                       (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                   (68 68
                       (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                   (68 68
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (65 65 (:REWRITE |(< (- x) (- y))|))
                   (62 44 (:REWRITE DEFAULT-<-2))
                   (51 51 (:REWRITE |(< (- x) 0)|))
                   (50 44 (:REWRITE DEFAULT-<-1))
                   (34 34
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (18 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (18 14
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (18 14
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (17 17 (:REWRITE REDUCE-INTEGERP-+))
                   (17 17 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                   (17 17
                       (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (17 17 (:REWRITE INTEGERP-MINUS-X))
                   (17 17 (:REWRITE DEFAULT-REALPART))
                   (17 17 (:REWRITE DEFAULT-NUMERATOR))
                   (17 17 (:REWRITE DEFAULT-IMAGPART))
                   (17 17 (:REWRITE DEFAULT-DENOMINATOR))
                   (17 17 (:REWRITE DEFAULT-COERCE-2))
                   (17 17 (:REWRITE DEFAULT-COERCE-1))
                   (17 17 (:META META-INTEGERP-CORRECT))
                   (16 8 (:REWRITE |(< d (+ c x y))|))
                   (14 14 (:REWRITE |(equal (- x) (- y))|))
                   (12 4 (:DEFINITION SYMBOL-LISTP))
                   (1 1
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
                   (1 1
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                   (1 1 (:REWRITE |(equal (- x) 0)|))
                   (1 1 (:REWRITE |(< 0 (- x))|)))
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-PSEUDO-TERMP-EQUIVALENCES)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP)
(TYPE-OF-PSEUDO-TERMP-TERM)
(TYPE-OF-PSEUDO-TERMP-LIST)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP2)
(BOOLEANP-OF-PSEUDO-TERMP)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP)
(TYPE-OF-PSEUDO-TERMP-TERM)
(TYPE-OF-PSEUDO-TERMP-LIST)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP)
(TYPE-OF-PSEUDO-TERMP)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP)
(TYPE-OF-PSEUDO-TERMP)
(FLAG-LEMMA-FOR-TYPE-OF-PSEUDO-TERMP
     (275 275 (:REWRITE DEFAULT-CAR))
     (274 274 (:REWRITE DEFAULT-CDR))
     (80 40 (:REWRITE DEFAULT-+-2))
     (75 3 (:REWRITE |(equal (if a b c) x)|))
     (62 62
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (57 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (57 32
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (57 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (55 55
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (40 40
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (40 40 (:REWRITE NORMALIZE-ADDENDS))
     (40 40 (:REWRITE DEFAULT-+-1))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (3 3 (:REWRITE DEFAULT-COERCE-2))
     (3 3 (:REWRITE DEFAULT-COERCE-1)))
(TYPE-OF-PSEUDO-TERMP)
(PSEUDO-TERMP-EQUAL-T)
(TERMS-INTO-BUCKET (148 8 (:DEFINITION INTEGER-ABS))
                   (105 35 (:REWRITE DEFAULT-+-2))
                   (76 4 (:REWRITE |(+ (if a b c) x)|))
                   (46 35 (:REWRITE DEFAULT-+-1))
                   (44 4 (:REWRITE NUMERATOR-NEGATIVE))
                   (40 4 (:DEFINITION LENGTH))
                   (35 35
                       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                   (28 10 (:REWRITE DEFAULT-UNARY-MINUS))
                   (28 4 (:DEFINITION LEN))
                   (17 11
                       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                   (17 11 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                   (16 16
                       (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                   (16 16
                       (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                   (16 16
                       (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                   (16 16
                       (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                   (16 16
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                   (16 16
                       (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                   (15 15 (:REWRITE |(< (- x) (- y))|))
                   (13 13 (:REWRITE DEFAULT-CDR))
                   (13 13 (:REWRITE |(+ c (+ d x))|))
                   (12 12 (:REWRITE |(< (- x) 0)|))
                   (12 10 (:REWRITE DEFAULT-<-2))
                   (11 11 (:REWRITE FOLD-CONSTS-IN-+))
                   (11 10 (:REWRITE DEFAULT-<-1))
                   (9 9 (:REWRITE DEFAULT-CAR))
                   (8 8
                      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                   (4 4 (:TYPE-PRESCRIPTION LEN))
                   (4 4 (:REWRITE REDUCE-INTEGERP-+))
                   (4 4 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                   (4 4 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (4 4 (:REWRITE INTEGERP-MINUS-X))
                   (4 4 (:REWRITE DEFAULT-REALPART))
                   (4 4 (:REWRITE DEFAULT-NUMERATOR))
                   (4 4 (:REWRITE DEFAULT-IMAGPART))
                   (4 4 (:REWRITE DEFAULT-DENOMINATOR))
                   (4 4 (:REWRITE DEFAULT-COERCE-2))
                   (4 4 (:REWRITE DEFAULT-COERCE-1))
                   (4 4 (:META META-INTEGERP-CORRECT))
                   (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (2 2
                      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (2 2
                      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (2 2 (:REWRITE |(equal (- x) (- y))|))
                   (2 1 (:REWRITE |(< d (+ c x y))|)))
(FLAG-TERMS-INTO-BUCKET)
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-TERMS-INTO-BUCKET-EQUIVALENCES)
(IGNORE-TEST-F)
(FLAG-IGNORE-TEST)
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-IGNORE-TEST-EQUIVALENCES)
(MY-EVENP)
(FLAG-MY-EVENP)
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-MY-EVENP-EQUIVALENCES)
(FLAG-LEMMA-FOR-DEFTHMD-TEST
     (108 12 (:REWRITE ZP-OPEN))
     (72 8 (:REWRITE |(< d (+ c x))|))
     (28 28
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (28 28 (:REWRITE NORMALIZE-ADDENDS))
     (28 28 (:REWRITE DEFAULT-+-2))
     (28 28 (:REWRITE DEFAULT-+-1))
     (18 18
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (18 18
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (10 10 (:REWRITE SIMPLIFY-SUMS-<))
     (10 10
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (10 10 (:REWRITE DEFAULT-<-2))
     (10 10 (:REWRITE DEFAULT-<-1))
     (10 10 (:REWRITE |(< (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2 (:REWRITE REDUCE-INTEGERP-+))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2 (:REWRITE INTEGERP-MINUS-X))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< (- x) 0)|))
     (2 2 (:META META-INTEGERP-CORRECT)))
(MY-EVENP-OF-INCREMENT)
(MY-ODDP-OF-INCREMENT)
(FLAG-LEMMA-FOR-HINTS-TEST-1
     (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (56 8 (:REWRITE ZP-OPEN))
     (36 4 (:REWRITE |(< d (+ c x))|))
     (34 18 (:REWRITE DEFAULT-+-2))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (18 18 (:REWRITE DEFAULT-+-1))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (10 10 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-*-2))
     (5 5 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE |(integerp (* c x))|))
     (4 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (2 2 (:REWRITE |(< (- x) 0)|)))
(MY-EVENP-IS-EVENP)
(MY-ODDP-IS-ODDP)
(FLAG-LEMMA-FOR-HINTS-TEST-2
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (56 8 (:REWRITE ZP-OPEN))
     (36 4 (:REWRITE |(< d (+ c x))|))
     (34 18 (:REWRITE DEFAULT-+-2))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (20 4 (:REWRITE |(+ c (+ d x))|))
     (18 18
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (18 18 (:REWRITE NORMALIZE-ADDENDS))
     (18 18 (:REWRITE DEFAULT-+-1))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (10 10
         (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
     (10 10 (:META META-INTEGERP-CORRECT))
     (6 6 (:REWRITE SIMPLIFY-SUMS-<))
     (6 6
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (6 6 (:REWRITE REDUCE-INTEGERP-+))
     (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (6 6 (:REWRITE INTEGERP-MINUS-X))
     (6 6 (:REWRITE DEFAULT-<-2))
     (6 6 (:REWRITE DEFAULT-<-1))
     (6 6 (:REWRITE |(< (- x) (- y))|))
     (5 5
        (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (5 5 (:REWRITE DEFAULT-*-2))
     (5 5 (:REWRITE DEFAULT-*-1))
     (4 4 (:REWRITE |(integerp (* c x))|))
     (4 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4 3
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (4 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (2 2 (:REWRITE |(< (- x) 0)|)))
(MY-EVENP-IS-EVENP)
(MY-ODDP-IS-ODDP)
(NAT-LIST-EQUIV)
(SUM-PAIRS-LIST (259 14 (:DEFINITION INTEGER-ABS))
                (200 66 (:REWRITE DEFAULT-+-2))
                (133 7 (:REWRITE |(+ (if a b c) x)|))
                (88 66 (:REWRITE DEFAULT-+-1))
                (77 7 (:REWRITE NUMERATOR-NEGATIVE))
                (70 7 (:DEFINITION LENGTH))
                (66 66
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                (49 7 (:DEFINITION LEN))
                (46 16 (:REWRITE DEFAULT-UNARY-MINUS))
                (34 26
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                (31 19
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                (31 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                (28 28
                    (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                (28 28
                    (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                (28 28
                    (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                (28 28
                    (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                (28 28 (:REWRITE DEFAULT-CDR))
                (26 26
                    (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                (26 26 (:REWRITE |(< (- x) (- y))|))
                (24 24 (:REWRITE FOLD-CONSTS-IN-+))
                (23 18 (:REWRITE DEFAULT-<-2))
                (21 21 (:REWRITE |(< (- x) 0)|))
                (21 18 (:REWRITE DEFAULT-<-1))
                (14 14
                    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                (12 12 (:REWRITE DEFAULT-CAR))
                (7 7 (:TYPE-PRESCRIPTION LEN))
                (7 7 (:REWRITE REDUCE-INTEGERP-+))
                (7 7 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                (7 7 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                (7 7 (:REWRITE INTEGERP-MINUS-X))
                (7 7 (:REWRITE DEFAULT-REALPART))
                (7 7 (:REWRITE DEFAULT-NUMERATOR))
                (7 7 (:REWRITE DEFAULT-IMAGPART))
                (7 7 (:REWRITE DEFAULT-DENOMINATOR))
                (7 7 (:REWRITE DEFAULT-COERCE-2))
                (7 7 (:REWRITE DEFAULT-COERCE-1))
                (7 7 (:META META-INTEGERP-CORRECT))
                (7 2 (:REWRITE |(< d (+ c x))|))
                (4 2 (:REWRITE |(< d (+ c x y))|))
                (1 1
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                (1 1 (:REWRITE |(< 0 (- x))|)))
(NAT-LIST-EQUIV-IS-AN-EQUIVALENCE
     (2076 2076 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2076 2076
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2076 2076
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2076 2076 (:REWRITE |(equal (- x) (- y))|))
     (1774 1774 (:REWRITE DEFAULT-CAR))
     (1664 1664
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (1664 1664 (:REWRITE |(equal (- x) 0)|))
     (1459 1459
           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
     (1457 1457 (:REWRITE SIMPLIFY-SUMS-<))
     (1457 1457
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1457 1457
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1457 1457 (:REWRITE DEFAULT-<-2))
     (1457 1457 (:REWRITE DEFAULT-<-1))
     (1457 1457 (:REWRITE |(< (- x) (- y))|))
     (1417 1417
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (1417 1417 (:REWRITE |(< (- x) 0)|))
     (1313 1313 (:REWRITE REDUCE-INTEGERP-+))
     (1313 1313 (:REWRITE INTEGERP-MINUS-X))
     (1313 1313 (:META META-INTEGERP-CORRECT))
     (1020 1020 (:REWRITE DEFAULT-CDR))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
     (40 40 (:REWRITE |(< 0 (- x))|)))
(SUM-PAIRS-LIST-DOUBLE (259 14 (:DEFINITION INTEGER-ABS))
                       (200 66 (:REWRITE DEFAULT-+-2))
                       (133 7 (:REWRITE |(+ (if a b c) x)|))
                       (88 66 (:REWRITE DEFAULT-+-1))
                       (77 7 (:REWRITE NUMERATOR-NEGATIVE))
                       (70 7 (:DEFINITION LENGTH))
                       (66 66
                           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                       (49 7 (:DEFINITION LEN))
                       (46 16 (:REWRITE DEFAULT-UNARY-MINUS))
                       (34 26
                           (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
                       (31 19
                           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
                       (31 19 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
                       (28 28
                           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
                       (28 28
                           (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
                       (28 28
                           (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
                       (28 28
                           (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
                       (28 28 (:REWRITE DEFAULT-CDR))
                       (26 26
                           (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
                       (26 26 (:REWRITE |(< (- x) (- y))|))
                       (24 24 (:REWRITE FOLD-CONSTS-IN-+))
                       (23 18 (:REWRITE DEFAULT-<-2))
                       (21 21 (:REWRITE |(< (- x) 0)|))
                       (21 18 (:REWRITE DEFAULT-<-1))
                       (14 14
                           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
                       (12 12 (:REWRITE DEFAULT-CAR))
                       (7 7 (:TYPE-PRESCRIPTION LEN))
                       (7 7 (:REWRITE REDUCE-INTEGERP-+))
                       (7 7 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                       (7 7 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                       (7 7 (:REWRITE INTEGERP-MINUS-X))
                       (7 7 (:REWRITE DEFAULT-REALPART))
                       (7 7 (:REWRITE DEFAULT-NUMERATOR))
                       (7 7 (:REWRITE DEFAULT-IMAGPART))
                       (7 7 (:REWRITE DEFAULT-DENOMINATOR))
                       (7 7 (:REWRITE DEFAULT-COERCE-2))
                       (7 7 (:REWRITE DEFAULT-COERCE-1))
                       (7 7 (:META META-INTEGERP-CORRECT))
                       (7 2 (:REWRITE |(< d (+ c x))|))
                       (4 2 (:REWRITE |(< d (+ c x y))|))
                       (1 1
                          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
                       (1 1 (:REWRITE |(< 0 (- x))|)))
(SUM-PAIRS-LIST-NAT-LIST-EQUIV-CONGRUENCE
     (3078 342 (:REWRITE |(+ x (if a b c))|))
     (2736 1026 (:REWRITE |(+ (if a b c) x)|))
     (1758 1758 (:REWRITE DEFAULT-CDR))
     (976 976 (:REWRITE DEFAULT-CAR))
     (707 707
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
     (707 707 (:REWRITE SIMPLIFY-SUMS-<))
     (707 707
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (707 707
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (707 707 (:REWRITE DEFAULT-<-2))
     (707 707 (:REWRITE DEFAULT-<-1))
     (707 707 (:REWRITE |(< (- x) 0)|))
     (707 707 (:REWRITE |(< (- x) (- y))|))
     (674 674 (:REWRITE REDUCE-INTEGERP-+))
     (674 674 (:REWRITE INTEGERP-MINUS-X))
     (674 674 (:META META-INTEGERP-CORRECT))
     (175 175
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (175 175 (:REWRITE NORMALIZE-ADDENDS))
     (175 175 (:REWRITE DEFAULT-+-2))
     (175 175 (:REWRITE DEFAULT-+-1))
     (79 78 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (79 78
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (79 78
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (78 78 (:REWRITE |(equal (- x) (- y))|))
     (56 56
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
     (56 56 (:REWRITE |(equal (- x) 0)|)))
