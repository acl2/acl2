(LRT-EQUALS-RANK-LT
     (8479 1167 (:REWRITE ACL2-NUMBERP-X))
     (5538 5538 (:REWRITE DEFAULT-CDR))
     (3656 914 (:REWRITE RATIONALP-X))
     (3359 3359 (:REWRITE DEFAULT-CAR))
     (1584 261
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (914 914 (:REWRITE REDUCE-RATIONALP-+))
     (914 914 (:REWRITE REDUCE-RATIONALP-*))
     (914 914 (:REWRITE REDUCE-INTEGERP-+))
     (914 914 (:REWRITE RATIONALP-MINUS-X))
     (914 914 (:REWRITE INTEGERP-MINUS-X))
     (914 914 (:META META-RATIONALP-CORRECT))
     (914 914 (:META META-INTEGERP-CORRECT))
     (586 586 (:REWRITE THE-FLOOR-BELOW))
     (586 586 (:REWRITE THE-FLOOR-ABOVE))
     (512 261
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (403 261 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (354 354
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (354 354 (:REWRITE NORMALIZE-ADDENDS))
     (354 354 (:REWRITE DEFAULT-PLUS-1))
     (294 294
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (294 294
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (294 294
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (294 294
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (294 294 (:REWRITE INTEGERP-<-CONSTANT))
     (294 294 (:REWRITE CONSTANT-<-INTEGERP))
     (294 294
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (294 294
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (294 294
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (294 294
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (294 294 (:REWRITE |(< c (- x))|))
     (294 294
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (294 294
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (294 294
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (294 294
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (294 294 (:REWRITE |(< (/ x) (/ y))|))
     (294 294 (:REWRITE |(< (- x) c)|))
     (294 294 (:REWRITE |(< (- x) (- y))|))
     (293 293 (:REWRITE SIMPLIFY-SUMS-<))
     (293 293
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (293 293
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (261 261
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (261 261
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (261 261
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (261 261 (:REWRITE |(equal c (/ x))|))
     (261 261 (:REWRITE |(equal c (- x))|))
     (261 261 (:REWRITE |(equal (/ x) c)|))
     (261 261 (:REWRITE |(equal (/ x) (/ y))|))
     (261 261 (:REWRITE |(equal (- x) c)|))
     (261 261 (:REWRITE |(equal (- x) (- y))|))
     (184 184 (:REWRITE |(< x (if a b c))|))
     (156 156 (:REWRITE |(+ x (if a b c))|))
     (152 152 (:REWRITE |(< (if a b c) x)|))
     (146 146 (:REWRITE |(equal (+ (- c) x) y)|))
     (107 107
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (107 107
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (107 107 (:REWRITE |(< 0 (/ x))|))
     (107 107 (:REWRITE |(< 0 (* x y))|))
     (94 94 (:REWRITE |(< (/ x) 0)|))
     (94 94 (:REWRITE |(< (* x y) 0)|))
     (93 93
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (93 93
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (30 30 (:REWRITE CDR-CONS))
     (23 23 (:REWRITE |(equal x (if a b c))|))
     (2 2 (:REWRITE CAR-CONS)))
(LTN-EQUALS-RANK-LT
     (9648 1320 (:REWRITE ACL2-NUMBERP-X))
     (6446 6446 (:REWRITE DEFAULT-CDR))
     (4164 1041 (:REWRITE RATIONALP-X))
     (3857 3857 (:REWRITE DEFAULT-CAR))
     (1938 365
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1041 1041 (:REWRITE REDUCE-RATIONALP-+))
     (1041 1041 (:REWRITE REDUCE-RATIONALP-*))
     (1041 1041 (:REWRITE REDUCE-INTEGERP-+))
     (1041 1041 (:REWRITE RATIONALP-MINUS-X))
     (1041 1041 (:REWRITE INTEGERP-MINUS-X))
     (1041 1041 (:META META-RATIONALP-CORRECT))
     (1041 1041 (:META META-INTEGERP-CORRECT))
     (928 528 (:REWRITE SIMPLIFY-SUMS-<))
     (928 528
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (928 528
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (855 855 (:REWRITE THE-FLOOR-BELOW))
     (855 855 (:REWRITE THE-FLOOR-ABOVE))
     (788 788 (:REWRITE DEFAULT-PLUS-1))
     (714 365
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (588 588
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (588 588 (:REWRITE NORMALIZE-ADDENDS))
     (529 529
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (529 529
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (529 529
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (529 529
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (529 529 (:REWRITE INTEGERP-<-CONSTANT))
     (529 529 (:REWRITE CONSTANT-<-INTEGERP))
     (529 529
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (529 529
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (529 529
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (529 529
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (529 529 (:REWRITE |(< c (- x))|))
     (529 529
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (529 529
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (529 529
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (529 529
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (529 529 (:REWRITE |(< (/ x) (/ y))|))
     (529 529 (:REWRITE |(< (- x) c)|))
     (529 529 (:REWRITE |(< (- x) (- y))|))
     (527 365 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (365 365
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (365 365
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (365 365
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (365 365 (:REWRITE |(equal c (/ x))|))
     (365 365 (:REWRITE |(equal c (- x))|))
     (365 365 (:REWRITE |(equal (/ x) c)|))
     (365 365 (:REWRITE |(equal (/ x) (/ y))|))
     (365 365 (:REWRITE |(equal (- x) c)|))
     (365 365 (:REWRITE |(equal (- x) (- y))|))
     (232 232 (:REWRITE |(equal (+ (- c) x) y)|))
     (202 202 (:REWRITE |(< x (if a b c))|))
     (174 174 (:REWRITE |(< (if a b c) x)|))
     (116 116
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (116 116
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (116 116 (:REWRITE |(< 0 (/ x))|))
     (116 116 (:REWRITE |(< 0 (* x y))|))
     (111 111 (:REWRITE |(< (/ x) 0)|))
     (111 111 (:REWRITE |(< (* x y) 0)|))
     (110 110
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (110 110
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (32 32 (:REWRITE CDR-CONS))
     (24 24 (:REWRITE |(equal x (if a b c))|))
     (2 2 (:REWRITE CAR-CONS)))
(MEMBER-INSERT-LT
     (58150 5420 (:REWRITE ACL2-NUMBERP-X))
     (26365 4858 (:REWRITE RATIONALP-X))
     (13706 12471 (:REWRITE DEFAULT-CDR))
     (9845 8630 (:REWRITE DEFAULT-CAR))
     (4860 4860 (:REWRITE REDUCE-INTEGERP-+))
     (4860 4860 (:REWRITE INTEGERP-MINUS-X))
     (4860 4860 (:META META-INTEGERP-CORRECT))
     (4858 4858 (:REWRITE REDUCE-RATIONALP-+))
     (4858 4858 (:REWRITE REDUCE-RATIONALP-*))
     (4858 4858 (:REWRITE RATIONALP-MINUS-X))
     (4858 4858 (:META META-RATIONALP-CORRECT))
     (3204 369
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2715 2715 (:REWRITE THE-FLOOR-BELOW))
     (2715 2715 (:REWRITE THE-FLOOR-ABOVE))
     (1439 1433
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1433 1433
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1433 1433
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1433 1433
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1433 1433
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1433 1433 (:REWRITE INTEGERP-<-CONSTANT))
     (1433 1433 (:REWRITE CONSTANT-<-INTEGERP))
     (1433 1433
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1433 1433
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1433 1433
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1433 1433
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1433 1433 (:REWRITE |(< c (- x))|))
     (1433 1433
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1433 1433
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1433 1433
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1433 1433 (:REWRITE |(< (/ x) (/ y))|))
     (1433 1433 (:REWRITE |(< (- x) c)|))
     (1433 1433 (:REWRITE |(< (- x) (- y))|))
     (1425 1425 (:REWRITE SIMPLIFY-SUMS-<))
     (1425 1425
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1425 1425
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1055 1055
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1055 1055 (:REWRITE NORMALIZE-ADDENDS))
     (1055 1055 (:REWRITE DEFAULT-PLUS-1))
     (969 969 (:REWRITE |(< x (if a b c))|))
     (959 959 (:REWRITE |(+ x (if a b c))|))
     (724 724 (:REWRITE |(< 0 (/ x))|))
     (724 724 (:REWRITE |(< 0 (* x y))|))
     (718 718
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (718 718
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (684 369
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (656 656 (:REWRITE |(< (if a b c) x)|))
     (599 369 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (369 369
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (369 369
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (369 369
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (369 369 (:REWRITE |(equal c (/ x))|))
     (369 369 (:REWRITE |(equal c (- x))|))
     (369 369 (:REWRITE |(equal (/ x) c)|))
     (369 369 (:REWRITE |(equal (/ x) (/ y))|))
     (369 369 (:REWRITE |(equal (- x) c)|))
     (369 369 (:REWRITE |(equal (- x) (- y))|))
     (341 341 (:REWRITE |(< (/ x) 0)|))
     (341 341 (:REWRITE |(< (* x y) 0)|))
     (339 339
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (339 339
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (86 86 (:REWRITE |(equal (+ (- c) x) y)|)))
(RANK-IS-NATP-LT
     (2181 313 (:REWRITE ACL2-NUMBERP-X))
     (1023 1023 (:REWRITE DEFAULT-CDR))
     (928 235 (:REWRITE RATIONALP-X))
     (640 640 (:REWRITE DEFAULT-CAR))
     (482 53
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (252 252 (:REWRITE REDUCE-INTEGERP-+))
     (252 252 (:REWRITE INTEGERP-MINUS-X))
     (252 252 (:META META-INTEGERP-CORRECT))
     (235 235 (:REWRITE REDUCE-RATIONALP-+))
     (235 235 (:REWRITE REDUCE-RATIONALP-*))
     (235 235 (:REWRITE RATIONALP-MINUS-X))
     (235 235 (:META META-RATIONALP-CORRECT))
     (156 104 (:REWRITE LEXORDER-TRANSITIVE))
     (146 146 (:REWRITE THE-FLOOR-BELOW))
     (146 146 (:REWRITE THE-FLOOR-ABOVE))
     (102 53
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (86 86 (:REWRITE SIMPLIFY-SUMS-<))
     (86 86
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (86 86 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (86 86
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (86 86
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (86 86
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (86 86
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (86 86 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (86 86 (:REWRITE INTEGERP-<-CONSTANT))
     (86 86 (:REWRITE CONSTANT-<-INTEGERP))
     (86 86
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (86 86
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (86 86
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (86 86
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (86 86 (:REWRITE |(< c (- x))|))
     (86 86
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (86 86
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (86 86
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (86 86
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (86 86 (:REWRITE |(< (/ x) (/ y))|))
     (86 86 (:REWRITE |(< (- x) c)|))
     (86 86 (:REWRITE |(< (- x) (- y))|))
     (82 53 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (53 53
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (53 53
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (53 53
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (53 53 (:REWRITE |(equal c (/ x))|))
     (53 53 (:REWRITE |(equal c (- x))|))
     (53 53 (:REWRITE |(equal (/ x) c)|))
     (53 53 (:REWRITE |(equal (/ x) (/ y))|))
     (53 53 (:REWRITE |(equal (- x) c)|))
     (53 53 (:REWRITE |(equal (- x) (- y))|))
     (52 52 (:REWRITE |(< x (if a b c))|))
     (46 46 (:REWRITE |(< (if a b c) x)|))
     (35 35
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (35 35 (:REWRITE NORMALIZE-ADDENDS))
     (35 35 (:REWRITE DEFAULT-PLUS-1))
     (34 34
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (34 34
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (34 34 (:REWRITE |(< (/ x) 0)|))
     (34 34 (:REWRITE |(< (* x y) 0)|))
     (33 33 (:REWRITE |(+ x (if a b c))|))
     (31 31 (:REWRITE |(equal (+ (- c) x) y)|))
     (28 28 (:REWRITE CDR-CONS))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (26 26 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< 0 (* x y))|))
     (2 2 (:REWRITE CAR-CONS)))
(SIZE-IS-NATP-LT)
(PROPER-MERGE-LT-L1
     (3275 363 (:REWRITE ACL2-NUMBERP-X))
     (1456 316 (:REWRITE RATIONALP-X))
     (737 725 (:REWRITE DEFAULT-CDR))
     (631 631 (:TYPE-PRESCRIPTION MERGE-LT))
     (533 509 (:REWRITE DEFAULT-CAR))
     (320 32
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (316 316 (:REWRITE REDUCE-RATIONALP-+))
     (316 316 (:REWRITE REDUCE-RATIONALP-*))
     (316 316 (:REWRITE REDUCE-INTEGERP-+))
     (316 316 (:REWRITE RATIONALP-MINUS-X))
     (316 316 (:REWRITE INTEGERP-MINUS-X))
     (316 316 (:META META-RATIONALP-CORRECT))
     (316 316 (:META META-INTEGERP-CORRECT))
     (190 190 (:REWRITE THE-FLOOR-BELOW))
     (190 190 (:REWRITE THE-FLOOR-ABOVE))
     (95 95 (:REWRITE SIMPLIFY-SUMS-<))
     (95 95
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (95 95 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (95 95
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (95 95
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (95 95
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (95 95
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (95 95 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (95 95 (:REWRITE INTEGERP-<-CONSTANT))
     (95 95 (:REWRITE CONSTANT-<-INTEGERP))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< c (- x))|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< (/ x) (/ y))|))
     (95 95 (:REWRITE |(< (- x) c)|))
     (95 95 (:REWRITE |(< (- x) (- y))|))
     (64 64 (:REWRITE |(< (if a b c) x)|))
     (64 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (62 62 (:REWRITE |(< x (if a b c))|))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (47 47 (:REWRITE NORMALIZE-ADDENDS))
     (47 47 (:REWRITE DEFAULT-PLUS-1))
     (47 47 (:REWRITE |(+ x (if a b c))|))
     (47 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (33 33 (:REWRITE |(< (/ x) 0)|))
     (33 33 (:REWRITE |(< (* x y) 0)|))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal c (- x))|))
     (32 32 (:REWRITE |(equal (/ x) c)|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) c)|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (31 31 (:REWRITE |(< 0 (/ x))|))
     (31 31 (:REWRITE |(< 0 (* x y))|))
     (15 15 (:REWRITE |(equal (+ (- c) x) y)|)))
(PROPER-MERGE-LT-L2
     (3275 363 (:REWRITE ACL2-NUMBERP-X))
     (1456 316 (:REWRITE RATIONALP-X))
     (799 799 (:TYPE-PRESCRIPTION MERGE-LT))
     (737 725 (:REWRITE DEFAULT-CDR))
     (533 509 (:REWRITE DEFAULT-CAR))
     (320 32
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (316 316 (:REWRITE REDUCE-RATIONALP-+))
     (316 316 (:REWRITE REDUCE-RATIONALP-*))
     (316 316 (:REWRITE REDUCE-INTEGERP-+))
     (316 316 (:REWRITE RATIONALP-MINUS-X))
     (316 316 (:REWRITE INTEGERP-MINUS-X))
     (316 316 (:META META-RATIONALP-CORRECT))
     (316 316 (:META META-INTEGERP-CORRECT))
     (190 190 (:REWRITE THE-FLOOR-BELOW))
     (190 190 (:REWRITE THE-FLOOR-ABOVE))
     (95 95 (:REWRITE SIMPLIFY-SUMS-<))
     (95 95
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (95 95 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (95 95
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (95 95
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (95 95
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (95 95
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (95 95 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (95 95 (:REWRITE INTEGERP-<-CONSTANT))
     (95 95 (:REWRITE CONSTANT-<-INTEGERP))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< c (- x))|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (95 95
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (95 95 (:REWRITE |(< (/ x) (/ y))|))
     (95 95 (:REWRITE |(< (- x) c)|))
     (95 95 (:REWRITE |(< (- x) (- y))|))
     (64 64 (:REWRITE |(< (if a b c) x)|))
     (64 32
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (62 62 (:REWRITE |(< x (if a b c))|))
     (47 47
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (47 47 (:REWRITE NORMALIZE-ADDENDS))
     (47 47 (:REWRITE DEFAULT-PLUS-1))
     (47 47 (:REWRITE |(+ x (if a b c))|))
     (47 32 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (33 33
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (33 33 (:REWRITE |(< (/ x) 0)|))
     (33 33 (:REWRITE |(< (* x y) 0)|))
     (32 32
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (32 32
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (32 32 (:REWRITE |(equal c (/ x))|))
     (32 32 (:REWRITE |(equal c (- x))|))
     (32 32 (:REWRITE |(equal (/ x) c)|))
     (32 32 (:REWRITE |(equal (/ x) (/ y))|))
     (32 32 (:REWRITE |(equal (- x) c)|))
     (32 32 (:REWRITE |(equal (- x) (- y))|))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (31 31
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (31 31 (:REWRITE |(< 0 (/ x))|))
     (31 31 (:REWRITE |(< 0 (* x y))|))
     (15 15 (:REWRITE |(equal (+ (- c) x) y)|)))
(PROPER-MERGE-LT-L3)
(PROPER-MERGE-LT-L4)
(PROPER-MERGE-LT
     (60130 6114 (:REWRITE ACL2-NUMBERP-X))
     (27008 5604 (:REWRITE RATIONALP-X))
     (13442 13300 (:REWRITE DEFAULT-CDR))
     (5604 5604 (:REWRITE REDUCE-RATIONALP-+))
     (5604 5604 (:REWRITE REDUCE-RATIONALP-*))
     (5604 5604 (:REWRITE REDUCE-INTEGERP-+))
     (5604 5604 (:REWRITE RATIONALP-MINUS-X))
     (5604 5604 (:REWRITE INTEGERP-MINUS-X))
     (5604 5604 (:META META-RATIONALP-CORRECT))
     (5604 5604 (:META META-INTEGERP-CORRECT))
     (3536 404
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3382 3382 (:REWRITE THE-FLOOR-BELOW))
     (3382 3382 (:REWRITE THE-FLOOR-ABOVE))
     (1760 1760
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1760 1760
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1760 1760
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1760 1760 (:REWRITE INTEGERP-<-CONSTANT))
     (1760 1760 (:REWRITE CONSTANT-<-INTEGERP))
     (1760 1760
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1760 1760
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1760 1760
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1760 1760
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1760 1760 (:REWRITE |(< c (- x))|))
     (1760 1760
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1760 1760
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1760 1760
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1760 1760
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1760 1760 (:REWRITE |(< (/ x) (/ y))|))
     (1760 1760 (:REWRITE |(< (- x) c)|))
     (1760 1760 (:REWRITE |(< (- x) (- y))|))
     (1744 1744 (:REWRITE SIMPLIFY-SUMS-<))
     (1744 1744
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1744 1744
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1116 1116 (:REWRITE |(< x (if a b c))|))
     (1076 1076 (:REWRITE |(< (if a b c) x)|))
     (1030 1030
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1030 1030 (:REWRITE NORMALIZE-ADDENDS))
     (1030 1030 (:REWRITE DEFAULT-PLUS-1))
     (982 982 (:REWRITE |(+ x (if a b c))|))
     (760 404
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (606 606 (:REWRITE |(< 0 (/ x))|))
     (606 606 (:REWRITE |(< 0 (* x y))|))
     (598 598
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (598 598
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (576 404 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (572 572 (:REWRITE |(< (/ x) 0)|))
     (572 572 (:REWRITE |(< (* x y) 0)|))
     (568 568
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (568 568
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (404 404
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (404 404
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (404 404
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (404 404 (:REWRITE |(equal c (/ x))|))
     (404 404 (:REWRITE |(equal c (- x))|))
     (404 404 (:REWRITE |(equal (/ x) c)|))
     (404 404 (:REWRITE |(equal (/ x) (/ y))|))
     (404 404 (:REWRITE |(equal (- x) c)|))
     (404 404 (:REWRITE |(equal (- x) (- y))|))
     (202 202 (:REWRITE |(equal (+ (- c) x) y)|)))
(PROPER-INSERT-LT
     (407 1 (:DEFINITION MERGE-LT))
     (388 14 (:REWRITE DEFAULT-LESS-THAN-2))
     (367 2 (:DEFINITION MAKE-LT))
     (267 27 (:REWRITE ACL2-NUMBERP-X))
     (257 11 (:REWRITE DEFAULT-LESS-THAN-1))
     (128 8 (:REWRITE DEFAULT-PLUS-2))
     (120 24 (:REWRITE RATIONALP-X))
     (74 74 (:TYPE-PRESCRIPTION MERGE-LT))
     (62 62 (:REWRITE DEFAULT-CDR))
     (47 1 (:REWRITE |(equal (if a b c) x)|))
     (34 34 (:REWRITE DEFAULT-CAR))
     (34 10 (:DEFINITION ROOT-LT))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24 (:REWRITE REDUCE-RATIONALP-*))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE RATIONALP-MINUS-X))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-RATIONALP-CORRECT))
     (24 24 (:META META-INTEGERP-CORRECT))
     (20 2
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (14 14 (:REWRITE THE-FLOOR-BELOW))
     (14 14 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE CONSTANT-<-INTEGERP))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< c (- x))|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7 7
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (7 5 (:REWRITE LEXORDER-TRANSITIVE))
     (5 5 (:REWRITE |(< x (if a b c))|))
     (4 4 (:TYPE-PRESCRIPTION LEXORDER))
     (4 4
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (4 4 (:REWRITE NORMALIZE-ADDENDS))
     (4 4 (:REWRITE DEFAULT-PLUS-1))
     (4 4 (:REWRITE |(< (if a b c) x)|))
     (4 4 (:REWRITE |(+ x (if a b c))|))
     (4 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (3 3
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (3 3 (:REWRITE |(< 0 (/ x))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2 2
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< (/ x) 0)|))
     (2 2 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(PROPER-BUILD-LT
     (1230 3 (:DEFINITION MERGE-LT))
     (1164 42 (:REWRITE DEFAULT-LESS-THAN-2))
     (1101 6 (:DEFINITION MAKE-LT))
     (801 81 (:REWRITE ACL2-NUMBERP-X))
     (771 33 (:REWRITE DEFAULT-LESS-THAN-1))
     (384 24 (:REWRITE DEFAULT-PLUS-2))
     (360 72 (:REWRITE RATIONALP-X))
     (222 222 (:TYPE-PRESCRIPTION MERGE-LT))
     (160 160 (:REWRITE DEFAULT-CDR))
     (141 3 (:REWRITE |(equal (if a b c) x)|))
     (103 103 (:REWRITE DEFAULT-CAR))
     (102 30 (:DEFINITION ROOT-LT))
     (72 72 (:REWRITE REDUCE-RATIONALP-+))
     (72 72 (:REWRITE REDUCE-RATIONALP-*))
     (72 72 (:REWRITE REDUCE-INTEGERP-+))
     (72 72 (:REWRITE RATIONALP-MINUS-X))
     (72 72 (:REWRITE INTEGERP-MINUS-X))
     (72 72 (:META META-RATIONALP-CORRECT))
     (72 72 (:META META-INTEGERP-CORRECT))
     (60 6
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (42 42 (:REWRITE THE-FLOOR-BELOW))
     (42 42 (:REWRITE THE-FLOOR-ABOVE))
     (21 21 (:REWRITE SIMPLIFY-SUMS-<))
     (21 21
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (21 21
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (21 21
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (21 21
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (21 21 (:REWRITE INTEGERP-<-CONSTANT))
     (21 21 (:REWRITE CONSTANT-<-INTEGERP))
     (21 21
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (21 21
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (21 21
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (21 21
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (21 21 (:REWRITE |(< c (- x))|))
     (21 21
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (21 21
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (21 21
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (21 21
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (21 21 (:REWRITE |(< (/ x) (/ y))|))
     (21 21 (:REWRITE |(< (- x) c)|))
     (21 21 (:REWRITE |(< (- x) (- y))|))
     (21 15 (:REWRITE LEXORDER-TRANSITIVE))
     (18 18 (:TYPE-PRESCRIPTION BUILD-LT))
     (15 15 (:REWRITE |(< x (if a b c))|))
     (12 12 (:TYPE-PRESCRIPTION LEXORDER))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (12 12 (:REWRITE |(< (if a b c) x)|))
     (12 12 (:REWRITE |(+ x (if a b c))|))
     (12 6
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (9 9 (:REWRITE |(< 0 (/ x))|))
     (9 9 (:REWRITE |(< 0 (* x y))|))
     (9 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (6 6
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (6 6
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (6 6 (:REWRITE |(equal c (/ x))|))
     (6 6 (:REWRITE |(equal c (- x))|))
     (6 6 (:REWRITE |(equal (/ x) c)|))
     (6 6 (:REWRITE |(equal (/ x) (/ y))|))
     (6 6 (:REWRITE |(equal (- x) c)|))
     (6 6 (:REWRITE |(equal (- x) (- y))|))
     (6 6 (:REWRITE |(< (/ x) 0)|))
     (6 6 (:REWRITE |(< (* x y) 0)|))
     (3 3 (:REWRITE |(equal (+ (- c) x) y)|)))
(PROPER-DELETE-MIN-LT
     (2490 10 (:DEFINITION MAKE-LT))
     (1938 210 (:REWRITE ACL2-NUMBERP-X))
     (864 186 (:REWRITE RATIONALP-X))
     (503 503 (:REWRITE DEFAULT-CDR))
     (374 374 (:TYPE-PRESCRIPTION MERGE-LT))
     (329 329 (:REWRITE DEFAULT-CAR))
     (186 186 (:REWRITE REDUCE-RATIONALP-+))
     (186 186 (:REWRITE REDUCE-RATIONALP-*))
     (186 186 (:REWRITE REDUCE-INTEGERP-+))
     (186 186 (:REWRITE RATIONALP-MINUS-X))
     (186 186 (:REWRITE INTEGERP-MINUS-X))
     (186 186 (:META META-RATIONALP-CORRECT))
     (186 186 (:META META-INTEGERP-CORRECT))
     (161 17
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (108 108 (:REWRITE THE-FLOOR-BELOW))
     (108 108 (:REWRITE THE-FLOOR-ABOVE))
     (59 41 (:REWRITE LEXORDER-TRANSITIVE))
     (56 56 (:REWRITE SIMPLIFY-SUMS-<))
     (56 56
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (56 56 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (56 56
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (56 56
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (56 56
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (56 56
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (56 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (56 56 (:REWRITE INTEGERP-<-CONSTANT))
     (56 56 (:REWRITE CONSTANT-<-INTEGERP))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< c (- x))|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (56 56
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (56 56 (:REWRITE |(< (/ x) (/ y))|))
     (56 56 (:REWRITE |(< (- x) c)|))
     (56 56 (:REWRITE |(< (- x) (- y))|))
     (38 38 (:REWRITE |(< x (if a b c))|))
     (37 37 (:REWRITE |(< (if a b c) x)|))
     (33 17
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (32 32
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (32 32 (:REWRITE NORMALIZE-ADDENDS))
     (32 32 (:REWRITE DEFAULT-PLUS-1))
     (32 32 (:REWRITE |(+ x (if a b c))|))
     (25 17 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (19 19
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (19 19 (:REWRITE |(< 0 (/ x))|))
     (19 19 (:REWRITE |(< 0 (* x y))|))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (18 18 (:REWRITE |(< (/ x) 0)|))
     (18 18 (:REWRITE |(< (* x y) 0)|))
     (17 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (17 17
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (17 17 (:REWRITE |(equal c (/ x))|))
     (17 17 (:REWRITE |(equal c (- x))|))
     (17 17 (:REWRITE |(equal (/ x) c)|))
     (17 17 (:REWRITE |(equal (/ x) (/ y))|))
     (17 17 (:REWRITE |(equal (- x) c)|))
     (17 17 (:REWRITE |(equal (- x) (- y))|))
     (9 9 (:REWRITE |(equal (+ (- c) x) y)|)))
(SIZE-RANK-LT-L1
 (623
  623
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (623 623
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (623
     623
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (623 623
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (623 623
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (225 1
      (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (210 39 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (207 7 (:LINEAR EXPT-<=-1-TWO))
 (206 6 (:LINEAR EXPT-X->=-X))
 (206 6 (:LINEAR EXPT-X->-X))
 (138 66 (:REWRITE DEFAULT-PLUS-2))
 (119 47 (:REWRITE DEFAULT-LESS-THAN-2))
 (108 18 (:REWRITE DEFAULT-TIMES-2))
 (106 66 (:REWRITE DEFAULT-PLUS-1))
 (102 18 (:REWRITE DEFAULT-TIMES-1))
 (92 47 (:REWRITE DEFAULT-LESS-THAN-1))
 (91 37 (:REWRITE SIMPLIFY-SUMS-<))
 (85 7 (:LINEAR EXPT-<-1-TWO))
 (47 47 (:REWRITE THE-FLOOR-BELOW))
 (47 47 (:REWRITE THE-FLOOR-ABOVE))
 (47 47
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (47 47
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (41 41
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (41 41 (:REWRITE INTEGERP-<-CONSTANT))
 (41 41 (:REWRITE CONSTANT-<-INTEGERP))
 (41 41
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (41 41
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (41 41
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (41 41
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (41 41 (:REWRITE |(< c (- x))|))
 (41 41
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (41 41
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (41 41
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (41 41
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (41 41 (:REWRITE |(< (/ x) (/ y))|))
 (41 41 (:REWRITE |(< (- x) c)|))
 (41 41 (:REWRITE |(< (- x) (- y))|))
 (34 34 (:REWRITE DEFAULT-EXPT-2))
 (34 34 (:REWRITE DEFAULT-EXPT-1))
 (34 34 (:REWRITE |(expt 1/c n)|))
 (34 34 (:REWRITE |(expt (- x) n)|))
 (34 7 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (24 24
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (16 16 (:REWRITE |(< 0 (/ x))|))
 (16 16 (:REWRITE |(< 0 (* x y))|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE |(< x (+ c/d y))|))
 (6 6 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-MINUS))
 (2 2 (:REWRITE |(< y (+ (- c) x))|)))
(SIZE-RANK-LT
 (2471 350 (:REWRITE ACL2-NUMBERP-X))
 (1871 1871 (:REWRITE DEFAULT-CDR))
 (1410
   1410
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1410
  1410
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1410
      1410
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1410
     1410
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1410 1410
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1128 1128 (:REWRITE DEFAULT-CAR))
 (1005 279 (:REWRITE RATIONALP-X))
 (453 75
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (444 227
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (444 227
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (416 12 (:LINEAR EXPT->=-1-ONE))
 (414 12 (:LINEAR EXPT-<=-1-TWO))
 (404 227 (:REWRITE SIMPLIFY-SUMS-<))
 (404 12 (:LINEAR EXPT-<-1-TWO))
 (402 12 (:LINEAR EXPT->-1-ONE))
 (354 12 (:LINEAR EXPT-X->=-X))
 (354 12 (:LINEAR EXPT-X->-X))
 (328 328 (:REWRITE THE-FLOOR-BELOW))
 (328 328 (:REWRITE THE-FLOOR-ABOVE))
 (295 224 (:REWRITE DEFAULT-PLUS-1))
 (279 279 (:REWRITE REDUCE-RATIONALP-+))
 (279 279 (:REWRITE REDUCE-RATIONALP-*))
 (279 279 (:REWRITE RATIONALP-MINUS-X))
 (279 279 (:META META-RATIONALP-CORRECT))
 (262 262 (:REWRITE REDUCE-INTEGERP-+))
 (262 262 (:REWRITE INTEGERP-MINUS-X))
 (262 262 (:META META-INTEGERP-CORRECT))
 (258 166 (:REWRITE LEXORDER-TRANSITIVE))
 (242 242
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (242 242
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (237 237
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (237 237 (:REWRITE INTEGERP-<-CONSTANT))
 (237 237 (:REWRITE CONSTANT-<-INTEGERP))
 (237 237
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (237 237
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (237 237
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (237 237
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (237 237 (:REWRITE |(< c (- x))|))
 (237 237
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (237 237
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (237 237
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (237 237
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (237 237 (:REWRITE |(< (/ x) (/ y))|))
 (237 237 (:REWRITE |(< (- x) c)|))
 (237 237 (:REWRITE |(< (- x) (- y))|))
 (211 211
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (211 211 (:REWRITE NORMALIZE-ADDENDS))
 (119 75
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (102 75 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (75 75
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (75 75
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (75 75
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (75 75 (:REWRITE |(equal c (/ x))|))
 (75 75 (:REWRITE |(equal c (- x))|))
 (75 75 (:REWRITE |(equal (/ x) c)|))
 (75 75 (:REWRITE |(equal (/ x) (/ y))|))
 (75 75 (:REWRITE |(equal (- x) c)|))
 (75 75 (:REWRITE |(equal (- x) (- y))|))
 (75 75 (:REWRITE |(< 0 (/ x))|))
 (75 75 (:REWRITE |(< 0 (* x y))|))
 (71 71 (:REWRITE FOLD-CONSTS-IN-+))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (62 62
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (62 62 (:REWRITE |(< (/ x) 0)|))
 (62 62 (:REWRITE |(< (* x y) 0)|))
 (45 45 (:REWRITE |(equal (+ (- c) x) y)|))
 (45 45 (:REWRITE |(< (if a b c) x)|))
 (36 36 (:REWRITE DEFAULT-EXPT-1))
 (36 36 (:REWRITE |(expt 1/c n)|))
 (36 36 (:REWRITE |(expt (- x) n)|))
 (35 35 (:REWRITE |(< (+ c/d x) y)|))
 (33 33 (:REWRITE |(< (+ (- c) x) y)|))
 (24 24
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (24 24
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (24 24
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (21 21 (:REWRITE |(< x (+ c/d y))|))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (14 14 (:LINEAR EXPT-LINEAR-LOWER-<))
 (12 12 (:LINEAR EXPT-LINEAR-UPPER-<))
 (12 12 (:LINEAR EXPT->=-1-TWO))
 (12 12 (:LINEAR EXPT->-1-TWO))
 (12 12 (:LINEAR EXPT-<=-1-ONE))
 (12 12 (:LINEAR EXPT-<-1-ONE))
 (5 5 (:REWRITE |(expt x (if a b c))|)))
