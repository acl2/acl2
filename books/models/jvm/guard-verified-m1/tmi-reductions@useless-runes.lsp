(M1::REV)
(M1::REV1)
(M1::SYMP)
(M1::SYM)
(M1::HALF-TAPE)
(M1::TAPEP)
(M1::SHOW-TAPE)
(M1::CURRENT-SYM)
(M1::OPERATIONP)
(M1::STATE-NAMEP)
(M1::TURING-4-TUPLE)
(M1::TURING-MACHINEP)
(M1::INSTR)
(M1::NEW-TAPE)
(M1::TEST-TAPE)
(M1::TEST-TAPE-DEMO)
(M1::TMI (68 1 (:DEFINITION M1::INSTR))
         (30 6 (:REWRITE ACL2-NUMBERP-X))
         (28 2
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
         (20 16 (:REWRITE DEFAULT-PLUS-1))
         (16 16 (:REWRITE DEFAULT-PLUS-2))
         (8 2 (:REWRITE RATIONALP-X))
         (8 2
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
         (7 7 (:REWRITE THE-FLOOR-BELOW))
         (7 7 (:REWRITE THE-FLOOR-ABOVE))
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
         (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
         (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
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
         (6 6 (:REWRITE DEFAULT-CAR))
         (5 5
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
         (5 5
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
         (5 5 (:REWRITE REDUCE-INTEGERP-+))
         (5 5 (:REWRITE INTEGERP-MINUS-X))
         (5 5 (:REWRITE |(< (/ x) 0)|))
         (5 5 (:REWRITE |(< (* x y) 0)|))
         (5 5 (:META META-INTEGERP-CORRECT))
         (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
         (4 4 (:REWRITE DEFAULT-CDR))
         (4 4 (:REWRITE |(< (+ c/d x) y)|))
         (4 4 (:REWRITE |(< (+ (- c) x) y)|))
         (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
         (4 2
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
         (4 2 (:DEFINITION M1::NTH-ALT-DEF))
         (4 1 (:REWRITE M1::NTH-ADD1!))
         (2 2 (:REWRITE REDUCE-RATIONALP-+))
         (2 2 (:REWRITE REDUCE-RATIONALP-*))
         (2 2
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (2 2
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
         (2 2 (:REWRITE RATIONALP-MINUS-X))
         (2 2
            (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
         (2 2
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
         (2 2 (:REWRITE |(equal c (/ x))|))
         (2 2 (:REWRITE |(equal c (- x))|))
         (2 2 (:REWRITE |(equal (/ x) c)|))
         (2 2 (:REWRITE |(equal (/ x) (/ y))|))
         (2 2 (:REWRITE |(equal (- x) c)|))
         (2 2 (:REWRITE |(equal (- x) (- y))|))
         (2 2 (:META META-RATIONALP-CORRECT))
         (1 1 (:REWRITE ZP-OPEN))
         (1 1 (:REWRITE |(equal x (if a b c))|))
         (1 1 (:REWRITE |(equal (if a b c) x)|)))
(M1::ROGERS-PROGRAM-DEMO)
(M1::RENAMING-MAP2)
(M1::RENAMING-MAP1)
(M1::RENAMING-MAP)
(M1::TM-TO-TM1)
(M1::ASSOC-INVERSE)
(M1::TM1-TO-TM)
(M1::DESCENDING-MAP)
(M1::TOTAL-MAP)
(M1::NATP-MAP)
(M1::NATP-MAP-RENAMING-MAP
     (108091 633
             (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (102558 1232
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (98893 1264
            (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (56255 616 (:DEFINITION ALISTP))
     (9049 9045 (:REWRITE DEFAULT-CAR))
     (6229 1159 (:REWRITE ACL2-NUMBERP-X))
     (6224 6224
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (5205 408
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5133 5132 (:REWRITE DEFAULT-CDR))
     (3421 3421 (:REWRITE REDUCE-INTEGERP-+))
     (3421 3421 (:REWRITE INTEGERP-MINUS-X))
     (3421 3421 (:META META-INTEGERP-CORRECT))
     (2585 2585 (:REWRITE THE-FLOOR-BELOW))
     (2585 2585 (:REWRITE THE-FLOOR-ABOVE))
     (2585 2585 (:REWRITE DEFAULT-LESS-THAN-2))
     (2584 2584
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (2584 2584
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (2584 2584
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (2584 2584
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (2584 2584 (:REWRITE INTEGERP-<-CONSTANT))
     (2584 2584 (:REWRITE CONSTANT-<-INTEGERP))
     (2584 2584
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (2584 2584
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (2584 2584
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (2584 2584
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (2584 2584 (:REWRITE |(< c (- x))|))
     (2584 2584
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (2584 2584
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (2584 2584
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (2584 2584
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (2584 2584 (:REWRITE |(< (/ x) 0)|))
     (2584 2584 (:REWRITE |(< (/ x) (/ y))|))
     (2584 2584 (:REWRITE |(< (- x) c)|))
     (2584 2584 (:REWRITE |(< (- x) (- y))|))
     (2584 2584 (:REWRITE |(< (* x y) 0)|))
     (2583 2583
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (2583 2583
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (2583 2583 (:REWRITE SIMPLIFY-SUMS-<))
     (2583 2583
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (2583 2583
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1690 421 (:REWRITE RATIONALP-X))
     (1690 421
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (967 595 (:REWRITE DEFAULT-PLUS-1))
     (777 408 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (777 408
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (595 595 (:REWRITE DEFAULT-PLUS-2))
     (485 485
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (485 485 (:REWRITE NORMALIZE-ADDENDS))
     (421 421 (:REWRITE REDUCE-RATIONALP-+))
     (421 421 (:REWRITE REDUCE-RATIONALP-*))
     (421 421 (:REWRITE RATIONALP-MINUS-X))
     (421 421 (:META META-RATIONALP-CORRECT))
     (408 408
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (408 408
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (408 408
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (408 408 (:REWRITE |(equal c (/ x))|))
     (408 408 (:REWRITE |(equal c (- x))|))
     (408 408 (:REWRITE |(equal (/ x) c)|))
     (408 408 (:REWRITE |(equal (/ x) (/ y))|))
     (408 408 (:REWRITE |(equal (- x) c)|))
     (408 408 (:REWRITE |(equal (- x) (- y))|))
     (12 1 (:REWRITE |(+ y (+ x z))|))
     (4 4 (:REWRITE |(< (+ c/d x) y)|))
     (4 4 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::RENAMING-MAP-PRESERVES-MAP
     (178183 930
             (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (169295 2008
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (163365 2063
             (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (138626 4075 (:DEFINITION NATP))
     (95434 1004 (:DEFINITION ALISTP))
     (14680 14680 (:REWRITE DEFAULT-CAR))
     (12927 2355 (:REWRITE ACL2-NUMBERP-X))
     (10394 813
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (9962 9962
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (7936 7934 (:REWRITE DEFAULT-CDR))
     (5935 5935 (:REWRITE REDUCE-INTEGERP-+))
     (5935 5935 (:REWRITE INTEGERP-MINUS-X))
     (5935 5935 (:META META-INTEGERP-CORRECT))
     (4337 4185
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4185 4185 (:REWRITE THE-FLOOR-BELOW))
     (4185 4185 (:REWRITE THE-FLOOR-ABOVE))
     (4185 4185
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4185 4185
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4185 4185 (:REWRITE DEFAULT-LESS-THAN-2))
     (4185 4185 (:REWRITE DEFAULT-LESS-THAN-1))
     (4181 4181 (:REWRITE SIMPLIFY-SUMS-<))
     (4181 4181
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4181 4181
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4181 4181
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4181 4181
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4181 4181 (:REWRITE INTEGERP-<-CONSTANT))
     (4181 4181 (:REWRITE CONSTANT-<-INTEGERP))
     (4181 4181
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4181 4181
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4181 4181
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4181 4181
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4181 4181 (:REWRITE |(< c (- x))|))
     (4181 4181
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4181 4181
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4181 4181
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4181 4181
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4181 4181 (:REWRITE |(< (/ x) (/ y))|))
     (4181 4181 (:REWRITE |(< (- x) c)|))
     (4181 4181 (:REWRITE |(< (- x) (- y))|))
     (4177 4177 (:REWRITE |(< (* x y) 0)|))
     (4173 4173
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4173 4173
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4173 4173 (:REWRITE |(< (/ x) 0)|))
     (3524 881 (:REWRITE RATIONALP-X))
     (3524 881
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1550 813 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (1550 813
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (881 881 (:REWRITE REDUCE-RATIONALP-+))
     (881 881 (:REWRITE REDUCE-RATIONALP-*))
     (881 881 (:REWRITE RATIONALP-MINUS-X))
     (881 881 (:META META-RATIONALP-CORRECT))
     (813 813
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (813 813
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (813 813
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (813 813 (:REWRITE |(equal c (/ x))|))
     (813 813 (:REWRITE |(equal c (- x))|))
     (813 813 (:REWRITE |(equal (/ x) c)|))
     (813 813 (:REWRITE |(equal (/ x) (/ y))|))
     (813 813 (:REWRITE |(equal (- x) c)|))
     (813 813 (:REWRITE |(equal (- x) (- y))|))
     (666 666 (:REWRITE DEFAULT-PLUS-2))
     (474 474
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (474 474 (:REWRITE NORMALIZE-ADDENDS))
     (80 7 (:REWRITE |(+ y (+ x z))|))
     (28 4 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (8 8 (:REWRITE |(+ 0 x)|))
     (4 4
        (:TYPE-PRESCRIPTION M1::RENAMING-MAP2))
     (4 4 (:REWRITE |(< (+ c/d x) y)|)))
(M1::TOTAL-MAP-RENAMING-MAP
     (587159 3068
             (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (558239 6534
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (539046 6768
             (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (453299 13321 (:DEFINITION NATP))
     (319185 3267 (:DEFINITION ALISTP))
     (49188 49188 (:REWRITE DEFAULT-CAR))
     (35291 6335 (:REWRITE ACL2-NUMBERP-X))
     (32335 32335
            (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (27694 2201
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (26647 26647 (:REWRITE DEFAULT-CDR))
     (18569 18569 (:REWRITE REDUCE-INTEGERP-+))
     (18569 18569 (:REWRITE INTEGERP-MINUS-X))
     (18569 18569 (:META META-INTEGERP-CORRECT))
     (14522 13800
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (13800 13800 (:REWRITE THE-FLOOR-BELOW))
     (13800 13800 (:REWRITE THE-FLOOR-ABOVE))
     (13800 13800
            (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (13800 13800
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (13800 13800 (:REWRITE DEFAULT-LESS-THAN-2))
     (13800 13800 (:REWRITE DEFAULT-LESS-THAN-1))
     (13781 13781 (:REWRITE SIMPLIFY-SUMS-<))
     (13781 13781
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (13781 13781
            (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (13781 13781
            (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13781 13781
            (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (13781 13781 (:REWRITE INTEGERP-<-CONSTANT))
     (13781 13781 (:REWRITE CONSTANT-<-INTEGERP))
     (13781 13781
            (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (13781 13781
            (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (13781 13781
            (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (13781 13781
            (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (13781 13781 (:REWRITE |(< c (- x))|))
     (13781 13781
            (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (13781 13781
            (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (13781 13781
            (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (13781 13781
            (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (13781 13781 (:REWRITE |(< (/ x) (/ y))|))
     (13781 13781 (:REWRITE |(< (- x) c)|))
     (13781 13781 (:REWRITE |(< (- x) (- y))|))
     (13762 13762 (:REWRITE |(< (* x y) 0)|))
     (13743 13743
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (13743 13743
            (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (13743 13743 (:REWRITE |(< (/ x) 0)|))
     (9652 2413 (:REWRITE RATIONALP-X))
     (9652 2413
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (4162 2201 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (4162 2201
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2413 2413 (:REWRITE REDUCE-RATIONALP-+))
     (2413 2413 (:REWRITE REDUCE-RATIONALP-*))
     (2413 2413 (:REWRITE RATIONALP-MINUS-X))
     (2413 2413 (:META META-RATIONALP-CORRECT))
     (2201 2201
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2201 2201
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2201 2201
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2201 2201 (:REWRITE |(equal c (/ x))|))
     (2201 2201 (:REWRITE |(equal c (- x))|))
     (2201 2201 (:REWRITE |(equal (/ x) c)|))
     (2201 2201 (:REWRITE |(equal (/ x) (/ y))|))
     (2201 2201 (:REWRITE |(equal (- x) c)|))
     (2201 2201 (:REWRITE |(equal (- x) (- y))|))
     (2120 2120 (:REWRITE DEFAULT-PLUS-2))
     (1554 1554
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1554 1554 (:REWRITE NORMALIZE-ADDENDS))
     (317 28 (:REWRITE |(+ y (+ x z))|))
     (133 19
          (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
     (42 42
         (:TYPE-PRESCRIPTION M1::RENAMING-MAP2))
     (38 38 (:REWRITE |(+ 0 x)|))
     (19 19 (:REWRITE |(< (+ c/d x) y)|)))
(M1::DESCENDING-MAP-RENAMING-MAP
     (306202 1900
             (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (289160 3974
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (278330 4244
             (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (164477 2118 (:DEFINITION ALISTP))
     (27563 4151 (:REWRITE ACL2-NUMBERP-X))
     (16386 16386
            (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (15505 1205
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (15427 15423 (:REWRITE DEFAULT-CDR))
     (10999 10999 (:REWRITE REDUCE-INTEGERP-+))
     (10999 10999 (:REWRITE INTEGERP-MINUS-X))
     (10999 10999 (:META META-INTEGERP-CORRECT))
     (7889 7889 (:REWRITE THE-FLOOR-BELOW))
     (7889 7889 (:REWRITE THE-FLOOR-ABOVE))
     (7804 1951 (:REWRITE RATIONALP-X))
     (7804 1951
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (7525 7525
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7525 7525
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7525 7525
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7525 7525 (:REWRITE INTEGERP-<-CONSTANT))
     (7525 7525 (:REWRITE CONSTANT-<-INTEGERP))
     (7525 7525
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (7525 7525
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (7525 7525
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (7525 7525
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (7525 7525 (:REWRITE |(< c (- x))|))
     (7525 7525
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (7525 7525
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (7525 7525
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (7525 7525
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (7525 7525 (:REWRITE |(< (/ x) (/ y))|))
     (7525 7525 (:REWRITE |(< (- x) c)|))
     (7525 7525 (:REWRITE |(< (- x) (- y))|))
     (7519 7519
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (7519 7519
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7519 7519
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (7211 7211
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7211 7211
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7211 7211 (:REWRITE |(< (/ x) 0)|))
     (7211 7211 (:REWRITE |(< (* x y) 0)|))
     (4033 2592 (:REWRITE DEFAULT-PLUS-1))
     (2592 2592 (:REWRITE DEFAULT-PLUS-2))
     (2305 1205 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2305 1205
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1951 1951 (:REWRITE REDUCE-RATIONALP-+))
     (1951 1951 (:REWRITE REDUCE-RATIONALP-*))
     (1951 1951 (:REWRITE RATIONALP-MINUS-X))
     (1951 1951 (:META META-RATIONALP-CORRECT))
     (1730 1730
           (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (1205 1205
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (1205 1205
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (1205 1205
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (1205 1205 (:REWRITE |(equal c (/ x))|))
     (1205 1205 (:REWRITE |(equal c (- x))|))
     (1205 1205 (:REWRITE |(equal (/ x) c)|))
     (1205 1205 (:REWRITE |(equal (/ x) (/ y))|))
     (1205 1205 (:REWRITE |(equal (- x) c)|))
     (1205 1205 (:REWRITE |(equal (- x) (- y))|))
     (148 148
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (148 148
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (148 148 (:REWRITE |(< 0 (/ x))|))
     (148 148 (:REWRITE |(< 0 (* x y))|))
     (46 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (23 23 (:REWRITE |(< y (+ (- c) x))|))
     (23 23 (:REWRITE |(< x (+ c/d y))|))
     (6 6 (:REWRITE |(< (+ c/d x) y)|))
     (6 6 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::ASSOC-INVERSE-ASSOC-LEMMA
     (25203 359 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (21127 262
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (15309 54
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (12477 133 (:DEFINITION ALISTP))
     (7945 1223 (:REWRITE DEFAULT-CDR))
     (6927 47 (:REWRITE M1::CONSP-ASSOC))
     (4133 431 (:REWRITE ACL2-NUMBERP-X))
     (3018 24
           (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
     (2357 149
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1884 30
           (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (1493 179 (:REWRITE RATIONALP-X))
     (1493 179
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1278 1278
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (1106 1106 (:REWRITE REDUCE-INTEGERP-+))
     (1106 1106 (:REWRITE INTEGERP-MINUS-X))
     (1106 1106 (:META META-INTEGERP-CORRECT))
     (857 857 (:REWRITE THE-FLOOR-BELOW))
     (857 857 (:REWRITE THE-FLOOR-ABOVE))
     (825 825
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (825 825
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (825 825
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (825 825
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (825 825 (:REWRITE INTEGERP-<-CONSTANT))
     (825 825 (:REWRITE CONSTANT-<-INTEGERP))
     (825 825
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (825 825
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (825 825
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (825 825
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (825 825 (:REWRITE |(< c (- x))|))
     (825 825
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (825 825
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (825 825
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (825 825
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (825 825 (:REWRITE |(< (/ x) (/ y))|))
     (825 825 (:REWRITE |(< (- x) c)|))
     (825 825 (:REWRITE |(< (- x) (- y))|))
     (823 823 (:REWRITE SIMPLIFY-SUMS-<))
     (823 823
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (745 745 (:REWRITE |(< (/ x) 0)|))
     (745 745 (:REWRITE |(< (* x y) 0)|))
     (744 744
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (744 744
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (275 149 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (275 149
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (179 179 (:REWRITE REDUCE-RATIONALP-+))
     (179 179 (:REWRITE REDUCE-RATIONALP-*))
     (179 179 (:REWRITE RATIONALP-MINUS-X))
     (179 179 (:META META-RATIONALP-CORRECT))
     (150 150
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (150 150
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (150 150 (:REWRITE |(equal c (/ x))|))
     (150 150 (:REWRITE |(equal (/ x) (/ y))|))
     (150 150 (:REWRITE |(equal (- x) (- y))|))
     (149 149
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (149 149 (:REWRITE |(equal c (- x))|))
     (149 149 (:REWRITE |(equal (- x) c)|))
     (30 1
         (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (30 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (26 26
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (26 26 (:REWRITE |(< 0 (/ x))|))
     (26 26 (:REWRITE |(< 0 (* x y))|))
     (23 23
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE DEFAULT-TIMES-2))
     (6 6 (:REWRITE DEFAULT-TIMES-1))
     (1 1 (:REWRITE DEFAULT-DIVIDE))
     (1 1 (:REWRITE |(not (equal x (/ y)))|))
     (1 1 (:REWRITE |(equal x (/ y))|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(< x (/ y)) with (< y 0)|)))
(M1::ASSOC-INVERSE-ASSOC
     (4449 62 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (4071 48
           (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (3004 11
           (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (2250 26 (:DEFINITION ALISTP))
     (1492 260 (:REWRITE DEFAULT-CDR))
     (1269 11 (:REWRITE M1::CONSP-ASSOC))
     (1153 121 (:REWRITE ACL2-NUMBERP-X))
     (758 31
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (495 161 (:REWRITE DEFAULT-LESS-THAN-2))
     (477 477 (:REWRITE DEFAULT-CAR))
     (398 59 (:REWRITE RATIONALP-X))
     (398 59
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (324 4
          (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (254 254
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (243 243 (:REWRITE REDUCE-INTEGERP-+))
     (243 243 (:REWRITE INTEGERP-MINUS-X))
     (243 243 (:META META-INTEGERP-CORRECT))
     (213 6
          (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
     (161 161 (:REWRITE THE-FLOOR-BELOW))
     (161 161 (:REWRITE THE-FLOOR-ABOVE))
     (147 147 (:REWRITE SIMPLIFY-SUMS-<))
     (147 147
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (147 147 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (147 147
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (147 147
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (147 147
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (147 147
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (147 147
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (147 147 (:REWRITE INTEGERP-<-CONSTANT))
     (147 147 (:REWRITE CONSTANT-<-INTEGERP))
     (147 147
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (147 147
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (147 147
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (147 147
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (147 147 (:REWRITE |(< c (- x))|))
     (147 147
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (147 147
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (147 147
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (147 147
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (147 147 (:REWRITE |(< (/ x) (/ y))|))
     (147 147 (:REWRITE |(< (- x) c)|))
     (147 147 (:REWRITE |(< (- x) (- y))|))
     (127 127
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (127 127
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (127 127 (:REWRITE |(< (/ x) 0)|))
     (127 127 (:REWRITE |(< (* x y) 0)|))
     (62 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (62 31
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (59 59 (:REWRITE REDUCE-RATIONALP-+))
     (59 59 (:REWRITE REDUCE-RATIONALP-*))
     (59 59 (:REWRITE RATIONALP-MINUS-X))
     (59 59 (:META META-RATIONALP-CORRECT))
     (31 31
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (31 31
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (31 31
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (31 31 (:REWRITE |(equal c (/ x))|))
     (31 31 (:REWRITE |(equal c (- x))|))
     (31 31 (:REWRITE |(equal (/ x) c)|))
     (31 31 (:REWRITE |(equal (/ x) (/ y))|))
     (31 31 (:REWRITE |(equal (- x) c)|))
     (31 31 (:REWRITE |(equal (- x) (- y))|))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (10 10
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (10 10 (:REWRITE |(< 0 (/ x))|))
     (10 10 (:REWRITE |(< 0 (* x y))|)))
(M1::CAR-ASSOC
     (2415 27
           (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (2337 29 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (1904 56 (:DEFINITION NATP))
     (1847 8
           (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (1298 14 (:DEFINITION ALISTP))
     (828 180 (:REWRITE DEFAULT-CAR))
     (684 4 (:REWRITE M1::CONSP-ASSOC))
     (135 135
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (135 27 (:REWRITE ACL2-NUMBERP-X))
     (126 9
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (81 81 (:REWRITE DEFAULT-CDR))
     (78 78 (:REWRITE REDUCE-INTEGERP-+))
     (78 78 (:REWRITE INTEGERP-MINUS-X))
     (78 78 (:META META-INTEGERP-CORRECT))
     (60 60 (:REWRITE THE-FLOOR-BELOW))
     (60 60 (:REWRITE THE-FLOOR-ABOVE))
     (60 60
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (60 60
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (60 60 (:REWRITE SIMPLIFY-SUMS-<))
     (60 60
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (60 60 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (60 60
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (60 60
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (60 60
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (60 60
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (60 60 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (60 60 (:REWRITE INTEGERP-<-CONSTANT))
     (60 60 (:REWRITE DEFAULT-LESS-THAN-2))
     (60 60 (:REWRITE DEFAULT-LESS-THAN-1))
     (60 60 (:REWRITE CONSTANT-<-INTEGERP))
     (60 60
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (60 60
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (60 60
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (60 60
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (60 60 (:REWRITE |(< c (- x))|))
     (60 60
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (60 60
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (60 60
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (60 60
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (60 60 (:REWRITE |(< (/ x) 0)|))
     (60 60 (:REWRITE |(< (/ x) (/ y))|))
     (60 60 (:REWRITE |(< (- x) c)|))
     (60 60 (:REWRITE |(< (- x) (- y))|))
     (60 60 (:REWRITE |(< (* x y) 0)|))
     (36 9 (:REWRITE RATIONALP-X))
     (36 9
         (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (18 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (18 9
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (9 9 (:REWRITE REDUCE-RATIONALP-+))
     (9 9 (:REWRITE REDUCE-RATIONALP-*))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (9 9
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (9 9 (:REWRITE RATIONALP-MINUS-X))
     (9 9
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (9 9 (:REWRITE |(equal c (/ x))|))
     (9 9 (:REWRITE |(equal c (- x))|))
     (9 9 (:REWRITE |(equal (/ x) c)|))
     (9 9 (:REWRITE |(equal (/ x) (/ y))|))
     (9 9 (:REWRITE |(equal (- x) c)|))
     (9 9 (:REWRITE |(equal (- x) (- y))|))
     (9 9 (:META META-RATIONALP-CORRECT)))
(M1::EQUAL-LEN-1 (18 9 (:REWRITE DEFAULT-PLUS-2))
                 (9 9 (:REWRITE DEFAULT-PLUS-1))
                 (7 7 (:REWRITE DEFAULT-CDR))
                 (6 6
                    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
                 (6 6 (:REWRITE NORMALIZE-ADDENDS))
                 (2 2
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                 (2 1
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                 (2 1
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                 (1 1
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                 (1 1 (:REWRITE |(equal x (if a b c))|))
                 (1 1 (:REWRITE |(equal c (/ x))|))
                 (1 1 (:REWRITE |(equal c (- x))|))
                 (1 1 (:REWRITE |(equal (if a b c) x)|))
                 (1 1 (:REWRITE |(equal (/ x) c)|))
                 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
                 (1 1 (:REWRITE |(equal (- x) c)|))
                 (1 1 (:REWRITE |(equal (- x) (- y))|)))
(M1::TM-TO-TM1-TO-TM
     (49248 608
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (47424 608 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (43078 1267 (:DEFINITION NATP))
     (41406 266
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (26448 304 (:DEFINITION ALISTP))
     (15008 4646 (:REWRITE DEFAULT-CDR))
     (11795 1775 (:REWRITE ACL2-NUMBERP-X))
     (10664 124 (:REWRITE M1::CONSP-ASSOC))
     (9712 911
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5969 5937 (:REWRITE DEFAULT-CAR))
     (5938 1429 (:REWRITE DEFAULT-LESS-THAN-2))
     (5047 1402 (:REWRITE DEFAULT-LESS-THAN-1))
     (4941 27 (:DEFINITION M1::DESCENDING-MAP))
     (3648 114 (:DEFINITION M1::ASSOC-INVERSE))
     (3340 835 (:REWRITE RATIONALP-X))
     (3340 835
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (3040 3040
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (2937 2937 (:REWRITE REDUCE-INTEGERP-+))
     (2937 2937 (:REWRITE INTEGERP-MINUS-X))
     (2937 2937 (:META META-INTEGERP-CORRECT))
     (1938 51 (:DEFINITION M1::NATP-MAP))
     (1636 911
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1429 1429 (:REWRITE THE-FLOOR-BELOW))
     (1429 1429 (:REWRITE THE-FLOOR-ABOVE))
     (1348 1348 (:REWRITE SIMPLIFY-SUMS-<))
     (1348 1348
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1348 1348
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1348 1348
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1348 1348
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1348 1348
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1348 1348
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1348 1348
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1348 1348 (:REWRITE INTEGERP-<-CONSTANT))
     (1348 1348 (:REWRITE CONSTANT-<-INTEGERP))
     (1348 1348
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1348 1348
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1348 1348
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1348 1348
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1348 1348 (:REWRITE |(< c (- x))|))
     (1348 1348
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1348 1348
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1348 1348
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1348 1348
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1348 1348 (:REWRITE |(< (/ x) (/ y))|))
     (1348 1348 (:REWRITE |(< (- x) c)|))
     (1348 1348 (:REWRITE |(< (- x) (- y))|))
     (1294 1294
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1294 1294
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1294 1294 (:REWRITE |(< (/ x) 0)|))
     (1294 1294 (:REWRITE |(< (* x y) 0)|))
     (1197 911 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (919 919
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (911 911
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (911 911 (:REWRITE |(equal c (/ x))|))
     (911 911 (:REWRITE |(equal c (- x))|))
     (911 911 (:REWRITE |(equal (/ x) c)|))
     (911 911 (:REWRITE |(equal (/ x) (/ y))|))
     (911 911 (:REWRITE |(equal (- x) c)|))
     (911 911 (:REWRITE |(equal (- x) (- y))|))
     (835 835 (:REWRITE REDUCE-RATIONALP-+))
     (835 835 (:REWRITE REDUCE-RATIONALP-*))
     (835 835 (:REWRITE RATIONALP-MINUS-X))
     (835 835 (:META META-RATIONALP-CORRECT))
     (350 350
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (350 350 (:REWRITE M1::MEMBER-SUBSETP))
     (290 145 (:REWRITE DEFAULT-PLUS-2))
     (145 145 (:REWRITE DEFAULT-PLUS-1))
     (112 112
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (105 105
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (105 105 (:REWRITE NORMALIZE-ADDENDS))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (27 27
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (27 27 (:REWRITE |(< 0 (/ x))|))
     (27 27 (:REWRITE |(< 0 (* x y))|))
     (8 8 (:REWRITE |(equal (+ (- c) x) y)|)))
(M1::NEW-TAPE1)
(M1::TMI1 (68 1 (:DEFINITION M1::INSTR))
          (30 6 (:REWRITE ACL2-NUMBERP-X))
          (28 2
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (20 16 (:REWRITE DEFAULT-PLUS-1))
          (16 16 (:REWRITE DEFAULT-PLUS-2))
          (8 2 (:REWRITE RATIONALP-X))
          (8 2
             (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
          (7 7 (:REWRITE THE-FLOOR-BELOW))
          (7 7 (:REWRITE THE-FLOOR-ABOVE))
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
          (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
          (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
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
          (6 6 (:REWRITE DEFAULT-CAR))
          (5 5
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (5 5
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (5 5 (:REWRITE REDUCE-INTEGERP-+))
          (5 5 (:REWRITE INTEGERP-MINUS-X))
          (5 5 (:REWRITE |(< (/ x) 0)|))
          (5 5 (:REWRITE |(< (* x y) 0)|))
          (5 5 (:META META-INTEGERP-CORRECT))
          (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
          (4 4 (:REWRITE DEFAULT-CDR))
          (4 4 (:REWRITE |(< (+ c/d x) y)|))
          (4 4 (:REWRITE |(< (+ (- c) x) y)|))
          (4 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (4 2
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (4 2 (:DEFINITION M1::NTH-ALT-DEF))
          (4 1 (:REWRITE M1::NTH-ADD1!))
          (2 2 (:REWRITE REDUCE-RATIONALP-+))
          (2 2 (:REWRITE REDUCE-RATIONALP-*))
          (2 2
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
          (2 2
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
          (2 2 (:REWRITE RATIONALP-MINUS-X))
          (2 2
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (2 2
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (2 2 (:REWRITE |(equal c (/ x))|))
          (2 2 (:REWRITE |(equal c (- x))|))
          (2 2 (:REWRITE |(equal (/ x) c)|))
          (2 2 (:REWRITE |(equal (/ x) (/ y))|))
          (2 2 (:REWRITE |(equal (- x) c)|))
          (2 2 (:REWRITE |(equal (- x) (- y))|))
          (2 2 (:META META-RATIONALP-CORRECT))
          (1 1 (:REWRITE ZP-OPEN))
          (1 1 (:REWRITE |(equal x (if a b c))|))
          (1 1 (:REWRITE |(equal (if a b c) x)|)))
(M1::CAR-INSTR (3796 628 (:REWRITE ACL2-NUMBERP-X))
               (3756 311
                     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
               (1203 1203 (:REWRITE DEFAULT-CAR))
               (1056 264 (:REWRITE RATIONALP-X))
               (1056 264
                     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
               (588 311
                    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
               (571 571 (:REWRITE DEFAULT-CDR))
               (528 528 (:REWRITE REDUCE-INTEGERP-+))
               (528 528 (:REWRITE INTEGERP-MINUS-X))
               (528 528 (:META META-INTEGERP-CORRECT))
               (411 311 (:REWRITE SIMPLIFY-SUMS-EQUAL))
               (311 311
                    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
               (311 311
                    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
               (311 311
                    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
               (311 311 (:REWRITE |(equal c (/ x))|))
               (311 311 (:REWRITE |(equal c (- x))|))
               (311 311 (:REWRITE |(equal (/ x) c)|))
               (311 311 (:REWRITE |(equal (/ x) (/ y))|))
               (311 311 (:REWRITE |(equal (- x) c)|))
               (311 311 (:REWRITE |(equal (- x) (- y))|))
               (264 264 (:REWRITE REDUCE-RATIONALP-+))
               (264 264 (:REWRITE REDUCE-RATIONALP-*))
               (264 264 (:REWRITE RATIONALP-MINUS-X))
               (264 264 (:META META-RATIONALP-CORRECT))
               (182 182
                    (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
               (182 182 (:REWRITE M1::MEMBER-SUBSETP))
               (91 13 (:DEFINITION LEN))
               (56 56
                   (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
               (26 13 (:REWRITE DEFAULT-PLUS-2))
               (26 13 (:DEFINITION TRUE-LISTP))
               (22 22 (:REWRITE |(equal x (if a b c))|))
               (22 22 (:REWRITE |(equal (if a b c) x)|))
               (13 13
                   (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
               (13 13 (:REWRITE NORMALIZE-ADDENDS))
               (13 13 (:REWRITE DEFAULT-PLUS-1)))
(M1::INSTR-IMPLIES-MAPPED-INSTR
     (49608 636 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (48276 596
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (45254 1331 (:DEFINITION NATP))
     (45144 264
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (27124 236 (:DEFINITION ASSOC-EQUAL))
     (25926 298 (:DEFINITION ALISTP))
     (10098 834 (:REWRITE ACL2-NUMBERP-X))
     (8839 3109 (:REWRITE DEFAULT-CDR))
     (8770 1589 (:REWRITE DEFAULT-LESS-THAN-2))
     (7869 43 (:DEFINITION M1::DESCENDING-MAP))
     (7351 1546 (:REWRITE DEFAULT-LESS-THAN-1))
     (6904 480
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (5868 88 (:REWRITE M1::CONSP-ASSOC))
     (5001 4937 (:REWRITE DEFAULT-CAR))
     (3628 502 (:REWRITE RATIONALP-X))
     (3628 502
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (3240 40
           (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (3180 3180
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (2335 2335 (:REWRITE REDUCE-INTEGERP-+))
     (2335 2335 (:REWRITE INTEGERP-MINUS-X))
     (2335 2335 (:META META-INTEGERP-CORRECT))
     (2242 59 (:DEFINITION M1::NATP-MAP))
     (1589 1589 (:REWRITE THE-FLOOR-BELOW))
     (1589 1589 (:REWRITE THE-FLOOR-ABOVE))
     (1460 1460 (:REWRITE SIMPLIFY-SUMS-<))
     (1460 1460
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1460 1460
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1460 1460
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1460 1460
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1460 1460
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1460 1460
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1460 1460
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1460 1460 (:REWRITE INTEGERP-<-CONSTANT))
     (1460 1460 (:REWRITE CONSTANT-<-INTEGERP))
     (1460 1460
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1460 1460
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1460 1460
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1460 1460
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1460 1460 (:REWRITE |(< c (- x))|))
     (1460 1460
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1460 1460
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1460 1460
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1460 1460
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1460 1460 (:REWRITE |(< (/ x) (/ y))|))
     (1460 1460 (:REWRITE |(< (- x) c)|))
     (1460 1460 (:REWRITE |(< (- x) (- y))|))
     (1374 1374
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1374 1374
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1374 1374 (:REWRITE |(< (/ x) 0)|))
     (1374 1374 (:REWRITE |(< (* x y) 0)|))
     (736 480
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (568 480 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (502 502 (:REWRITE REDUCE-RATIONALP-+))
     (502 502 (:REWRITE REDUCE-RATIONALP-*))
     (502 502 (:REWRITE RATIONALP-MINUS-X))
     (502 502 (:META META-RATIONALP-CORRECT))
     (480 480
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (480 480
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (480 480
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (480 480 (:REWRITE |(equal c (/ x))|))
     (480 480 (:REWRITE |(equal c (- x))|))
     (480 480 (:REWRITE |(equal (/ x) c)|))
     (480 480 (:REWRITE |(equal (/ x) (/ y))|))
     (480 480 (:REWRITE |(equal (- x) c)|))
     (480 480 (:REWRITE |(equal (- x) (- y))|))
     (168 168
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (168 168 (:REWRITE M1::MEMBER-SUBSETP))
     (84 12 (:DEFINITION LEN))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (43 43 (:REWRITE |(< 0 (/ x))|))
     (43 43 (:REWRITE |(< 0 (* x y))|))
     (24 12 (:REWRITE DEFAULT-PLUS-2))
     (24 12 (:DEFINITION TRUE-LISTP))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1)))
(M1::CDR-ASSOC-DESCENDING-LEMMA
     (12463 176 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (10581 312 (:DEFINITION NATP))
     (10422 139
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (9043 49
           (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (6438 72 (:DEFINITION ALISTP))
     (3567 193 (:REWRITE ACL2-NUMBERP-X))
     (2114 32
           (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (1993 14 (:REWRITE M1::CONSP-ASSOC))
     (1477 105 (:REWRITE RATIONALP-X))
     (1477 105
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (1017 1017 (:REWRITE DEFAULT-CAR))
     (720 720
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (616 44
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (531 531 (:REWRITE REDUCE-INTEGERP-+))
     (531 531 (:REWRITE INTEGERP-MINUS-X))
     (531 531 (:META META-INTEGERP-CORRECT))
     (428 428 (:REWRITE THE-FLOOR-BELOW))
     (428 428 (:REWRITE THE-FLOOR-ABOVE))
     (405 4
          (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
     (384 384 (:REWRITE SIMPLIFY-SUMS-<))
     (384 384
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (384 384 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (384 384
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (384 384
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (384 384
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (384 384
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (384 384
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (384 384 (:REWRITE INTEGERP-<-CONSTANT))
     (384 384 (:REWRITE CONSTANT-<-INTEGERP))
     (384 384
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (384 384
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (384 384
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (384 384
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (384 384 (:REWRITE |(< c (- x))|))
     (384 384
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (384 384
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (384 384
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (384 384
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (384 384 (:REWRITE |(< (/ x) (/ y))|))
     (384 384 (:REWRITE |(< (- x) c)|))
     (384 384 (:REWRITE |(< (- x) (- y))|))
     (336 336
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (336 336
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (336 336 (:REWRITE |(< (/ x) 0)|))
     (336 336 (:REWRITE |(< (* x y) 0)|))
     (105 105 (:REWRITE REDUCE-RATIONALP-+))
     (105 105 (:REWRITE REDUCE-RATIONALP-*))
     (105 105 (:REWRITE RATIONALP-MINUS-X))
     (105 105 (:META META-RATIONALP-CORRECT))
     (88 44 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (88 44
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (44 44
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (44 44
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (44 44
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (44 44 (:REWRITE |(equal c (/ x))|))
     (44 44 (:REWRITE |(equal c (- x))|))
     (44 44 (:REWRITE |(equal (/ x) c)|))
     (44 44 (:REWRITE |(equal (/ x) (/ y))|))
     (44 44 (:REWRITE |(equal (- x) c)|))
     (44 44 (:REWRITE |(equal (- x) (- y))|))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (22 22
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (22 22 (:REWRITE |(< 0 (/ x))|))
     (22 22 (:REWRITE |(< 0 (* x y))|)))
(M1::MAP-PROPERTY
     (17810 324 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (17621 269
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (15323 90
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (10056 149 (:DEFINITION ALISTP))
     (4256 950 (:REWRITE DEFAULT-CDR))
     (3407 31 (:REWRITE M1::CONSP-ASSOC))
     (2764 340 (:REWRITE ACL2-NUMBERP-X))
     (2004 108
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1803 1803 (:REWRITE DEFAULT-CAR))
     (1533 531 (:REWRITE DEFAULT-LESS-THAN-2))
     (1044 1044
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (916 148 (:REWRITE RATIONALP-X))
     (916 148
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (762 762 (:REWRITE REDUCE-INTEGERP-+))
     (762 762 (:REWRITE INTEGERP-MINUS-X))
     (762 762 (:META META-INTEGERP-CORRECT))
     (648 8
          (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (531 531 (:REWRITE THE-FLOOR-BELOW))
     (531 531 (:REWRITE THE-FLOOR-ABOVE))
     (500 500 (:REWRITE SIMPLIFY-SUMS-<))
     (500 500
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (500 500 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (500 500
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (500 500
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (500 500
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (500 500
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (500 500
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (500 500 (:REWRITE INTEGERP-<-CONSTANT))
     (500 500 (:REWRITE CONSTANT-<-INTEGERP))
     (500 500
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (500 500
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (500 500
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (500 500
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (500 500 (:REWRITE |(< c (- x))|))
     (500 500
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (500 500
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (500 500
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (500 500
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (500 500 (:REWRITE |(< (/ x) (/ y))|))
     (500 500 (:REWRITE |(< (- x) c)|))
     (500 500 (:REWRITE |(< (- x) (- y))|))
     (472 472
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (472 472
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (472 472 (:REWRITE |(< (/ x) 0)|))
     (472 472 (:REWRITE |(< (* x y) 0)|))
     (282 16
          (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
     (204 108 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (204 108
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (148 148 (:REWRITE REDUCE-RATIONALP-+))
     (148 148 (:REWRITE REDUCE-RATIONALP-*))
     (148 148 (:REWRITE RATIONALP-MINUS-X))
     (148 148 (:META META-RATIONALP-CORRECT))
     (108 108
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (108 108
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (108 108
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (108 108 (:REWRITE |(equal c (/ x))|))
     (108 108 (:REWRITE |(equal c (- x))|))
     (108 108 (:REWRITE |(equal (/ x) c)|))
     (108 108 (:REWRITE |(equal (/ x) (/ y))|))
     (108 108 (:REWRITE |(equal (- x) c)|))
     (108 108 (:REWRITE |(equal (- x) (- y))|))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (14 14 (:REWRITE |(< 0 (/ x))|))
     (14 14 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE |(equal x (if a b c))|))
     (6 6 (:REWRITE |(equal (if a b c) x)|)))
(M1::INSTR-IMPLIES-MAPPED-INSTR-VICE-VERSA
     (61414 774
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (60280 360
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (59748 766 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (54094 1591 (:DEFINITION NATP))
     (33669 387 (:DEFINITION ALISTP))
     (9030 1849 (:REWRITE DEFAULT-LESS-THAN-2))
     (7869 43 (:DEFINITION M1::DESCENDING-MAP))
     (7844 3300 (:REWRITE DEFAULT-CDR))
     (7611 1806 (:REWRITE DEFAULT-LESS-THAN-1))
     (7529 845 (:REWRITE ACL2-NUMBERP-X))
     (5373 5349 (:REWRITE DEFAULT-CAR))
     (4655 65 (:REWRITE M1::CONSP-ASSOC))
     (4318 473
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3830 3830
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (2597 2597 (:REWRITE REDUCE-INTEGERP-+))
     (2597 2597 (:REWRITE INTEGERP-MINUS-X))
     (2597 2597 (:META META-INTEGERP-CORRECT))
     (2336 503 (:REWRITE RATIONALP-X))
     (2336 503
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (2242 59 (:DEFINITION M1::NATP-MAP))
     (1849 1849 (:REWRITE THE-FLOOR-BELOW))
     (1849 1849 (:REWRITE THE-FLOOR-ABOVE))
     (1720 1720 (:REWRITE SIMPLIFY-SUMS-<))
     (1720 1720
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1720 1720
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1720 1720
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1720 1720
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1720 1720
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1720 1720
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1720 1720
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1720 1720 (:REWRITE INTEGERP-<-CONSTANT))
     (1720 1720 (:REWRITE CONSTANT-<-INTEGERP))
     (1720 1720
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1720 1720
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1720 1720
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1720 1720
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1720 1720 (:REWRITE |(< c (- x))|))
     (1720 1720
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1720 1720
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1720 1720
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1720 1720
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1720 1720 (:REWRITE |(< (/ x) (/ y))|))
     (1720 1720 (:REWRITE |(< (- x) c)|))
     (1720 1720 (:REWRITE |(< (- x) (- y))|))
     (1634 1634
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1634 1634
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1634 1634 (:REWRITE |(< (/ x) 0)|))
     (1634 1634 (:REWRITE |(< (* x y) 0)|))
     (730 473
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (648 8
          (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (570 473 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (503 503 (:REWRITE REDUCE-RATIONALP-+))
     (503 503 (:REWRITE REDUCE-RATIONALP-*))
     (503 503 (:REWRITE RATIONALP-MINUS-X))
     (503 503 (:META META-RATIONALP-CORRECT))
     (473 473
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (473 473
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (473 473
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (473 473 (:REWRITE |(equal c (/ x))|))
     (473 473 (:REWRITE |(equal c (- x))|))
     (473 473 (:REWRITE |(equal (/ x) c)|))
     (473 473 (:REWRITE |(equal (/ x) (/ y))|))
     (473 473 (:REWRITE |(equal (- x) c)|))
     (473 473 (:REWRITE |(equal (- x) (- y))|))
     (168 168
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (168 168 (:REWRITE M1::MEMBER-SUBSETP))
     (84 12 (:DEFINITION LEN))
     (48 48
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (43 43
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (43 43 (:REWRITE |(< 0 (/ x))|))
     (43 43 (:REWRITE |(< 0 (* x y))|))
     (32 28
         (:REWRITE M1::INSTR-IMPLIES-MAPPED-INSTR))
     (24 12 (:REWRITE DEFAULT-PLUS-2))
     (24 12 (:DEFINITION TRUE-LISTP))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1)))
(M1::INSTR-IMPLIES-ASSOC
     (3572 20
           (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (3336 56
           (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (3184 56 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (3100 28 (:DEFINITION ALISTP))
     (2720 80 (:DEFINITION NATP))
     (1442 122
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1423 211 (:REWRITE ACL2-NUMBERP-X))
     (613 613 (:REWRITE DEFAULT-CAR))
     (404 101 (:REWRITE RATIONALP-X))
     (404 101
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (338 338 (:REWRITE DEFAULT-CDR))
     (282 282 (:REWRITE REDUCE-INTEGERP-+))
     (282 282 (:REWRITE INTEGERP-MINUS-X))
     (282 282 (:META META-INTEGERP-CORRECT))
     (230 122
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (216 216
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (131 122 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (122 122
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (122 122
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (122 122
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (122 122 (:REWRITE |(equal c (/ x))|))
     (122 122 (:REWRITE |(equal c (- x))|))
     (122 122 (:REWRITE |(equal (/ x) c)|))
     (122 122 (:REWRITE |(equal (/ x) (/ y))|))
     (122 122 (:REWRITE |(equal (- x) c)|))
     (122 122 (:REWRITE |(equal (- x) (- y))|))
     (101 101 (:REWRITE REDUCE-RATIONALP-+))
     (101 101 (:REWRITE REDUCE-RATIONALP-*))
     (101 101 (:REWRITE RATIONALP-MINUS-X))
     (101 101 (:META META-RATIONALP-CORRECT))
     (98 98
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (98 98 (:REWRITE M1::MEMBER-SUBSETP))
     (80 80 (:REWRITE THE-FLOOR-BELOW))
     (80 80 (:REWRITE THE-FLOOR-ABOVE))
     (80 80
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (80 80
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (80 80 (:REWRITE SIMPLIFY-SUMS-<))
     (80 80
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (80 80 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (80 80
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (80 80
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (80 80
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (80 80
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (80 80 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (80 80 (:REWRITE INTEGERP-<-CONSTANT))
     (80 80 (:REWRITE DEFAULT-LESS-THAN-2))
     (80 80 (:REWRITE DEFAULT-LESS-THAN-1))
     (80 80 (:REWRITE CONSTANT-<-INTEGERP))
     (80 80
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (80 80
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (80 80
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (80 80
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (80 80 (:REWRITE |(< c (- x))|))
     (80 80
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (80 80
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (80 80
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (80 80
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (80 80 (:REWRITE |(< (/ x) 0)|))
     (80 80 (:REWRITE |(< (/ x) (/ y))|))
     (80 80 (:REWRITE |(< (- x) c)|))
     (80 80 (:REWRITE |(< (- x) (- y))|))
     (80 80 (:REWRITE |(< (* x y) 0)|))
     (49 7 (:DEFINITION LEN))
     (32 32
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 7 (:REWRITE DEFAULT-PLUS-2))
     (14 7 (:DEFINITION TRUE-LISTP))
     (7 7
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (7 7 (:REWRITE NORMALIZE-ADDENDS))
     (7 7 (:REWRITE DEFAULT-PLUS-1)))
(M1::MAPPED-INSTR
     (404800 800 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (201200 27626 (:REWRITE ACL2-NUMBERP-X))
     (196950 15752
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (182988 2346
             (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (173404 2204
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (131680 800
             (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (95874 1102 (:DEFINITION ALISTP))
     (93437 42792 (:REWRITE DEFAULT-CDR))
     (60639 13074 (:REWRITE RATIONALP-X))
     (60639 13074
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (52059 719 (:REWRITE M1::CONSP-ASSOC))
     (45668 45548 (:REWRITE DEFAULT-CAR))
     (30937 30937 (:REWRITE REDUCE-INTEGERP-+))
     (30937 30937 (:REWRITE INTEGERP-MINUS-X))
     (30937 30937 (:META META-INTEGERP-CORRECT))
     (29208 15752
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (17716 15752 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (16686 206
            (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (15752 15752
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15752 15752
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (15752 15752
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (15752 15752 (:REWRITE |(equal c (/ x))|))
     (15752 15752 (:REWRITE |(equal c (- x))|))
     (15752 15752 (:REWRITE |(equal (/ x) c)|))
     (15752 15752 (:REWRITE |(equal (/ x) (/ y))|))
     (15752 15752 (:REWRITE |(equal (- x) c)|))
     (15752 15752 (:REWRITE |(equal (- x) (- y))|))
     (13074 13074 (:REWRITE REDUCE-RATIONALP-+))
     (13074 13074 (:REWRITE REDUCE-RATIONALP-*))
     (13074 13074 (:REWRITE RATIONALP-MINUS-X))
     (13074 13074 (:META META-RATIONALP-CORRECT))
     (12152 12152
            (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (12152 12152 (:REWRITE M1::MEMBER-SUBSETP))
     (11730 11730
            (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (10176 10176 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (6076 868 (:DEFINITION LEN))
     (5275 5275 (:REWRITE THE-FLOOR-BELOW))
     (5275 5275 (:REWRITE THE-FLOOR-ABOVE))
     (5032 5032 (:REWRITE SIMPLIFY-SUMS-<))
     (5032 5032
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5032 5032
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5032 5032
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5032 5032
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5032 5032
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5032 5032
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5032 5032
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5032 5032 (:REWRITE INTEGERP-<-CONSTANT))
     (5032 5032 (:REWRITE CONSTANT-<-INTEGERP))
     (5032 5032
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5032 5032
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5032 5032
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5032 5032
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5032 5032 (:REWRITE |(< c (- x))|))
     (5032 5032
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5032 5032
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5032 5032
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5032 5032
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5032 5032 (:REWRITE |(< (/ x) (/ y))|))
     (5032 5032 (:REWRITE |(< (- x) c)|))
     (5032 5032 (:REWRITE |(< (- x) (- y))|))
     (4870 4870
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4870 4870
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4870 4870 (:REWRITE |(< (/ x) 0)|))
     (4870 4870 (:REWRITE |(< (* x y) 0)|))
     (4280 868 (:DEFINITION TRUE-LISTP))
     (3484 3484
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (3392 3392 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1736 868 (:REWRITE DEFAULT-PLUS-2))
     (868 868
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (868 868 (:REWRITE NORMALIZE-ADDENDS))
     (868 868 (:REWRITE DEFAULT-PLUS-1))
     (81 81
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (81 81
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (81 81 (:REWRITE |(< 0 (/ x))|))
     (81 81 (:REWRITE |(< 0 (* x y))|))
     (11 11 (:REWRITE |(equal x (if a b c))|))
     (11 11 (:REWRITE |(equal (if a b c) x)|)))
(M1::SYMBOLP-ST-OUT-INSTR
     (2252 188
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2250 354 (:REWRITE ACL2-NUMBERP-X))
     (638 638 (:REWRITE DEFAULT-CAR))
     (632 158 (:REWRITE RATIONALP-X))
     (632 158
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (437 437 (:REWRITE DEFAULT-CDR))
     (356 188
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (316 316 (:REWRITE REDUCE-INTEGERP-+))
     (316 316 (:REWRITE INTEGERP-MINUS-X))
     (316 316 (:META META-INTEGERP-CORRECT))
     (226 188 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (188 188
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (188 188
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (188 188
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (188 188 (:REWRITE |(equal c (/ x))|))
     (188 188 (:REWRITE |(equal c (- x))|))
     (188 188 (:REWRITE |(equal (/ x) c)|))
     (188 188 (:REWRITE |(equal (/ x) (/ y))|))
     (188 188 (:REWRITE |(equal (- x) c)|))
     (188 188 (:REWRITE |(equal (- x) (- y))|))
     (158 158 (:REWRITE REDUCE-RATIONALP-+))
     (158 158 (:REWRITE REDUCE-RATIONALP-*))
     (158 158 (:REWRITE RATIONALP-MINUS-X))
     (158 158 (:META META-RATIONALP-CORRECT))
     (140 140
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (140 140 (:REWRITE M1::MEMBER-SUBSETP))
     (70 10 (:DEFINITION LEN))
     (40 40
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (20 10 (:REWRITE DEFAULT-PLUS-2))
     (20 10 (:DEFINITION TRUE-LISTP))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 10 (:REWRITE NORMALIZE-ADDENDS))
     (10 10 (:REWRITE DEFAULT-PLUS-1)))
(M1::TOTAL-MAP-COVERS-TM
     (245240 532 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (87468 7804
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (85366 12286 (:REWRITE ACL2-NUMBERP-X))
     (82812 532
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (78408 968
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (75504 968 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (65824 1936 (:DEFINITION NATP))
     (42108 484 (:DEFINITION ALISTP))
     (24360 6090 (:REWRITE RATIONALP-X))
     (24360 6090
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (20784 20784 (:REWRITE DEFAULT-CDR))
     (20469 20469 (:REWRITE DEFAULT-CAR))
     (14388 7804
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (14116 14116 (:REWRITE REDUCE-INTEGERP-+))
     (14116 14116 (:REWRITE INTEGERP-MINUS-X))
     (14116 14116 (:META META-INTEGERP-CORRECT))
     (7910 7804 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (7804 7804
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7804 7804
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7804 7804
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7804 7804 (:REWRITE |(equal c (/ x))|))
     (7804 7804 (:REWRITE |(equal c (- x))|))
     (7804 7804 (:REWRITE |(equal (/ x) c)|))
     (7804 7804 (:REWRITE |(equal (/ x) (/ y))|))
     (7804 7804 (:REWRITE |(equal (- x) c)|))
     (7804 7804 (:REWRITE |(equal (- x) (- y))|))
     (6916 6916
           (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (6916 6916 (:REWRITE M1::MEMBER-SUBSETP))
     (6090 6090 (:REWRITE REDUCE-RATIONALP-+))
     (6090 6090 (:REWRITE REDUCE-RATIONALP-*))
     (6090 6090 (:REWRITE RATIONALP-MINUS-X))
     (6090 6090 (:META META-RATIONALP-CORRECT))
     (5808 5808 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (4840 4840
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (3458 494 (:DEFINITION LEN))
     (2440 494 (:DEFINITION TRUE-LISTP))
     (2004 2004
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1936 1936 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1936 1936 (:REWRITE THE-FLOOR-BELOW))
     (1936 1936 (:REWRITE THE-FLOOR-ABOVE))
     (1936 1936
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1936 1936
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1936 1936 (:REWRITE SIMPLIFY-SUMS-<))
     (1936 1936
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1936 1936
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1936 1936
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1936 1936
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1936 1936
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1936 1936
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1936 1936
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1936 1936 (:REWRITE INTEGERP-<-CONSTANT))
     (1936 1936 (:REWRITE DEFAULT-LESS-THAN-2))
     (1936 1936 (:REWRITE DEFAULT-LESS-THAN-1))
     (1936 1936 (:REWRITE CONSTANT-<-INTEGERP))
     (1936 1936
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1936 1936
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1936 1936
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1936 1936
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1936 1936 (:REWRITE |(< c (- x))|))
     (1936 1936
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1936 1936
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1936 1936
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1936 1936
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1936 1936 (:REWRITE |(< (/ x) 0)|))
     (1936 1936 (:REWRITE |(< (/ x) (/ y))|))
     (1936 1936 (:REWRITE |(< (- x) c)|))
     (1936 1936 (:REWRITE |(< (- x) (- y))|))
     (1936 1936 (:REWRITE |(< (* x y) 0)|))
     (988 494 (:REWRITE DEFAULT-PLUS-2))
     (494 494
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (494 494 (:REWRITE NORMALIZE-ADDENDS))
     (494 494 (:REWRITE DEFAULT-PLUS-1)))
(M1::MAPPED-NEW-TAPE1
     (34 34 (:REWRITE DEFAULT-CDR))
     (32 32 (:REWRITE DEFAULT-CAR))
     (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (15 15
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (15 15 (:REWRITE |(equal c (/ x))|))
     (15 15 (:REWRITE |(equal c (- x))|))
     (15 15 (:REWRITE |(equal (/ x) c)|))
     (15 15 (:REWRITE |(equal (/ x) (/ y))|))
     (15 15 (:REWRITE |(equal (- x) c)|))
     (15 15 (:REWRITE |(equal (- x) (- y))|))
     (10 10
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (10 10 (:REWRITE M1::MEMBER-SUBSETP))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-INTEGERP-+))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-MINUS-X))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|))
     (1 1 (:META META-INTEGERP-CORRECT)))
(M1::OP-INSTR (5566 934 (:REWRITE ACL2-NUMBERP-X))
              (5472 437
                    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
              (1764 1764 (:REWRITE DEFAULT-CAR))
              (1544 386 (:REWRITE RATIONALP-X))
              (1544 386
                    (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
              (1106 1106 (:REWRITE DEFAULT-CDR))
              (840 437
                   (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
              (772 772 (:REWRITE REDUCE-INTEGERP-+))
              (772 772 (:REWRITE INTEGERP-MINUS-X))
              (772 772 (:META META-INTEGERP-CORRECT))
              (599 437 (:REWRITE SIMPLIFY-SUMS-EQUAL))
              (437 437
                   (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
              (437 437
                   (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
              (437 437
                   (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
              (437 437 (:REWRITE |(equal c (/ x))|))
              (437 437 (:REWRITE |(equal c (- x))|))
              (437 437 (:REWRITE |(equal (/ x) c)|))
              (437 437 (:REWRITE |(equal (/ x) (/ y))|))
              (437 437 (:REWRITE |(equal (- x) c)|))
              (437 437 (:REWRITE |(equal (- x) (- y))|))
              (386 386 (:REWRITE REDUCE-RATIONALP-+))
              (386 386 (:REWRITE REDUCE-RATIONALP-*))
              (386 386 (:REWRITE RATIONALP-MINUS-X))
              (386 386 (:META META-RATIONALP-CORRECT))
              (238 238
                   (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
              (238 238 (:REWRITE M1::MEMBER-SUBSETP))
              (119 17 (:DEFINITION LEN))
              (73 73
                  (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
              (34 17 (:REWRITE DEFAULT-PLUS-2))
              (34 17 (:DEFINITION TRUE-LISTP))
              (17 17
                  (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
              (17 17 (:REWRITE NORMALIZE-ADDENDS))
              (17 17 (:REWRITE DEFAULT-PLUS-1)))
(M1::OP-INSTR-LESSP-TRICK
     (3908 620 (:REWRITE ACL2-NUMBERP-X))
     (3582 306
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1096 274 (:REWRITE RATIONALP-X))
     (1096 274
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (936 936 (:REWRITE DEFAULT-CAR))
     (667 667 (:REWRITE DEFAULT-CDR))
     (570 306
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (548 548 (:REWRITE REDUCE-INTEGERP-+))
     (548 548 (:REWRITE INTEGERP-MINUS-X))
     (548 548 (:META META-INTEGERP-CORRECT))
     (382 306 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (306 306
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (306 306
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (306 306
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (306 306 (:REWRITE |(equal c (/ x))|))
     (306 306 (:REWRITE |(equal c (- x))|))
     (306 306 (:REWRITE |(equal (/ x) c)|))
     (306 306 (:REWRITE |(equal (/ x) (/ y))|))
     (306 306 (:REWRITE |(equal (- x) c)|))
     (306 306 (:REWRITE |(equal (- x) (- y))|))
     (274 274 (:REWRITE REDUCE-RATIONALP-+))
     (274 274 (:REWRITE REDUCE-RATIONALP-*))
     (274 274 (:REWRITE RATIONALP-MINUS-X))
     (274 274 (:META META-RATIONALP-CORRECT))
     (182 182
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (182 182 (:REWRITE M1::MEMBER-SUBSETP))
     (91 13 (:DEFINITION LEN))
     (58 58 (:REWRITE THE-FLOOR-BELOW))
     (58 58 (:REWRITE THE-FLOOR-ABOVE))
     (58 58 (:REWRITE DEFAULT-LESS-THAN-2))
     (52 52
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (26 13 (:REWRITE DEFAULT-PLUS-2))
     (26 13 (:DEFINITION TRUE-LISTP))
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
     (13 13
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (13 13 (:REWRITE NORMALIZE-ADDENDS))
     (13 13 (:REWRITE DEFAULT-PLUS-1)))
(M1::TMI1-IS-TMI-LEMMA
     (116319 18855 (:REWRITE ACL2-NUMBERP-X))
     (113784 11039
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (98164 194 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (80797 508 (:DEFINITION ASSOC-EQUAL))
     (56052 692
            (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (53976 692 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (33174 194
            (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (32488 8122 (:REWRITE RATIONALP-X))
     (32488 8122
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (30102 346 (:DEFINITION ALISTP))
     (29526 29526 (:REWRITE DEFAULT-CAR))
     (26202 33 (:DEFINITION M1::TM-TO-TM1))
     (26131 291 (:REWRITE M1::CONSP-ASSOC))
     (19176 11039
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (17675 17675 (:REWRITE REDUCE-INTEGERP-+))
     (17675 17675 (:REWRITE INTEGERP-MINUS-X))
     (17675 17675 (:META META-INTEGERP-CORRECT))
     (13914 11039 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (11039 11039
            (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (11039 11039
            (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (11039 11039
            (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (11039 11039 (:REWRITE |(equal c (/ x))|))
     (11039 11039 (:REWRITE |(equal c (- x))|))
     (11039 11039 (:REWRITE |(equal (/ x) c)|))
     (11039 11039 (:REWRITE |(equal (/ x) (/ y))|))
     (11039 11039 (:REWRITE |(equal (- x) c)|))
     (11039 11039 (:REWRITE |(equal (- x) (- y))|))
     (8122 8122 (:REWRITE REDUCE-RATIONALP-+))
     (8122 8122 (:REWRITE REDUCE-RATIONALP-*))
     (8122 8122 (:REWRITE RATIONALP-MINUS-X))
     (8122 8122 (:META META-RATIONALP-CORRECT))
     (6788 20 (:REWRITE |(< (if a b c) x)|))
     (3575 3575
           (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (3575 3575 (:REWRITE M1::MEMBER-SUBSETP))
     (3460 3460
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (2508 2508
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (2328 2328 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1709 1709 (:REWRITE THE-FLOOR-BELOW))
     (1709 1709 (:REWRITE THE-FLOOR-ABOVE))
     (1589 227 (:DEFINITION LEN))
     (1570 1570 (:REWRITE SIMPLIFY-SUMS-<))
     (1570 1570
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1570 1570
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1570 1570
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1570 1570
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1570 1570
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1570 1570
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1570 1570
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1570 1570 (:REWRITE INTEGERP-<-CONSTANT))
     (1570 1570 (:REWRITE CONSTANT-<-INTEGERP))
     (1570 1570
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1570 1570
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1570 1570
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1570 1570
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1570 1570 (:REWRITE |(< c (- x))|))
     (1570 1570
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1570 1570
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1570 1570
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1570 1570
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1570 1570 (:REWRITE |(< (/ x) (/ y))|))
     (1570 1570 (:REWRITE |(< (- x) c)|))
     (1570 1570 (:REWRITE |(< (- x) (- y))|))
     (1464 1464
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1464 1464
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1464 1464 (:REWRITE |(< (/ x) 0)|))
     (1464 1464 (:REWRITE |(< (* x y) 0)|))
     (1379 59 (:REWRITE ZP-OPEN))
     (1114 324 (:REWRITE |(equal (if a b c) x)|))
     (1036 227 (:DEFINITION TRUE-LISTP))
     (776 776 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (594 367 (:REWRITE DEFAULT-PLUS-2))
     (367 367 (:REWRITE DEFAULT-PLUS-1))
     (327 327
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (327 327 (:REWRITE NORMALIZE-ADDENDS))
     (264 264 (:REWRITE |(equal x (if a b c))|))
     (200 40 (:REWRITE |(+ c (+ d x))|))
     (73 73
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (73 73
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (73 73 (:REWRITE |(< 0 (/ x))|))
     (73 73 (:REWRITE |(< 0 (* x y))|))
     (40 40 (:REWRITE |(< y (+ (- c) x))|))
     (40 40 (:REWRITE |(< x (+ c/d y))|))
     (14 14 (:TYPE-PRESCRIPTION NATP))
     (10 10 (:REWRITE CONS-CAR-CDR)))
(M1::TMI1-IS-TMI
     (245646 12 (:REWRITE M1::OP-INSTR))
     (206492 148 (:DEFINITION M1::RENAMING-MAP1))
     (174716 130 (:DEFINITION M1::TM-TO-TM1))
     (152232 3258 (:DEFINITION NATP))
     (139424 2896
             (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (132486 2078
             (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (109664 1804 (:DEFINITION MV-NTH))
     (83862 15078 (:REWRITE ACL2-NUMBERP-X))
     (75836 7014
            (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (73919 18005 (:REWRITE DEFAULT-CDR))
     (71026 1533 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (57864 780 (:REWRITE M1::CONSP-ASSOC))
     (41532 2 (:REWRITE M1::MAPPED-NEW-TAPE1))
     (41460 2 (:LINEAR M1::OP-INSTR-LESSP-TRICK))
     (31871 31871 (:REWRITE DEFAULT-CAR))
     (22928 5732 (:REWRITE RATIONALP-X))
     (22928 5732
            (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (14722 14722 (:REWRITE REDUCE-INTEGERP-+))
     (14722 14722 (:REWRITE INTEGERP-MINUS-X))
     (14722 14722 (:META META-INTEGERP-CORRECT))
     (12380 7014
            (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (11073 7014 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (9934 9934
           (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (7014 7014
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (7014 7014
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (7014 7014
           (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (7014 7014 (:REWRITE |(equal c (/ x))|))
     (7014 7014 (:REWRITE |(equal c (- x))|))
     (7014 7014 (:REWRITE |(equal (/ x) c)|))
     (7014 7014 (:REWRITE |(equal (/ x) (/ y))|))
     (7014 7014 (:REWRITE |(equal (- x) c)|))
     (7014 7014 (:REWRITE |(equal (- x) (- y))|))
     (5732 5732 (:REWRITE REDUCE-RATIONALP-+))
     (5732 5732 (:REWRITE REDUCE-RATIONALP-*))
     (5732 5732 (:REWRITE RATIONALP-MINUS-X))
     (5732 5732 (:META META-RATIONALP-CORRECT))
     (5261 673 (:REWRITE DEFAULT-PLUS-1))
     (3904 3904
           (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (3904 3904 (:REWRITE M1::MEMBER-SUBSETP))
     (3258 3258 (:REWRITE THE-FLOOR-BELOW))
     (3258 3258 (:REWRITE THE-FLOOR-ABOVE))
     (3258 3258
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (3258 3258
           (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3258 3258 (:REWRITE SIMPLIFY-SUMS-<))
     (3258 3258
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (3258 3258
           (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (3258 3258
           (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (3258 3258
           (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (3258 3258
           (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (3258 3258
           (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (3258 3258
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (3258 3258 (:REWRITE INTEGERP-<-CONSTANT))
     (3258 3258 (:REWRITE DEFAULT-LESS-THAN-2))
     (3258 3258 (:REWRITE DEFAULT-LESS-THAN-1))
     (3258 3258 (:REWRITE CONSTANT-<-INTEGERP))
     (3258 3258
           (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (3258 3258
           (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (3258 3258
           (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (3258 3258
           (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (3258 3258 (:REWRITE |(< c (- x))|))
     (3258 3258
           (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (3258 3258
           (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (3258 3258
           (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (3258 3258
           (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (3258 3258 (:REWRITE |(< (/ x) 0)|))
     (3258 3258 (:REWRITE |(< (/ x) (/ y))|))
     (3258 3258 (:REWRITE |(< (- x) c)|))
     (3258 3258 (:REWRITE |(< (- x) (- y))|))
     (3258 3258 (:REWRITE |(< (* x y) 0)|))
     (2460 2460 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1392 22 (:DEFINITION M1::INSTR))
     (1346 1346 (:TYPE-PRESCRIPTION NATP))
     (750 673 (:REWRITE DEFAULT-PLUS-2))
     (740 148 (:REWRITE |(+ y x)|))
     (666 2 (:DEFINITION M1::TMI))
     (539 77 (:DEFINITION LEN))
     (379 77 (:DEFINITION TRUE-LISTP))
     (377 377
          (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (377 377 (:REWRITE NORMALIZE-ADDENDS))
     (334 334
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (300 300 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (136 2 (:DEFINITION M1::NEW-TAPE))
     (112 112 (:TYPE-PRESCRIPTION M1::TM-TO-TM1))
     (22 22 (:REWRITE |(equal x (if a b c))|))
     (22 22 (:REWRITE |(equal (if a b c) x)|))
     (4 4 (:REWRITE ZP-OPEN)))
(M1::LOG2 (81 31 (:REWRITE DEFAULT-PLUS-2))
          (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
          (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (80 80 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (76 23 (:REWRITE DEFAULT-LESS-THAN-1))
          (75 31 (:REWRITE DEFAULT-PLUS-1))
          (67 67 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
          (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
          (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
          (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
          (28 23 (:REWRITE DEFAULT-LESS-THAN-2))
          (23 23 (:REWRITE THE-FLOOR-BELOW))
          (23 23 (:REWRITE THE-FLOOR-ABOVE))
          (22 22 (:REWRITE DEFAULT-TIMES-2))
          (22 22 (:REWRITE DEFAULT-TIMES-1))
          (20 17
              (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (20 17
              (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (20 15 (:REWRITE |(< (- x) (- y))|))
          (19 6 (:REWRITE DEFAULT-MINUS))
          (17 17
              (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
          (15 15
              (:REWRITE |(< c (/ x)) positive c --- present in goal|))
          (15 15
              (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
          (15 15
              (:REWRITE |(< c (/ x)) negative c --- present in goal|))
          (15 15
              (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
          (15 15 (:REWRITE |(< c (- x))|))
          (15 15
              (:REWRITE |(< (/ x) c) positive c --- present in goal|))
          (15 15
              (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
          (15 15
              (:REWRITE |(< (/ x) c) negative c --- present in goal|))
          (15 15
              (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
          (15 15 (:REWRITE |(< (/ x) (/ y))|))
          (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (14 14
              (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (14 14 (:REWRITE INTEGERP-<-CONSTANT))
          (14 14 (:REWRITE CONSTANT-<-INTEGERP))
          (13 13
              (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
          (13 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
          (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
          (10 10
              (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
          (9 1
             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
          (9 1
             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
          (9 1
             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
          (7 7 (:REWRITE |(< (/ x) 0)|))
          (7 7 (:REWRITE |(< (+ c/d x) y)|))
          (7 7 (:REWRITE |(< (+ (- c) x) y)|))
          (7 7 (:REWRITE |(< (* x y) 0)|))
          (6 6 (:TYPE-PRESCRIPTION ABS))
          (5 5
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (5 5
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
          (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
          (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
          (5 1
             (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
          (3 3 (:REWRITE REDUCE-INTEGERP-+))
          (3 3 (:REWRITE INTEGERP-MINUS-X))
          (3 3 (:REWRITE |(< y (+ (- c) x))|))
          (3 3 (:REWRITE |(< x (+ c/d y))|))
          (3 3 (:REWRITE |(< 0 (* x y))|))
          (3 3 (:META META-INTEGERP-CORRECT))
          (2 2 (:REWRITE ZP-OPEN))
          (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (2 2
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (2 2
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
          (2 2
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
          (2 2
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (2 2
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (2 2 (:REWRITE |(equal c (/ x))|))
          (2 2 (:REWRITE |(equal c (- x))|))
          (2 2 (:REWRITE |(equal (/ x) c)|))
          (2 2 (:REWRITE |(equal (/ x) (/ y))|))
          (2 2 (:REWRITE |(equal (- x) c)|))
          (2 2 (:REWRITE |(equal (- x) (- y))|))
          (2 2 (:REWRITE |(< 0 (/ x))|))
          (2 2
             (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
          (2 2 (:REWRITE |(* (- x) y)|))
          (1 1
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
          (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
          (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
          (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
          (1 1
             (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
          (1 1 (:REWRITE DEFAULT-FLOOR-2))
          (1 1 (:REWRITE DEFAULT-FLOOR-1))
          (1 1 (:REWRITE |(floor x 2)| . 2))
          (1 1
             (:REWRITE |(<= (/ x) y) with (< x 0)|))
          (1 1
             (:REWRITE |(<= (/ x) y) with (< 0 x)|))
          (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
          (1 1
             (:REWRITE |(< (/ x) y) with (< x 0)|)))
(M1::LOG2-IMPLIES-EXPT-UPPERBOUND-HINT
     (120 120
          (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (120 120
          (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (120 120
          (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (120 120
          (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (81 31 (:REWRITE DEFAULT-PLUS-2))
     (76 23 (:REWRITE DEFAULT-LESS-THAN-1))
     (75 31 (:REWRITE DEFAULT-PLUS-1))
     (67 67 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (39 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
     (28 23 (:REWRITE DEFAULT-LESS-THAN-2))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
     (27 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
     (23 23 (:REWRITE THE-FLOOR-BELOW))
     (23 23 (:REWRITE THE-FLOOR-ABOVE))
     (22 22 (:REWRITE DEFAULT-TIMES-2))
     (22 22 (:REWRITE DEFAULT-TIMES-1))
     (20 17
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (20 17
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (20 15 (:REWRITE |(< (- x) (- y))|))
     (19 6 (:REWRITE DEFAULT-MINUS))
     (17 17
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< c (- x))|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (15 15
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (15 15 (:REWRITE |(< (/ x) (/ y))|))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
     (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
     (15 3
         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
     (14 14 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (14 14
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (14 14 (:REWRITE INTEGERP-<-CONSTANT))
     (14 14 (:REWRITE CONSTANT-<-INTEGERP))
     (13 13
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
     (10 10
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (10 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (+ c/d x) y)|))
     (7 7 (:REWRITE |(< (+ (- c) x) y)|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (6 6 (:TYPE-PRESCRIPTION ABS))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (3 3 (:REWRITE REDUCE-INTEGERP-+))
     (3 3 (:REWRITE INTEGERP-MINUS-X))
     (3 3 (:REWRITE |(< y (+ (- c) x))|))
     (3 3 (:REWRITE |(< x (+ c/d y))|))
     (3 3 (:REWRITE |(< 0 (* x y))|))
     (3 3 (:META META-INTEGERP-CORRECT))
     (2 2 (:REWRITE ZP-OPEN))
     (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (2 2
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (2 2
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (2 2
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (2 2
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (2 2 (:REWRITE |(equal c (/ x))|))
     (2 2 (:REWRITE |(equal c (- x))|))
     (2 2 (:REWRITE |(equal (/ x) c)|))
     (2 2 (:REWRITE |(equal (/ x) (/ y))|))
     (2 2 (:REWRITE |(equal (- x) c)|))
     (2 2 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE |(< 0 (/ x))|))
     (2 2
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
     (2 2 (:REWRITE |(* (- x) y)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (1 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
     (1 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
     (1 1 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
     (1 1
        (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
     (1 1 (:REWRITE DEFAULT-FLOOR-2))
     (1 1 (:REWRITE DEFAULT-FLOOR-1))
     (1 1 (:REWRITE |(floor x 2)| . 2))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< x 0)|))
     (1 1
        (:REWRITE |(<= (/ x) y) with (< 0 x)|))
     (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE |(< (/ x) y) with (< x 0)|)))
(M1::LOG2-IMPLIES-EXPT-UPPERBOUND
 (1223 1223
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1223 1223
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1223 1223
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1223 1223
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1184
  1184
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1184
      1184
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1184
     1184
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1184 1184
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1184 1184
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (721 147
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (597 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (525 34 (:REWRITE DEFAULT-FLOOR-RATIO))
 (497 253 (:REWRITE DEFAULT-PLUS-2))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (464 464
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (433 325 (:REWRITE DEFAULT-TIMES-2))
 (421 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (421 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (418 155 (:REWRITE DEFAULT-LESS-THAN-2))
 (394 46
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (363 21 (:REWRITE ZP-OPEN))
 (331 325 (:REWRITE DEFAULT-TIMES-1))
 (320 122
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (309 122 (:REWRITE SIMPLIFY-SUMS-<))
 (257 253 (:REWRITE DEFAULT-PLUS-1))
 (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (245 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (245 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (245 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (245 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (245 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (245 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (230 46
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (215 21 (:LINEAR EXPT-<=-1-TWO))
 (207 1 (:REWRITE |(floor (if a b c) x)|))
 (200 50 (:REWRITE |(* c (* d x))|))
 (188 188
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (188 188 (:REWRITE NORMALIZE-ADDENDS))
 (164 128
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (163 155 (:REWRITE DEFAULT-LESS-THAN-1))
 (155 155 (:REWRITE THE-FLOOR-BELOW))
 (155 155 (:REWRITE THE-FLOOR-ABOVE))
 (150 147
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (150 147
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 128 (:REWRITE INTEGERP-<-CONSTANT))
 (128 128 (:REWRITE CONSTANT-<-INTEGERP))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< c (- x))|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (128 128
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (128 128 (:REWRITE |(< (/ x) (/ y))|))
 (128 128 (:REWRITE |(< (- x) c)|))
 (128 128 (:REWRITE |(< (- x) (- y))|))
 (124 54 (:REWRITE REDUCE-INTEGERP-+))
 (111 103 (:REWRITE DEFAULT-EXPT-2))
 (103 103 (:REWRITE DEFAULT-EXPT-1))
 (103 103 (:REWRITE |(expt 1/c n)|))
 (103 103 (:REWRITE |(expt (- x) n)|))
 (89 20 (:REWRITE ODD-EXPT-THM))
 (78 6 (:REWRITE |(* (* x y) z)|))
 (70 1 (:REWRITE |(< x (if a b c))|))
 (65 5
     (:REWRITE |(not (equal (* (/ x) y) 1))|))
 (65 5 (:REWRITE |(equal (* (/ x) y) 1)|))
 (54 54 (:REWRITE INTEGERP-MINUS-X))
 (54 54 (:META META-INTEGERP-CORRECT))
 (41 36
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (41 1 (:REWRITE |(* (if a b c) x)|))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (39 35
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (39 35
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (36 36
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (36 36 (:REWRITE |(equal c (/ x))|))
 (36 36 (:REWRITE |(equal c (- x))|))
 (36 36 (:REWRITE |(equal (/ x) c)|))
 (36 36 (:REWRITE |(equal (/ x) (/ y))|))
 (36 36 (:REWRITE |(equal (- x) c)|))
 (36 36 (:REWRITE |(equal (- x) (- y))|))
 (35 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (35 35
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (34 34 (:REWRITE DEFAULT-FLOOR-2))
 (34 34 (:REWRITE DEFAULT-FLOOR-1))
 (34 34 (:REWRITE |(< 0 (/ x))|))
 (34 34 (:REWRITE |(< 0 (* x y))|))
 (33 33 (:REWRITE |(floor x 2)| . 2))
 (31 31 (:REWRITE |(< x (+ c/d y))|))
 (30 30 (:REWRITE |(< (/ x) 0)|))
 (30 30 (:REWRITE |(< (* x y) 0)|))
 (26 1 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (25 25
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (25 5
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (23 21 (:LINEAR EXPT-<-1-TWO))
 (22 1 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (21 21 (:LINEAR EXPT-LINEAR-UPPER-<))
 (21 21 (:LINEAR EXPT-LINEAR-LOWER-<))
 (21 21 (:LINEAR EXPT->=-1-TWO))
 (21 21 (:LINEAR EXPT->-1-TWO))
 (21 21 (:LINEAR EXPT-<=-1-ONE))
 (21 21 (:LINEAR EXPT-<-1-ONE))
 (17 17 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:TYPE-PRESCRIPTION ABS))
 (7 7 (:REWRITE |(floor (+ x r) i)|))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (6 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
 (114 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (93 2 (:LINEAR EXPT-X->=-X))
 (93 2 (:LINEAR EXPT-X->-X))
 (65
  65
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (65 65
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (57 1 (:DEFINITION M1::LOG2))
 (27 18 (:REWRITE DEFAULT-PLUS-2))
 (25 1 (:REWRITE |(floor x 2)| . 1))
 (22 8 (:REWRITE DEFAULT-LESS-THAN-2))
 (18 18 (:REWRITE DEFAULT-PLUS-1))
 (18 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (18 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (16 6 (:REWRITE SIMPLIFY-SUMS-<))
 (14 10 (:REWRITE DEFAULT-EXPT-2))
 (11 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 10 (:REWRITE |(expt 1/c n)|))
 (10 10 (:REWRITE |(expt (- x) n)|))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8 (:REWRITE THE-FLOOR-ABOVE))
 (8 8
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE DEFAULT-TIMES-2))
 (5 5 (:REWRITE DEFAULT-TIMES-1))
 (4 4
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 1 (:REWRITE |(* y x)|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 2 (:LINEAR EXPT-<=-1-TWO))
 (3 2 (:LINEAR EXPT-<-1-TWO))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE DEFAULT-FLOOR-2))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x 2)| . 2))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(M1::MAX-WIDTH1)
(M1::MAX-WIDTH)
(M1::TURING1-4-TUPLE
 (15
   15
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::TURING1-MACHINEP)
(M1::MAKE-CELL
 (18
  18
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (18 18
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::NCONS
 (5
  5
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5 5
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::NCAR
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::NCDR)
(M1::CELLP
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::NCAR-NCONS
 (2180 10 (:REWRITE |(* x (+ y z))|))
 (1761 9 (:REWRITE MOD-ZERO . 3))
 (1616 293 (:REWRITE DEFAULT-TIMES-2))
 (1433 9 (:REWRITE DEFAULT-MOD-RATIO))
 (1400 293 (:REWRITE DEFAULT-TIMES-1))
 (998
  998
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (998 998
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (998
     998
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (998 998
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (953 9 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (710 9 (:REWRITE MOD-X-Y-=-X . 4))
 (668 2 (:LINEAR MOD-BOUNDS-3))
 (553 9 (:REWRITE MOD-ZERO . 4))
 (408 152 (:REWRITE DEFAULT-PLUS-1))
 (395 152 (:REWRITE DEFAULT-PLUS-2))
 (320 32 (:REWRITE DEFAULT-DIVIDE))
 (261 9 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (238 238
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (238 238
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (238 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (238 34 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (238 34 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (225 9 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (225 9 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (214 34
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (214 34
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (210 21
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (210 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (174 21 (:REWRITE SIMPLIFY-SUMS-<))
 (172 4 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (172 4
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (138 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (136 4 (:REWRITE MOD-X-Y-=-X . 2))
 (112 76 (:REWRITE DEFAULT-MINUS))
 (100 4 (:LINEAR MOD-BOUNDS-2))
 (93 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (90 9 (:REWRITE DEFAULT-MOD-2))
 (81 9 (:REWRITE ODD-EXPT-THM))
 (46 46
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (45 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (45 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (45 9 (:REWRITE DEFAULT-MOD-1))
 (39 39 (:REWRITE DEFAULT-EXPT-2))
 (39 39 (:REWRITE DEFAULT-EXPT-1))
 (39 39 (:REWRITE |(expt 1/c n)|))
 (39 39 (:REWRITE |(expt (- x) n)|))
 (39 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (34 34 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (34 34
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (34 34 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (34 34
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (18 18 (:REWRITE REDUCE-INTEGERP-+))
 (18 18 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:META META-INTEGERP-CORRECT))
 (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (7 7 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4 (:REWRITE |(< y (+ (- c) x))|))
 (4 4 (:REWRITE |(< x (+ c/d y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NCDR-NCONS
 (762 4 (:REWRITE |(* x (+ y z))|))
 (482 4 (:REWRITE |(* y (* x z))|))
 (468 90 (:REWRITE DEFAULT-TIMES-2))
 (429 90 (:REWRITE DEFAULT-TIMES-1))
 (377 2 (:REWRITE FLOOR-=-X/Y . 3))
 (367 1 (:REWRITE FLOOR-ZERO . 3))
 (365 2 (:REWRITE FLOOR-=-X/Y . 2))
 (322 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (295
  295
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (295 295
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (295
     295
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (295 295
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (232 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (157 2 (:REWRITE FLOOR-ZERO . 5))
 (136 55 (:REWRITE DEFAULT-PLUS-2))
 (134 55 (:REWRITE DEFAULT-PLUS-1))
 (107 1 (:REWRITE |(floor (+ x r) i)|))
 (100 10 (:REWRITE DEFAULT-DIVIDE))
 (82 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (76 13 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (73 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (59 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (55 10 (:REWRITE SIMPLIFY-SUMS-<))
 (50 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (50 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (46 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (46 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (36 27 (:REWRITE DEFAULT-MINUS))
 (28 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (21 3 (:REWRITE ODD-EXPT-THM))
 (20 2 (:REWRITE DEFAULT-FLOOR-2))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (19 19 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (19 19
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (19 19
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (19 1
     (:REWRITE |(* (expt x m) (expt x n))|))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (11 2 (:REWRITE DEFAULT-FLOOR-1))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE |(< (/ x) 0)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::CELLP-MAKE-CELL
 (3808
  3808
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3808
      3808
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3808
     3808
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3808 3808
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3808 3808
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1076 35 (:REWRITE ODD-EXPT-THM))
 (916 122 (:REWRITE DEFAULT-PLUS-2))
 (761 247
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (658 235
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (658 235
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (631 235 (:REWRITE SIMPLIFY-SUMS-<))
 (562 247 (:REWRITE DEFAULT-LESS-THAN-2))
 (527 122 (:REWRITE DEFAULT-PLUS-1))
 (443 239 (:REWRITE CONSTANT-<-INTEGERP))
 (355 247 (:REWRITE DEFAULT-LESS-THAN-1))
 (348 8 (:LINEAR EXPT-X->=-X))
 (348 8 (:LINEAR EXPT-X->-X))
 (308 308 (:REWRITE DEFAULT-CDR))
 (292 8 (:LINEAR EXPT-<=-1-TWO))
 (284 8 (:LINEAR EXPT->-1-ONE))
 (247 247 (:REWRITE THE-FLOOR-BELOW))
 (247 247 (:REWRITE THE-FLOOR-ABOVE))
 (239 239
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (239 239
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (239 239
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (239 239
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (239 239
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (239 239
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (239 239 (:REWRITE |(< c (- x))|))
 (239 239
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (239 239
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (239 239
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (239 239
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (239 239 (:REWRITE |(< (/ x) (/ y))|))
 (239 239 (:REWRITE |(< (- x) c)|))
 (239 239 (:REWRITE |(< (- x) (- y))|))
 (235 235
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (235 235 (:REWRITE INTEGERP-<-CONSTANT))
 (228 228 (:REWRITE DEFAULT-CAR))
 (215 215 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (177 42 (:REWRITE DEFAULT-TIMES-1))
 (100 100
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (100 100
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (100 100 (:REWRITE |(< (/ x) 0)|))
 (100 100 (:REWRITE |(< (* x y) 0)|))
 (99 99 (:REWRITE REDUCE-INTEGERP-+))
 (99 99 (:REWRITE INTEGERP-MINUS-X))
 (99 99 (:META META-INTEGERP-CORRECT))
 (88 8 (:REWRITE |(* y (* x z))|))
 (87 87 (:REWRITE |arith (expt x c)|))
 (82 82
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (82 82 (:REWRITE NORMALIZE-ADDENDS))
 (78 78 (:REWRITE |arith (expt 1/c n)|))
 (74 42 (:REWRITE DEFAULT-TIMES-2))
 (56 56 (:REWRITE DEFAULT-EXPT-2))
 (56 56 (:REWRITE DEFAULT-EXPT-1))
 (56 56 (:REWRITE |(expt 1/c n)|))
 (56 56 (:REWRITE |(expt (- x) n)|))
 (55 55 (:REWRITE |arith (* c (* d x))|))
 (54 27
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (54 27
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (54 27 (:DEFINITION TRUE-LISTP))
 (52 52 (:REWRITE |(< 0 (* x y))|))
 (48 48
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (48 48
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (48 48 (:REWRITE |(< 0 (/ x))|))
 (27 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (27 27
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (27 27
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (27 27 (:REWRITE |(equal c (/ x))|))
 (27 27 (:REWRITE |(equal c (- x))|))
 (27 27 (:REWRITE |(equal (/ x) c)|))
 (27 27 (:REWRITE |(equal (/ x) (/ y))|))
 (27 27 (:REWRITE |(equal (- x) c)|))
 (27 27 (:REWRITE |(equal (- x) (- y))|))
 (26 26
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (24 24 (:REWRITE |arith (* (- x) y)|))
 (21 21 (:REWRITE |arith (- (* c x))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:TYPE-PRESCRIPTION ABS))
 (8 8 (:REWRITE |(* a (/ a) b)|))
 (8 8
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< x 0)|))
 (4 4 (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |arith (+ c (+ d x))|)))
(M1::NCDR-DECREASES
 (455 13 (:REWRITE DEFAULT-PLUS-1))
 (454 13 (:REWRITE DEFAULT-PLUS-2))
 (217 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (207 1 (:REWRITE FLOOR-ZERO . 4))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (177 177
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (177 177
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (164 1 (:REWRITE FLOOR-ZERO . 3))
 (152 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (145 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (118 1 (:REWRITE CANCEL-FLOOR-+))
 (117
  117
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (117 117
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (117
     117
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (117 117
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (115 21 (:REWRITE DEFAULT-TIMES-2))
 (104 8
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (104 8
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (104 8
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (76 1 (:REWRITE FLOOR-=-X/Y . 3))
 (70 1 (:REWRITE FLOOR-=-X/Y . 2))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (56 8 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (49 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (46 2 (:LINEAR EXPT-X->-X))
 (46 2 (:LINEAR EXPT->-1-ONE))
 (41 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (34 7 (:REWRITE DEFAULT-LESS-THAN-1))
 (31 8 (:REWRITE |(* (- x) y)|))
 (31 1 (:REWRITE |(integerp (- x))|))
 (28 2 (:LINEAR EXPT-X->=-X))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (25 16 (:REWRITE DEFAULT-MINUS))
 (25 7 (:REWRITE DEFAULT-LESS-THAN-2))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (23 5 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE DEFAULT-TIMES-1))
 (17 17 (:REWRITE DEFAULT-EXPT-2))
 (17 17 (:REWRITE DEFAULT-EXPT-1))
 (17 17 (:REWRITE |(expt 1/c n)|))
 (17 17 (:REWRITE |(expt (- x) n)|))
 (16 16
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (16 1 (:REWRITE FLOOR-ZERO . 5))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (10 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (8 8 (:REWRITE THE-FLOOR-BELOW))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (7 7
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:META META-INTEGERP-CORRECT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (1 1
    (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (1 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(M1::NATP-NCDR
 (217 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (207 1 (:REWRITE FLOOR-ZERO . 4))
 (180 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (164 1 (:REWRITE FLOOR-ZERO . 3))
 (118 1 (:REWRITE CANCEL-FLOOR-+))
 (85 5 (:REWRITE |(/ (expt x n))|))
 (79
  79
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (79 79
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (79 79
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (79 79
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (79 79
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 1 (:REWRITE FLOOR-=-X/Y . 3))
 (70 1 (:REWRITE FLOOR-=-X/Y . 2))
 (68 14 (:REWRITE DEFAULT-TIMES-2))
 (50 5 (:REWRITE DEFAULT-DIVIDE))
 (49 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (46 2 (:LINEAR EXPT-X->-X))
 (46 2 (:LINEAR EXPT->-1-ONE))
 (46 1 (:REWRITE FLOOR-ZERO . 5))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (36 36
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (33 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (31 1 (:REWRITE |(integerp (- x))|))
 (30 7 (:REWRITE |(* (- x) y)|))
 (28 2 (:LINEAR EXPT-X->=-X))
 (28 2 (:LINEAR EXPT->=-1-ONE))
 (25 1 (:REWRITE FLOOR-ZERO . 2))
 (25 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (25 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (24 6 (:REWRITE SIMPLIFY-SUMS-<))
 (24 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (23 14 (:REWRITE DEFAULT-MINUS))
 (19 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (16 1
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (16 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (16 1
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (16 1
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (15 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (14 14 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:REWRITE DEFAULT-EXPT-2))
 (14 14 (:REWRITE DEFAULT-EXPT-1))
 (14 14 (:REWRITE |(expt 1/c n)|))
 (14 14 (:REWRITE |(expt (- x) n)|))
 (13 13
     (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 1
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (13 1
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (13 1
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE DEFAULT-PLUS-2))
 (7 7 (:REWRITE DEFAULT-PLUS-1))
 (7 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (7 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (7 1
    (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2 2 (:REWRITE ODD-EXPT-THM))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-FLOOR-1))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|)))
(M1::POSITIVE-NATP-NCONS
 (2
  2
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(M1::NST-IN
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (10 10
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-3))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)))
(M1::NSYM (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
          (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
          (25 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
          (25 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
          (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
          (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
          (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
          (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
          (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
          (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(M1::NOP
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (35 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (22 22
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (22 22
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(M1::NST-OUT
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (35 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (35 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (22 22
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (22 22
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (4
   4
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1)))
(M1::NNIL (10 5
              (:TYPE-PRESCRIPTION M1::CELLP-MAKE-CELL))
          (5 5 (:TYPE-PRESCRIPTION NATP)))
(M1::NCODE (8 4
              (:TYPE-PRESCRIPTION M1::CELLP-MAKE-CELL)))
(M1::POSITIVE-NATP-NNIL
 (88 16 (:REWRITE DEFAULT-TIMES-2))
 (72 16 (:REWRITE DEFAULT-TIMES-1))
 (62 26 (:REWRITE DEFAULT-PLUS-2))
 (44 26 (:REWRITE DEFAULT-PLUS-1))
 (35
  35
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (35 35
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (14 7
     (:TYPE-PRESCRIPTION M1::CELLP-MAKE-CELL))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (11 2
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (11 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (11 2 (:REWRITE DEFAULT-LESS-THAN-2))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE THE-FLOOR-BELOW))
 (2 2 (:REWRITE THE-FLOOR-ABOVE))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (2 2 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2 2
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2 2
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (2 2 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2 2 (:REWRITE INTEGERP-<-CONSTANT))
 (2 2 (:REWRITE DEFAULT-LESS-THAN-1))
 (2 2 (:REWRITE CONSTANT-<-INTEGERP))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< c (- x))|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2 2
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2 2 (:REWRITE |(< (/ x) (/ y))|))
 (2 2 (:REWRITE |(< (- x) c)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE ODD-EXPT-THM))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:META META-INTEGERP-CORRECT)))
(M1::POSITIVE-NATP-NCODE
 (8928 60 (:REWRITE |(+ x (if a b c))|))
 (6394 636 (:REWRITE DEFAULT-PLUS-2))
 (6210 78 (:REWRITE |(+ (if a b c) x)|))
 (3672 630 (:REWRITE DEFAULT-PLUS-1))
 (1641
  1641
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1641
      1641
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1641
     1641
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1641 1641
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1641 1641
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1060 106 (:REWRITE DEFAULT-TIMES-2))
 (840 30 (:REWRITE ODD-EXPT-THM))
 (624 48 (:REWRITE ACL2-NUMBERP-X))
 (528 88 (:REWRITE DEFAULT-TIMES-1))
 (471 171
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (471 171
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (471 171 (:REWRITE DEFAULT-LESS-THAN-2))
 (432 171 (:REWRITE SIMPLIFY-SUMS-<))
 (263 263 (:REWRITE DEFAULT-CDR))
 (216 216
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (216 216 (:REWRITE NORMALIZE-ADDENDS))
 (204 204 (:REWRITE DEFAULT-CAR))
 (192 48 (:REWRITE RATIONALP-X))
 (192 48
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (176 176 (:REWRITE REDUCE-INTEGERP-+))
 (176 176 (:REWRITE INTEGERP-MINUS-X))
 (176 176 (:META META-INTEGERP-CORRECT))
 (171 171 (:REWRITE THE-FLOOR-BELOW))
 (171 171 (:REWRITE THE-FLOOR-ABOVE))
 (171 171
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (171 171
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (171 171
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (171 171
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (171 171 (:REWRITE INTEGERP-<-CONSTANT))
 (171 171 (:REWRITE DEFAULT-LESS-THAN-1))
 (171 171 (:REWRITE CONSTANT-<-INTEGERP))
 (171 171
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (171 171
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (171 171
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (171 171
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (171 171 (:REWRITE |(< c (- x))|))
 (171 171
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (171 171
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (171 171
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (171 171
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (171 171 (:REWRITE |(< (/ x) (/ y))|))
 (171 171 (:REWRITE |(< (- x) c)|))
 (171 171 (:REWRITE |(< (- x) (- y))|))
 (165 165 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (91 91 (:REWRITE DEFAULT-EXPT-2))
 (91 91 (:REWRITE DEFAULT-EXPT-1))
 (91 91 (:REWRITE |(expt 1/c n)|))
 (91 91 (:REWRITE |(expt (- x) n)|))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (72 72
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (72 72 (:REWRITE |(< (/ x) 0)|))
 (72 72 (:REWRITE |(< (* x y) 0)|))
 (62 2 (:LINEAR EXPT-<=-1-TWO))
 (60 2 (:LINEAR EXPT->-1-ONE))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:META META-RATIONALP-CORRECT))
 (42 42 (:REWRITE FOLD-CONSTS-IN-+))
 (40 20 (:DEFINITION TRUE-LISTP))
 (38 19
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (38 19
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (37 37
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (37 37 (:REWRITE |(< 0 (/ x))|))
 (37 37 (:REWRITE |(< 0 (* x y))|))
 (19 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (19 19
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (19 19
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (19 19 (:REWRITE |(equal c (/ x))|))
 (19 19 (:REWRITE |(equal c (- x))|))
 (19 19 (:REWRITE |(equal (/ x) c)|))
 (19 19 (:REWRITE |(equal (/ x) (/ y))|))
 (19 19 (:REWRITE |(equal (- x) c)|))
 (19 19 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE)))
(M1::NST-IN-MAKE-CELL
 (52464 24 (:LINEAR M1::CELLP-MAKE-CELL))
 (35712 240 (:REWRITE |(+ x (if a b c))|))
 (24840 312 (:REWRITE |(+ (if a b c) x)|))
 (23204 2029 (:REWRITE DEFAULT-PLUS-2))
 (18249 8 (:REWRITE MOD-ZERO . 4))
 (13621 2005 (:REWRITE DEFAULT-PLUS-1))
 (10222 8 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (9644 8 (:REWRITE MOD-X-Y-=-X . 4))
 (9227 8 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (6325
  6325
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6325
      6325
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6325
     6325
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6325 6325
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6325 6325
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2555 373 (:REWRITE DEFAULT-TIMES-2))
 (2150 12 (:REWRITE |(* x (+ y z))|))
 (2085 8 (:REWRITE MOD-ZERO . 3))
 (2042 301 (:REWRITE DEFAULT-TIMES-1))
 (1627 8 (:REWRITE DEFAULT-MOD-RATIO))
 (537 537
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (406 58 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (406 58 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (353 7 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (353 7
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (343 41
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (343 41 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (310 31 (:REWRITE DEFAULT-DIVIDE))
 (290 7 (:REWRITE MOD-X-Y-=-X . 2))
 (268 43 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (265 41 (:REWRITE SIMPLIFY-SUMS-<))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (260 260
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (260 260
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (260 260
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (253 8 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (253 8 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (216 2 (:LINEAR MOD-BOUNDS-3))
 (211 41 (:REWRITE DEFAULT-LESS-THAN-2))
 (192 192 (:REWRITE ACL2-NUMBERP-X))
 (188 12 (:REWRITE ODD-EXPT-THM))
 (173 41 (:REWRITE DEFAULT-LESS-THAN-1))
 (170 170 (:REWRITE DEFAULT-CDR))
 (161 62 (:REWRITE DEFAULT-MINUS))
 (157 157 (:REWRITE FOLD-CONSTS-IN-+))
 (122 40
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (118 58
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (118 58
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (113 113 (:REWRITE DEFAULT-CAR))
 (112 112 (:REWRITE DEFAULT-EXPT-2))
 (112 112 (:REWRITE DEFAULT-EXPT-1))
 (112 112 (:REWRITE |(expt 1/c n)|))
 (112 112 (:REWRITE |(expt (- x) n)|))
 (108 4 (:LINEAR MOD-BOUNDS-2))
 (80 24 (:META META-INTEGERP-CORRECT))
 (80 8 (:REWRITE DEFAULT-MOD-2))
 (72 9
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (72 9
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (72 4
     (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (72 4 (:REWRITE MOD-CANCEL-*-CONST))
 (72 4
     (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (72 4
     (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (70 8 (:REWRITE DEFAULT-MOD-1))
 (63 63
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (63 63
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (63 63
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (63 63
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (58 58 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (58 58
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (58 58 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (58 58
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (48 48 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (48 48 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (41 41 (:REWRITE THE-FLOOR-BELOW))
 (41 41 (:REWRITE THE-FLOOR-ABOVE))
 (41 41
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (41 41
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (41 41
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (41 41
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (31 31 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (18 18 (:REWRITE |(* c (* d x))|))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 9
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (9 9
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (9 9 (:REWRITE |(equal c (/ x))|))
 (9 9 (:REWRITE |(equal c (- x))|))
 (9 9 (:REWRITE |(equal (/ x) c)|))
 (9 9 (:REWRITE |(equal (/ x) (/ y))|))
 (9 9 (:REWRITE |(equal (- x) c)|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (7 1 (:DEFINITION LEN))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (4 4 (:REWRITE |(mod x (- y))| . 3))
 (4 4 (:REWRITE |(mod x (- y))| . 2))
 (4 4 (:REWRITE |(mod x (- y))| . 1))
 (4 4
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (4 4 (:REWRITE |(mod (- x) y)| . 3))
 (4 4 (:REWRITE |(mod (- x) y)| . 2))
 (4 4 (:REWRITE |(mod (- x) y)| . 1))
 (4 4
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::NSYM-MAKE-CELL
 (2039 328 (:REWRITE DEFAULT-TIMES-2))
 (1819 328 (:REWRITE DEFAULT-TIMES-1))
 (1744 3 (:REWRITE FLOOR-ZERO . 3))
 (1617 4 (:REWRITE FLOOR-=-X/Y . 3))
 (1564 4 (:REWRITE FLOOR-=-X/Y . 2))
 (1387 4 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1245
  1245
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1245
      1245
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1245
     1245
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1245 1245
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1245 1245
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1029 230 (:REWRITE DEFAULT-PLUS-2))
 (934 4 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (804 230 (:REWRITE DEFAULT-PLUS-1))
 (586 4 (:REWRITE FLOOR-ZERO . 5))
 (514 3 (:REWRITE |(floor (+ x r) i)|))
 (422 71 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (362 35 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (296 35
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (273 273
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (273 273
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (273 273
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (260 52 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (260 52 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (260 52
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (260 52
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (240 24 (:REWRITE DEFAULT-DIVIDE))
 (236 35 (:REWRITE DEFAULT-LESS-THAN-1))
 (215 35 (:REWRITE SIMPLIFY-SUMS-<))
 (199 4 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (176 8 (:REWRITE ODD-EXPT-THM))
 (161 35 (:REWRITE DEFAULT-LESS-THAN-2))
 (145 4 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (145 4 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (140 28 (:META META-INTEGERP-CORRECT))
 (123 5 (:REWRITE DEFAULT-MOD-RATIO))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (122 122
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (120 3 (:REWRITE FLOOR-ZERO . 2))
 (101 62 (:REWRITE DEFAULT-MINUS))
 (90 6
     (:REWRITE |(* (expt x m) (expt x n))|))
 (62 2 (:LINEAR EXPT-<=-1-TWO))
 (60 60
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (60 2 (:LINEAR EXPT->-1-ONE))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (58 58 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (58 4 (:REWRITE DEFAULT-FLOOR-1))
 (54 2 (:LINEAR MOD-BOUNDS-3))
 (52 52 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (52 52
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (52 52 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (52 52
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (52 52 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (52 2 (:LINEAR EXPT-X->=-X))
 (52 2 (:LINEAR EXPT-X->-X))
 (43 43
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (43 43
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (40 4 (:REWRITE DEFAULT-FLOOR-2))
 (36 36 (:REWRITE DEFAULT-EXPT-2))
 (36 36 (:REWRITE DEFAULT-EXPT-1))
 (36 36 (:REWRITE |(expt 1/c n)|))
 (36 36 (:REWRITE |(expt (- x) n)|))
 (35 35 (:REWRITE THE-FLOOR-BELOW))
 (35 35 (:REWRITE THE-FLOOR-ABOVE))
 (35 35
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (35 35
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (35 35
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (35 35
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (35 35 (:REWRITE INTEGERP-<-CONSTANT))
 (35 35 (:REWRITE CONSTANT-<-INTEGERP))
 (35 35
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (35 35
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (35 35
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (35 35
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (35 35 (:REWRITE |(< c (- x))|))
 (35 35
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (35 35
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (35 35
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (35 35
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (35 35 (:REWRITE |(< (/ x) (/ y))|))
 (35 35 (:REWRITE |(< (- x) c)|))
 (35 35 (:REWRITE |(< (- x) (- y))|))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (27 27 (:REWRITE DEFAULT-CDR))
 (25 25 (:REWRITE FOLD-CONSTS-IN-+))
 (24 4 (:LINEAR MOD-BOUNDS-2))
 (20 20 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (17 17 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE |(< (+ c/d x) y)|))
 (11 11 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (9 5 (:REWRITE DEFAULT-MOD-1))
 (8 8 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (7 1 (:DEFINITION LEN))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE DEFAULT-MOD-2))
 (5 5 (:REWRITE |(mod x 2)| . 2))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4A-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (4 4
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (4 4
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (4 3
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 3
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (2 2 (:LINEAR EXPT-LINEAR-UPPER-<))
 (2 2 (:LINEAR EXPT-LINEAR-LOWER-<))
 (2 2 (:LINEAR EXPT->=-1-TWO))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<=-1-ONE))
 (2 2 (:LINEAR EXPT-<-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::NOP-MAKE-CELL
 (87982 52 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (84047 84047
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (84047 84047
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (83736 1119 (:REWRITE DEFAULT-PLUS-2))
 (54644 50 (:REWRITE MOD-X-Y-=-X . 4))
 (53543 3057 (:REWRITE DEFAULT-TIMES-2))
 (48528 3744
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (38048 1119 (:REWRITE DEFAULT-PLUS-1))
 (34161 3801
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (34161 3801
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (33648 3744
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (33434 50 (:REWRITE FLOOR-ZERO . 3))
 (28141 52 (:REWRITE MOD-ZERO . 4))
 (26523
  26523
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (26523
      26523
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (26523
     26523
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (26523 26523
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (26523 26523
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (19005 3801
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (19005 3801
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (19005 3801
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (19005 3801
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (18720 3744
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (18720 3744
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (18720 3744
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (18720 3744
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (18296 21 (:REWRITE MOD-X-I*J))
 (15827 3057 (:REWRITE DEFAULT-TIMES-1))
 (15409 53 (:REWRITE DEFAULT-MOD-RATIO))
 (15154 75 (:REWRITE |(* x (+ y z))|))
 (14240 56 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (13501 321 (:META META-INTEGERP-CORRECT))
 (12468 12468
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (12468 12468
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (12024 12024
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (11646 56 (:REWRITE FLOOR-=-X/Y . 2))
 (11115 56 (:REWRITE FLOOR-=-X/Y . 3))
 (10880 128 (:REWRITE |(integerp (expt x n))|))
 (9892 4510
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (8952 814 (:REWRITE DEFAULT-MINUS))
 (8170 1044 (:REWRITE DEFAULT-LESS-THAN-1))
 (8081 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (7756 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (7756 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (7649 1532
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (7566 56 (:REWRITE DEFAULT-FLOOR-RATIO))
 (7390 739 (:REWRITE DEFAULT-DIVIDE))
 (6841 225 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (6700 1340 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (6700 1340 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (6642 1027 (:REWRITE |(< (- x) c)|))
 (6608 1340
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6468 85
       (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
 (5729 1037
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5455 140 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (4845 1088 (:REWRITE THE-FLOOR-BELOW))
 (4814 4814 (:REWRITE |arith (expt x c)|))
 (4814 4814 (:REWRITE |arith (expt 1/c n)|))
 (4669 1044 (:REWRITE DEFAULT-LESS-THAN-2))
 (4608 52 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (4510 4510
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (4510 4510
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (4463 32 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (4463 32
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4346 32 (:REWRITE MOD-X-Y-=-X . 2))
 (3558 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (3558 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (3438 56 (:REWRITE FLOOR-ZERO . 5))
 (3077 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4D-EXPT))
 (3077 633
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (2623 52 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (2623 52 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (2561 829 (:REWRITE SIMPLIFY-SUMS-<))
 (2552 2552 (:REWRITE |arith (* c (* d x))|))
 (2411 53 (:REWRITE DEFAULT-MOD-1))
 (2206 1 (:REWRITE |(* (if a b c) x)|))
 (2035 30
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1781 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-B))
 (1659 255 (:LINEAR EXPT-<-1-TWO))
 (1658 78 (:LINEAR MOD-BOUNDS-2))
 (1556 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4G-EXPT-B))
 (1556 1556
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-B))
 (1340 1340 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (1340 1340
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (1340 1340
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (1340 1340
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (1329 1329
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (1157 788
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (1157 788
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (1154 255 (:LINEAR EXPT->-1-ONE))
 (1108 1037
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1108 1037
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1072 56 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1067 3 (:REWRITE |(floor (+ x r) i)|))
 (1033 1033
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1033 1033
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1033 1033
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1033 1033
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1033 1033
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1033 1033
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1033 1033
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1033 1033
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1033 1033 (:REWRITE |(< (/ x) (/ y))|))
 (1033 1033 (:REWRITE |(< (- x) (- y))|))
 (1030 255 (:LINEAR EXPT-X->=-X))
 (1030 255 (:LINEAR EXPT-X->-X))
 (1027 1027 (:REWRITE |(< c (- x))|))
 (991 56 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (991 56 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (966 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3F-EXPT-B))
 (966 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1F-EXPT-B))
 (930 930 (:REWRITE |arith (* (- x) y)|))
 (926 845
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (845 845 (:REWRITE INTEGERP-<-CONSTANT))
 (845 845 (:REWRITE CONSTANT-<-INTEGERP))
 (835 50 (:REWRITE FLOOR-ZERO . 2))
 (788 788
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (741 47
      (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (739 30 (:REWRITE MOD-CANCEL-*-CONST))
 (727 18
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (697 697 (:REWRITE |arith (- (* c x))|))
 (633 633
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2F-EXPT-B))
 (584 584 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (510 510
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (510 510
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (510 510
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (501 48 (:REWRITE FLOOR-CANCEL-*-CONST))
 (495 13 (:REWRITE FLOOR-=-X/Y . 4))
 (485 485 (:REWRITE |(< 0 (* x y))|))
 (477 477
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (477 477
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (424 424 (:REWRITE DEFAULT-EXPT-2))
 (424 424 (:REWRITE DEFAULT-EXPT-1))
 (421 421 (:REWRITE |(expt 1/c n)|))
 (421 421 (:REWRITE |(expt (- x) n)|))
 (408 48
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (408 48
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (408 48
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (408 21 (:REWRITE MOD-X-I*J-V2))
 (394 47
      (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (384 12 (:REWRITE FLOOR-POSITIVE . 3))
 (371 56 (:REWRITE DEFAULT-FLOOR-2))
 (366 366
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (324 12 (:REWRITE FLOOR-POSITIVE . 2))
 (324 12 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (321 321 (:REWRITE REDUCE-INTEGERP-+))
 (276 12 (:REWRITE FLOOR-POSITIVE . 4))
 (276 12 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (276 12 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (255 255
      (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
               . 1))
 (255 255 (:LINEAR EXPT-LINEAR-UPPER-<))
 (255 255 (:LINEAR EXPT-LINEAR-LOWER-<))
 (255 255 (:LINEAR EXPT->=-1-TWO))
 (255 255 (:LINEAR EXPT->-1-TWO))
 (255 255 (:LINEAR EXPT-<=-1-ONE))
 (255 255 (:LINEAR EXPT-<-1-ONE))
 (242 53 (:REWRITE DEFAULT-MOD-2))
 (202 202 (:REWRITE |(< (/ x) 0)|))
 (202 202 (:REWRITE |(< (* x y) 0)|))
 (187 18
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (182 13
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (171 171 (:REWRITE DEFAULT-CDR))
 (168 24
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (150 5 (:REWRITE |(floor x 2)| . 2))
 (149 149 (:TYPE-PRESCRIPTION ABS))
 (141 48
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (141 48
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (137 56 (:REWRITE DEFAULT-FLOOR-1))
 (130 130 (:REWRITE FOLD-CONSTS-IN-+))
 (92 85
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (85 85
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (85 85
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (85 85 (:REWRITE |(equal c (/ x))|))
 (85 85 (:REWRITE |(equal c (- x))|))
 (85 85 (:REWRITE |(equal (/ x) c)|))
 (85 85 (:REWRITE |(equal (/ x) (/ y))|))
 (85 85 (:REWRITE |(equal (- x) c)|))
 (85 85 (:REWRITE |(equal (- x) (- y))|))
 (76 76 (:REWRITE DEFAULT-CAR))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (53 53 (:REWRITE |(< (+ c/d x) y)|))
 (49 49 (:REWRITE |(< (+ (- c) x) y)|))
 (48 48 (:REWRITE |(floor x (- y))| . 2))
 (48 48 (:REWRITE |(floor x (- y))| . 1))
 (48 48
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (48 48 (:REWRITE |(floor (- x) y)| . 2))
 (48 48 (:REWRITE |(floor (- x) y)| . 1))
 (44 2 (:REWRITE SUM-IS-EVEN . 2))
 (41 41 (:REWRITE |arith (+ c (+ d x))|))
 (36 36 (:REWRITE |(equal (+ (- c) x) y)|))
 (30 30
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (24 24
     (:REWRITE ARITH-BUBBLE-DOWN-*-MATCH-3))
 (23 23 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (21 21
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (21 21
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (18 18 (:REWRITE |(mod x (- y))| . 3))
 (18 18 (:REWRITE |(mod x (- y))| . 2))
 (18 18 (:REWRITE |(mod x (- y))| . 1))
 (18 18
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (18 18 (:REWRITE |(mod (- x) y)| . 3))
 (18 18 (:REWRITE |(mod (- x) y)| . 2))
 (18 18 (:REWRITE |(mod (- x) y)| . 1))
 (18 18
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (13 13
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (12 12 (:REWRITE FLOOR-ZERO . 1))
 (12 12 (:REWRITE FLOOR-POSITIVE . 1))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 5))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 4))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 3))
 (12 12 (:REWRITE |(mod (floor x y) z)| . 2))
 (10 10 (:REWRITE |(* a (/ a) b)|))
 (5 5 (:REWRITE |(floor x 2)| . 1))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (4 4
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (4 4
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (3 3 (:REWRITE |(equal (* x y) 0)|))
 (2 2 (:REWRITE SUM-IS-EVEN . 1))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2)))
(M1::NST-OUT-MAKE-CELL
 (250197 168 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (231628 2698 (:REWRITE DEFAULT-PLUS-2))
 (222449 222449
         (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (222449 222449
         (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (126348 164 (:REWRITE MOD-X-Y-=-X . 4))
 (120703 9307
         (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (113314 7525 (:REWRITE DEFAULT-TIMES-2))
 (105290 2698 (:REWRITE DEFAULT-PLUS-1))
 (89564
  89564
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (89564
      89564
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (89564
     89564
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (89564 89564
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (89564 89564
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (83955 9339
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (83955 9339
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (83667 9307
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (77180 106 (:REWRITE CANCEL-MOD-+))
 (67365 168 (:REWRITE MOD-ZERO . 4))
 (54564 52 (:REWRITE MOD-X-I*J))
 (46695 9339
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (46695 9339
        (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (46695 9339
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (46695 9339
        (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (46535 9307
        (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (46535 9307
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (46535 9307
        (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (46535 9307
        (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (44992 7525 (:REWRITE DEFAULT-TIMES-1))
 (40963 171 (:REWRITE DEFAULT-MOD-RATIO))
 (38450 6414 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (38450 6414 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (38234 6414
        (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (32145 32145
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (32145 32145
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (31653 31653
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (29782 777 (:META META-INTEGERP-CORRECT))
 (28560 336 (:REWRITE |(integerp (expt x n))|))
 (27665 2921 (:REWRITE DEFAULT-LESS-THAN-1))
 (23526 136 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (22924 136 (:REWRITE FLOOR-=-X/Y . 2))
 (22667 11498
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (21763 136 (:REWRITE FLOOR-=-X/Y . 3))
 (21178 21178 (:REWRITE |arith (expt x c)|))
 (20453 20453 (:REWRITE |arith (expt 1/c n)|))
 (20069 4664
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (19619 4639
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (19536 4664
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (18800 1880 (:REWRITE DEFAULT-DIVIDE))
 (18469 2169 (:REWRITE DEFAULT-MINUS))
 (17858 692 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (17696 74 (:REWRITE |(integerp (- x))|))
 (17461 17461
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (17461 17461
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (15858 2758 (:REWRITE |(< (- x) c)|))
 (14658 2921 (:REWRITE DEFAULT-LESS-THAN-2))
 (13425 136 (:REWRITE DEFAULT-FLOOR-RATIO))
 (12357 168 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (11931 11931 (:REWRITE |arith (* c (* d x))|))
 (11893 106
        (:REWRITE |(mod (+ x (mod a b)) y)|))
 (11893 106
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (11863 3023 (:REWRITE THE-FLOOR-BELOW))
 (11651 11498
        (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (11651 11498
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (11047 106 (:REWRITE MOD-X-Y-=-X . 2))
 (10319 2901
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10211 2204 (:REWRITE SIMPLIFY-SUMS-<))
 (9582 2026
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3D-EXPT))
 (9582 2026
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2D-EXPT))
 (9582 2026
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1D-EXPT))
 (8780 310 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (7813 168 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (7813 168 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (6630 4
       (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (6583 5 (:REWRITE |(* (if a b c) x)|))
 (6414 6414
       (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (6414 6414
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (6205 1321 (:REWRITE |(< 0 (/ x))|))
 (5931 171 (:REWRITE DEFAULT-MOD-1))
 (5915 136 (:REWRITE FLOOR-ZERO . 5))
 (5729 5729 (:REWRITE |arith (* (- x) y)|))
 (5614 5614 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (5602 5602
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5025 2824 (:REWRITE |(< (- x) (- y))|))
 (4762 3736
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (4639 7 (:REWRITE |(floor (+ x r) i)|))
 (4103 3734
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-B))
 (3762 2334 (:REWRITE CONSTANT-<-INTEGERP))
 (3743 3743
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4G-EXPT-B))
 (3736 3736
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (3734 3734
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-B))
 (3697 1079 (:LINEAR EXPT-<-1-TWO))
 (3559 1079 (:LINEAR EXPT-X->=-X))
 (3559 1079 (:LINEAR EXPT-X->-X))
 (3375 2306 (:REWRITE INTEGERP-<-CONSTANT))
 (3224 3224
       (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (3127 1079 (:LINEAR EXPT->-1-ONE))
 (3086 248 (:REWRITE |(equal (- x) (- y))|))
 (3040 2828
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2995 4
       (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (2960 130 (:LINEAR MOD-BOUNDS-2))
 (2828 2828
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (2824 2824
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (2824 2824
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (2824 2824
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (2824 2824
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (2824 2824
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (2824 2824
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (2824 2824
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (2824 2824
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (2824 2824 (:REWRITE |(< (/ x) (/ y))|))
 (2758 2758 (:REWRITE |(< c (- x))|))
 (2635 2301
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (2591 21 (:REWRITE |(mod (+ 1 x) y)|))
 (2210 136 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (2186 68
       (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (2158 2158
       (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2158 2158
       (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2158 2158
       (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2111 136 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (2111 136 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1949 1949
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3F-EXPT-B))
 (1949 1949
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2F-EXPT-B))
 (1949 1949
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1F-EXPT-B))
 (1905 68
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (1887 120 (:REWRITE FLOOR-ZERO . 2))
 (1763 177
       (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (1692 1692
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1638 1478 (:REWRITE |(expt 1/c n)|))
 (1512 171 (:REWRITE DEFAULT-MOD-2))
 (1481 1481 (:REWRITE DEFAULT-EXPT-2))
 (1481 1481 (:REWRITE DEFAULT-EXPT-1))
 (1478 1478 (:REWRITE |(expt (- x) n)|))
 (1395 1251
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1395 1251
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1349 1349 (:REWRITE |(< 0 (* x y))|))
 (1132 119 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1128 32 (:REWRITE FLOOR-=-X/Y . 4))
 (1079 1079
       (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
                . 1))
 (1079 1079 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1079 1079 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1079 1079 (:LINEAR EXPT->=-1-TWO))
 (1079 1079 (:LINEAR EXPT->-1-TWO))
 (1079 1079 (:LINEAR EXPT-<=-1-ONE))
 (1079 1079 (:LINEAR EXPT-<-1-ONE))
 (1048 5 (:REWRITE |(< x (/ y)) with (< 0 y)|))
 (1006 52 (:REWRITE MOD-X-I*J-V2))
 (962 117
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (960 30 (:REWRITE FLOOR-POSITIVE . 3))
 (954 117
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (870 87
      (:REWRITE |(* (expt x m) (expt x n))|))
 (857 857
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (810 30 (:REWRITE FLOOR-POSITIVE . 2))
 (810 30 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (810 30
      (:REWRITE |(<= 1 (* (/ x) y)) with (< 0 x)|))
 (802 136 (:REWRITE DEFAULT-FLOOR-2))
 (777 777 (:REWRITE REDUCE-INTEGERP-+))
 (690 30 (:REWRITE FLOOR-POSITIVE . 4))
 (690 30 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (690 30 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (511 511 (:REWRITE |(< (* x y) 0)|))
 (506 506 (:TYPE-PRESCRIPTION ABS))
 (499 499 (:REWRITE |(< (/ x) 0)|))
 (456 456 (:REWRITE DEFAULT-CDR))
 (448 32
      (:REWRITE |(equal (floor (+ x y) z) x)|))
 (420 30
      (:REWRITE |(<= 1 (* (/ x) y)) with (< x 0)|))
 (400 40 (:REWRITE |(expt c (* d n))|))
 (343 117
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (343 117
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (336 48
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (278 278 (:REWRITE FOLD-CONSTS-IN-+))
 (258 249
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (249 249
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (248 248 (:REWRITE |(equal c (/ x))|))
 (248 248 (:REWRITE |(equal c (- x))|))
 (248 248 (:REWRITE |(equal (/ x) c)|))
 (248 248 (:REWRITE |(equal (/ x) (/ y))|))
 (248 248 (:REWRITE |(equal (- x) c)|))
 (247 247
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (235 136 (:REWRITE DEFAULT-FLOOR-1))
 (206 46
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4L-EXPT))
 (206 46
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3L-EXPT))
 (206 46
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2L-EXPT))
 (206 46
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1L-EXPT))
 (190 190 (:REWRITE DEFAULT-CAR))
 (182 146
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (150 150 (:REWRITE |(< (+ c/d x) y)|))
 (150 150 (:REWRITE |(< (+ (- c) x) y)|))
 (150 98
      (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (120 68
      (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (119 1 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (117 117 (:REWRITE |(floor x (- y))| . 2))
 (117 117 (:REWRITE |(floor x (- y))| . 1))
 (117 117
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (117 117 (:REWRITE |(floor (- x) y)| . 2))
 (117 117 (:REWRITE |(floor (- x) y)| . 1))
 (112 112 (:REWRITE |(equal (+ (- c) x) y)|))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (75 75
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (68 68 (:REWRITE |(mod x (- y))| . 3))
 (68 68 (:REWRITE |(mod x (- y))| . 2))
 (68 68 (:REWRITE |(mod x (- y))| . 1))
 (68 68
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (68 68 (:REWRITE |(mod (- x) y)| . 3))
 (68 68 (:REWRITE |(mod (- x) y)| . 2))
 (68 68 (:REWRITE |(mod (- x) y)| . 1))
 (55 55 (:REWRITE |arith (+ c (+ d x))|))
 (54 54 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (46 46
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (45 45
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (43 1 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4O-EXPT-B))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3O-EXPT-B))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2O-EXPT-B))
 (40 40
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1O-EXPT-B))
 (35 35 (:REWRITE |(< y (+ (- c) x))|))
 (35 35 (:REWRITE |(< x (+ c/d y))|))
 (32 5 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (30 30 (:REWRITE FLOOR-ZERO . 1))
 (30 30 (:REWRITE FLOOR-POSITIVE . 1))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 5))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 4))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 3))
 (30 30 (:REWRITE |(mod (floor x y) z)| . 2))
 (28 28
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (28 28
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (27 1
     (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (27 1
     (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (14 14
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (14 14
     (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (13 1 (:REWRITE EXPT-2-N-IS-EVEN))
 (12 12
     (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (10 10 (:REWRITE |(equal (expt 2 n) c)|))
 (10 10 (:REWRITE |(equal (* x y) 0)|))
 (10 1
     (:REWRITE |(equal (mod (+ x y) z) x)|))
 (6 6 (:REWRITE EXPT-X->-X))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1)))
(M1::NOP-NNIL
 (412 45 (:REWRITE DEFAULT-TIMES-2))
 (225 1 (:REWRITE DEFAULT-FLOOR-RATIO))
 (205 45 (:REWRITE DEFAULT-TIMES-1))
 (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (190 38 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (190 38
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (190 38
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (185 185
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (185 185
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (185 185
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (108 4 (:LINEAR MOD-BOUNDS-3))
 (77
  77
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (77 77
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (76 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (60 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (60 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (60 6 (:REWRITE DEFAULT-DIVIDE))
 (48 8 (:LINEAR MOD-BOUNDS-2))
 (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (38 38
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (38 38 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (38 38
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (38 38 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (35 17 (:REWRITE DEFAULT-PLUS-2))
 (33 6 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (29 17 (:REWRITE DEFAULT-PLUS-1))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (10 10 (:REWRITE DEFAULT-EXPT-2))
 (10 10 (:REWRITE DEFAULT-EXPT-1))
 (10 1 (:REWRITE DEFAULT-FLOOR-2))
 (10 1 (:REWRITE DEFAULT-FLOOR-1))
 (9 9 (:REWRITE DEFAULT-MINUS))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1
    (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|)))
(M1::NOT-EQUAL-NCONS-NNIL
 (10185 84 (:REWRITE |(+ (if a b c) x)|))
 (7836 640
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6685 640 (:REWRITE DEFAULT-PLUS-2))
 (6466 637 (:REWRITE DEFAULT-PLUS-1))
 (5778
  5778
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5778
      5778
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5778
     5778
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5778 5778
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5778 5778
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4464 30 (:REWRITE |(+ x (if a b c))|))
 (3384 528 (:REWRITE CONSTANT-<-INTEGERP))
 (3156 46 (:LINEAR EXPT-X->=-X))
 (3156 46 (:LINEAR EXPT-X->-X))
 (2073 47 (:LINEAR EXPT-<=-1-TWO))
 (2026 47 (:LINEAR EXPT->-1-ONE))
 (1743 484 (:REWRITE DEFAULT-TIMES-2))
 (1280 640 (:REWRITE DEFAULT-LESS-THAN-2))
 (1193 472
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1193 472
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1047 57 (:REWRITE ODD-EXPT-THM))
 (1035 475 (:REWRITE DEFAULT-TIMES-1))
 (899 472
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (721 640 (:REWRITE DEFAULT-LESS-THAN-1))
 (640 640 (:REWRITE THE-FLOOR-BELOW))
 (640 640 (:REWRITE THE-FLOOR-ABOVE))
 (528 528
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (528 528
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (528 528
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (528 528
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (528 528
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (528 528
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (528 528 (:REWRITE |(< c (- x))|))
 (528 528
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (528 528
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (528 528
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (528 528
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (528 528 (:REWRITE |(< (/ x) (/ y))|))
 (528 528 (:REWRITE |(< (- x) c)|))
 (528 528 (:REWRITE |(< (- x) (- y))|))
 (472 472 (:REWRITE INTEGERP-<-CONSTANT))
 (371 371 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (314 314 (:REWRITE |arith (expt x c)|))
 (312 24 (:REWRITE ACL2-NUMBERP-X))
 (296 296
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (278 278 (:REWRITE DEFAULT-CDR))
 (273 273 (:REWRITE |arith (expt 1/c n)|))
 (224 224 (:REWRITE DEFAULT-CAR))
 (185 185 (:REWRITE |(< 0 (* x y))|))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (170 170
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (146 146 (:REWRITE REDUCE-INTEGERP-+))
 (146 146 (:REWRITE INTEGERP-MINUS-X))
 (146 146 (:META META-INTEGERP-CORRECT))
 (129 129
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (129 129
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (129 129 (:REWRITE |(< 0 (/ x))|))
 (117 117 (:REWRITE DEFAULT-EXPT-2))
 (117 117 (:REWRITE DEFAULT-EXPT-1))
 (117 117 (:REWRITE |(expt 1/c n)|))
 (117 117 (:REWRITE |(expt (- x) n)|))
 (112 112 (:TYPE-PRESCRIPTION ABS))
 (112 112 (:REWRITE |(* a (/ a) b)|))
 (96 24 (:REWRITE RATIONALP-X))
 (96 24
     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (94 94
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (94 94
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (92 92
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (92 92
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (92 92 (:REWRITE |(< (/ x) 0)|))
 (92 92 (:REWRITE |(< (* x y) 0)|))
 (79 79 (:REWRITE FOLD-CONSTS-IN-+))
 (71 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (69 69 (:REWRITE |arith (* (- x) y)|))
 (56 56
     (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (56 56
     (:REWRITE |(< (/ x) y) with (< x 0)|))
 (56 56
     (:REWRITE |(< (/ x) y) with (< 0 x)|))
 (47 47
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (47 47 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (47 47 (:LINEAR EXPT-LINEAR-UPPER-<))
 (47 47 (:LINEAR EXPT-LINEAR-LOWER-<))
 (47 47 (:LINEAR EXPT->=-1-TWO))
 (47 47 (:LINEAR EXPT->-1-TWO))
 (47 47 (:LINEAR EXPT-<=-1-ONE))
 (47 47 (:LINEAR EXPT-<-1-TWO))
 (47 47 (:LINEAR EXPT-<-1-ONE))
 (38 19 (:DEFINITION TRUE-LISTP))
 (36 18
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (36 18
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24 24 (:REWRITE REDUCE-RATIONALP-+))
 (24 24 (:REWRITE REDUCE-RATIONALP-*))
 (24 24 (:REWRITE RATIONALP-MINUS-X))
 (24 24 (:META META-RATIONALP-CORRECT))
 (22 22 (:REWRITE |arith (- (* c x))|))
 (18 18 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (18 18
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (18 18
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (18 18
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(equal (- x) (- y))|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (4 4 (:REWRITE |arith (+ c (+ d x))|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::NINSTR
     (30 6 (:REWRITE ACL2-NUMBERP-X))
     (30 3
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (11 7
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (11 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (11 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 7 (:REWRITE SIMPLIFY-SUMS-<))
     (8 2 (:REWRITE RATIONALP-X))
     (8 2
        (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (7 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (6 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (6 3
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE REDUCE-INTEGERP-+))
     (5 5 (:REWRITE INTEGERP-MINUS-X))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (5 5 (:META META-INTEGERP-CORRECT))
     (3 3
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (3 3
        (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (3 3 (:REWRITE |(equal c (/ x))|))
     (3 3 (:REWRITE |(equal c (- x))|))
     (3 3 (:REWRITE |(equal (/ x) c)|))
     (3 3 (:REWRITE |(equal (/ x) (/ y))|))
     (3 3 (:REWRITE |(equal (- x) c)|))
     (3 3 (:REWRITE |(equal (- x) (- y))|))
     (2 2 (:REWRITE REDUCE-RATIONALP-+))
     (2 2 (:REWRITE REDUCE-RATIONALP-*))
     (2 2 (:REWRITE RATIONALP-MINUS-X))
     (2 2 (:META META-RATIONALP-CORRECT))
     (1 1 (:REWRITE ZP-OPEN)))
(M1::NINSTR-NCODE
 (60064 128 (:DEFINITION M1::TURING-MACHINEP))
 (59168 128 (:DEFINITION M1::TURING-4-TUPLE))
 (53248 1024 (:DEFINITION MEMBER-EQUAL))
 (35328 128 (:DEFINITION M1::OPERATIONP))
 (29376 64 (:REWRITE M1::CAR-INSTR))
 (23299 2169
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (22612 3268 (:REWRITE ACL2-NUMBERP-X))
 (18688 128 (:DEFINITION M1::SYMP))
 (16384 32 (:LINEAR M1::OP-INSTR-LESSP-TRICK))
 (14688 32 (:REWRITE M1::OP-INSTR))
 (7835
   7835
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (7835
  7835
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7835
      7835
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7835
     7835
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7835 7835
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7835 7835
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6563 1632 (:REWRITE RATIONALP-X))
 (6563 1632
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (5294 5294 (:REWRITE DEFAULT-CDR))
 (4735 175 (:REWRITE ODD-EXPT-THM))
 (4148 2169
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4006 4006 (:REWRITE DEFAULT-CAR))
 (3520 3520 (:REWRITE REDUCE-INTEGERP-+))
 (3520 3520 (:REWRITE INTEGERP-MINUS-X))
 (3520 3520 (:META META-INTEGERP-CORRECT))
 (2604 951 (:REWRITE DEFAULT-LESS-THAN-2))
 (2581 922
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2581 922
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2497 922 (:REWRITE SIMPLIFY-SUMS-<))
 (2343 2169 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2181 2181
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (2169 2169
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (2169 2169 (:REWRITE |(equal c (/ x))|))
 (2169 2169 (:REWRITE |(equal c (- x))|))
 (2169 2169 (:REWRITE |(equal (/ x) c)|))
 (2169 2169 (:REWRITE |(equal (/ x) (/ y))|))
 (2169 2169 (:REWRITE |(equal (- x) c)|))
 (2169 2169 (:REWRITE |(equal (- x) (- y))|))
 (1792 1792
       (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (1792 1792 (:REWRITE M1::MEMBER-SUBSETP))
 (1632 1632 (:REWRITE REDUCE-RATIONALP-+))
 (1632 1632 (:REWRITE REDUCE-RATIONALP-*))
 (1632 1632 (:REWRITE RATIONALP-MINUS-X))
 (1632 1632 (:META META-RATIONALP-CORRECT))
 (1536 1536 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1384 692 (:REWRITE DEFAULT-PLUS-2))
 (951 951 (:REWRITE THE-FLOOR-BELOW))
 (951 951 (:REWRITE THE-FLOOR-ABOVE))
 (947 947
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (947 947
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (947 947
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (947 947 (:REWRITE INTEGERP-<-CONSTANT))
 (947 947 (:REWRITE CONSTANT-<-INTEGERP))
 (947 947
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (947 947
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (947 947
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (947 947
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (947 947 (:REWRITE |(< c (- x))|))
 (947 947
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (947 947
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (947 947
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (947 947
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (947 947 (:REWRITE |(< (/ x) (/ y))|))
 (947 947 (:REWRITE |(< (- x) c)|))
 (947 947 (:REWRITE |(< (- x) (- y))|))
 (899 29 (:LINEAR EXPT-<=-1-TWO))
 (870 29 (:LINEAR EXPT->-1-ONE))
 (754 29 (:LINEAR EXPT-X->=-X))
 (754 29 (:LINEAR EXPT-X->-X))
 (692 692 (:REWRITE DEFAULT-PLUS-1))
 (640 640
      (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
 (591 591
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (591 591 (:REWRITE NORMALIZE-ADDENDS))
 (520 520
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (310 310 (:REWRITE DEFAULT-EXPT-2))
 (310 310 (:REWRITE DEFAULT-EXPT-1))
 (310 310 (:REWRITE |(expt 1/c n)|))
 (310 310 (:REWRITE |(expt (- x) n)|))
 (276 276
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (276 276
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (276 276 (:REWRITE |(< (/ x) 0)|))
 (276 276 (:REWRITE |(< (* x y) 0)|))
 (256 256 (:DEFINITION M1::STATE-NAMEP))
 (253 253 (:REWRITE |(< 0 (/ x))|))
 (253 253 (:REWRITE |(< 0 (* x y))|))
 (243 243
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (243 243
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (76 76 (:REWRITE |(+ x (if a b c))|))
 (75 75 (:TYPE-PRESCRIPTION M1::NST-IN))
 (63 63 (:TYPE-PRESCRIPTION M1::NSYM))
 (58 58
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (58 58
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (58 58
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (38 38 (:REWRITE |(equal x (if a b c))|))
 (29 29
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (29 29 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (29 29 (:LINEAR EXPT-LINEAR-UPPER-<))
 (29 29 (:LINEAR EXPT-LINEAR-LOWER-<))
 (29 29 (:LINEAR EXPT->=-1-TWO))
 (29 29 (:LINEAR EXPT->-1-TWO))
 (29 29 (:LINEAR EXPT-<=-1-ONE))
 (29 29 (:LINEAR EXPT-<-1-TWO))
 (29 29 (:LINEAR EXPT-<-1-ONE))
 (19 19 (:REWRITE |(equal (+ (- c) x) y)|)))
(M1::TMI2 (113 1 (:DEFINITION M1::NINSTR))
          (34 1 (:DEFINITION NATP))
          (32 4
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (30 6 (:REWRITE ACL2-NUMBERP-X))
          (20 16 (:REWRITE DEFAULT-PLUS-1))
          (16 16 (:REWRITE DEFAULT-PLUS-2))
          (8 8 (:REWRITE THE-FLOOR-BELOW))
          (8 8 (:REWRITE THE-FLOOR-ABOVE))
          (8 8
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (8 8 (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (8 8
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (8 8
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (8 8 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
          (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
          (8 8 (:REWRITE INTEGERP-<-CONSTANT))
          (8 8 (:REWRITE DEFAULT-LESS-THAN-2))
          (8 8 (:REWRITE DEFAULT-LESS-THAN-1))
          (8 8 (:REWRITE CONSTANT-<-INTEGERP))
          (8 8
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
          (8 8
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
          (8 8
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
          (8 8
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
          (8 8 (:REWRITE |(< c (- x))|))
          (8 8
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
          (8 8
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
          (8 8
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
          (8 8
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
          (8 8 (:REWRITE |(< (/ x) (/ y))|))
          (8 8 (:REWRITE |(< (- x) c)|))
          (8 8 (:REWRITE |(< (- x) (- y))|))
          (8 4
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (8 2 (:REWRITE RATIONALP-X))
          (8 2
             (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
          (7 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (6 6
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (6 6
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (6 6 (:REWRITE REDUCE-INTEGERP-+))
          (6 6 (:REWRITE INTEGERP-MINUS-X))
          (6 6 (:REWRITE |(< (/ x) 0)|))
          (6 6 (:REWRITE |(< (* x y) 0)|))
          (6 6 (:META META-INTEGERP-CORRECT))
          (5 5
             (:TYPE-PRESCRIPTION M1::POSITIVE-NATP-NNIL))
          (4 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
          (4 4
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
          (4 4
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
          (4 4
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (4 4 (:REWRITE |(equal c (/ x))|))
          (4 4 (:REWRITE |(equal c (- x))|))
          (4 4 (:REWRITE |(equal (/ x) c)|))
          (4 4 (:REWRITE |(equal (/ x) (/ y))|))
          (4 4 (:REWRITE |(equal (- x) c)|))
          (4 4 (:REWRITE |(equal (- x) (- y))|))
          (4 4 (:REWRITE |(< (+ c/d x) y)|))
          (4 4 (:REWRITE |(< (+ (- c) x) y)|))
          (2 2 (:TYPE-PRESCRIPTION M1::NSYM))
          (2 2 (:TYPE-PRESCRIPTION M1::NST-IN))
          (2 2 (:REWRITE ZP-OPEN))
          (2 2 (:REWRITE REDUCE-RATIONALP-+))
          (2 2 (:REWRITE REDUCE-RATIONALP-*))
          (2 2 (:REWRITE RATIONALP-MINUS-X))
          (2 2
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (2 2 (:META META-RATIONALP-CORRECT))
          (1 1 (:REWRITE DEFAULT-CDR))
          (1 1 (:REWRITE DEFAULT-CAR))
          (1 1 (:REWRITE |(equal x (if a b c))|))
          (1 1 (:REWRITE |(equal (if a b c) x)|)))
(M1::NATP-MAKE-CELL
 (218
  218
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (218
     218
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (218 218
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (173 19 (:REWRITE DEFAULT-PLUS-2))
 (100 19 (:REWRITE DEFAULT-PLUS-1))
 (62 2 (:REWRITE ODD-EXPT-THM))
 (33 15 (:REWRITE SIMPLIFY-SUMS-<))
 (33 15
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (33 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (33 15 (:REWRITE DEFAULT-LESS-THAN-2))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 3 (:REWRITE DEFAULT-TIMES-1))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 26 (:REWRITE DEFAULT-CDR))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (16 16 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE THE-FLOOR-BELOW))
 (15 15 (:REWRITE THE-FLOOR-ABOVE))
 (15 15
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (15 15
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (15 15
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (15 15 (:REWRITE INTEGERP-<-CONSTANT))
 (15 15 (:REWRITE DEFAULT-LESS-THAN-1))
 (15 15 (:REWRITE CONSTANT-<-INTEGERP))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< c (- x))|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (15 15
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (15 15 (:REWRITE |(< (/ x) (/ y))|))
 (15 15 (:REWRITE |(< (- x) c)|))
 (15 15 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (11 11
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (11 11 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (7 1 (:DEFINITION LEN))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (5 5
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (5 5 (:REWRITE REDUCE-INTEGERP-+))
 (5 5 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE |(< (/ x) 0)|))
 (5 5 (:REWRITE |(< (* x y) 0)|))
 (5 5 (:META META-INTEGERP-CORRECT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< 0 (/ x))|))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (3 3
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE DEFAULT-TIMES-2))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::PROPERTIES-OF-INSTR
 (16335 35 (:DEFINITION M1::TURING-MACHINEP))
 (16090 35 (:DEFINITION M1::TURING-4-TUPLE))
 (14420 280 (:DEFINITION MEMBER-EQUAL))
 (9570 35 (:DEFINITION M1::OPERATIONP))
 (9364 20 (:REWRITE M1::OP-INSTR))
 (6916 601
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6836 1028 (:REWRITE ACL2-NUMBERP-X))
 (5576 12 (:REWRITE M1::CAR-INSTR))
 (5060 35 (:DEFINITION M1::SYMP))
 (1936 484 (:REWRITE RATIONALP-X))
 (1936 484
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1500 3 (:LINEAR M1::OP-INSTR-LESSP-TRICK))
 (1132 601
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1054 34 (:REWRITE ODD-EXPT-THM))
 (1050 1050 (:REWRITE DEFAULT-CAR))
 (1042 1042 (:REWRITE REDUCE-INTEGERP-+))
 (1042 1042 (:REWRITE INTEGERP-MINUS-X))
 (1042 1042 (:META META-INTEGERP-CORRECT))
 (1006 1006 (:REWRITE DEFAULT-CDR))
 (665
   665
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (665
  665
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (665 665
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (665
     665
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (665 665
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (665 665
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (663 601 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (601 601
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (601 601
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (601 601
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (601 601 (:REWRITE |(equal c (/ x))|))
 (601 601 (:REWRITE |(equal c (- x))|))
 (601 601 (:REWRITE |(equal (/ x) c)|))
 (601 601 (:REWRITE |(equal (/ x) (/ y))|))
 (601 601 (:REWRITE |(equal (- x) c)|))
 (601 601 (:REWRITE |(equal (- x) (- y))|))
 (492 186 (:REWRITE DEFAULT-LESS-THAN-2))
 (491 185 (:REWRITE SIMPLIFY-SUMS-<))
 (491 185
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (491 185
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (490 490
      (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (490 490 (:REWRITE M1::MEMBER-SUBSETP))
 (484 484 (:REWRITE REDUCE-RATIONALP-+))
 (484 484 (:REWRITE REDUCE-RATIONALP-*))
 (484 484 (:REWRITE RATIONALP-MINUS-X))
 (484 484 (:META META-RATIONALP-CORRECT))
 (420 420 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (343 49 (:DEFINITION LEN))
 (203 49 (:DEFINITION TRUE-LISTP))
 (186 186 (:REWRITE THE-FLOOR-BELOW))
 (186 186 (:REWRITE THE-FLOOR-ABOVE))
 (185 185 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (185 185
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (185 185
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (185 185
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (185 185
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (185 185 (:REWRITE INTEGERP-<-CONSTANT))
 (185 185 (:REWRITE CONSTANT-<-INTEGERP))
 (185 185
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (185 185
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (185 185
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (185 185
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (185 185 (:REWRITE |(< c (- x))|))
 (185 185
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (185 185
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (185 185
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (185 185
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (185 185 (:REWRITE |(< (/ x) (/ y))|))
 (185 185 (:REWRITE |(< (- x) c)|))
 (185 185 (:REWRITE |(< (- x) (- y))|))
 (175 175
      (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
 (140 140 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (140 140
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (98 49 (:REWRITE DEFAULT-PLUS-2))
 (83 83
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (83 83
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (83 83 (:REWRITE |(< (/ x) 0)|))
 (83 83 (:REWRITE |(< (* x y) 0)|))
 (70 70 (:DEFINITION M1::STATE-NAMEP))
 (49 49
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (49 49 (:REWRITE NORMALIZE-ADDENDS))
 (49 49 (:REWRITE DEFAULT-PLUS-1))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (34 34
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (34 34 (:REWRITE DEFAULT-EXPT-2))
 (34 34 (:REWRITE DEFAULT-EXPT-1))
 (34 34 (:REWRITE |(expt 1/c n)|))
 (34 34 (:REWRITE |(expt (- x) n)|))
 (34 34 (:REWRITE |(< 0 (/ x))|))
 (34 34 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 2
    (:TYPE-PRESCRIPTION M1::PROPERTIES-OF-INSTR . 2))
 (4 2
    (:TYPE-PRESCRIPTION M1::PROPERTIES-OF-INSTR . 1)))
(M1::TURING1-4-TUPLE-INSTR
     (285 57 (:REWRITE ACL2-NUMBERP-X))
     (266 19
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (77 77 (:REWRITE DEFAULT-CAR))
     (76 19 (:REWRITE RATIONALP-X))
     (76 19
         (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (45 45 (:REWRITE REDUCE-INTEGERP-+))
     (45 45 (:REWRITE INTEGERP-MINUS-X))
     (45 45 (:META META-INTEGERP-CORRECT))
     (38 19 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (38 19
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (22 22 (:REWRITE DEFAULT-CDR))
     (19 19 (:REWRITE REDUCE-RATIONALP-+))
     (19 19 (:REWRITE REDUCE-RATIONALP-*))
     (19 19
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (19 19
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (19 19 (:REWRITE RATIONALP-MINUS-X))
     (19 19
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (19 19 (:REWRITE |(equal c (/ x))|))
     (19 19 (:REWRITE |(equal c (- x))|))
     (19 19 (:REWRITE |(equal (/ x) c)|))
     (19 19 (:REWRITE |(equal (/ x) (/ y))|))
     (19 19 (:REWRITE |(equal (- x) c)|))
     (19 19 (:REWRITE |(equal (- x) (- y))|))
     (19 19 (:META META-RATIONALP-CORRECT))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
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
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-1))
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
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE |(< (* x y) 0)|)))
(M1::TAPEP-NEW-TAPE1
     (1775 241
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1730 242 (:REWRITE ACL2-NUMBERP-X))
     (496 124 (:REWRITE RATIONALP-X))
     (496 124
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (437 241
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (327 327 (:REWRITE DEFAULT-CAR))
     (255 255 (:REWRITE DEFAULT-CDR))
     (252 252 (:REWRITE REDUCE-INTEGERP-+))
     (252 252 (:REWRITE INTEGERP-MINUS-X))
     (252 252 (:META META-INTEGERP-CORRECT))
     (241 241 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (241 241
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (241 241
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (241 241
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (241 241 (:REWRITE |(equal c (/ x))|))
     (241 241 (:REWRITE |(equal c (- x))|))
     (241 241 (:REWRITE |(equal (/ x) c)|))
     (241 241 (:REWRITE |(equal (/ x) (/ y))|))
     (241 241 (:REWRITE |(equal (- x) c)|))
     (241 241 (:REWRITE |(equal (- x) (- y))|))
     (150 150
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (150 150 (:REWRITE M1::MEMBER-SUBSETP))
     (124 124 (:REWRITE REDUCE-RATIONALP-+))
     (124 124 (:REWRITE REDUCE-RATIONALP-*))
     (124 124 (:REWRITE RATIONALP-MINUS-X))
     (124 124 (:META META-RATIONALP-CORRECT))
     (91 91
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE THE-FLOOR-BELOW))
     (4 4 (:REWRITE THE-FLOOR-ABOVE))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (4 4
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (4 4 (:REWRITE SIMPLIFY-SUMS-<))
     (4 4
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (4 4
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (4 4
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (4 4 (:REWRITE INTEGERP-<-CONSTANT))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
     (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
     (4 4 (:REWRITE CONSTANT-<-INTEGERP))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< c (- x))|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (4 4
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (4 4 (:REWRITE |(< (/ x) 0)|))
     (4 4 (:REWRITE |(< (/ x) (/ y))|))
     (4 4 (:REWRITE |(< (- x) c)|))
     (4 4 (:REWRITE |(< (- x) (- y))|))
     (4 4 (:REWRITE |(< (* x y) 0)|)))
(M1::NATP-CURRENT-SYM
     (528 72 (:REWRITE ACL2-NUMBERP-X))
     (500 58
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (152 38 (:REWRITE RATIONALP-X))
     (152 38
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (118 58
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (102 102 (:REWRITE DEFAULT-CAR))
     (77 77 (:REWRITE REDUCE-INTEGERP-+))
     (77 77 (:REWRITE INTEGERP-MINUS-X))
     (77 77 (:META META-INTEGERP-CORRECT))
     (75 75
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (75 75 (:REWRITE M1::MEMBER-SUBSETP))
     (58 58 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (58 58
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (58 58
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (58 58
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (58 58 (:REWRITE |(equal c (/ x))|))
     (58 58 (:REWRITE |(equal c (- x))|))
     (58 58 (:REWRITE |(equal (/ x) c)|))
     (58 58 (:REWRITE |(equal (/ x) (/ y))|))
     (58 58 (:REWRITE |(equal (- x) c)|))
     (58 58 (:REWRITE |(equal (- x) (- y))|))
     (47 47 (:REWRITE DEFAULT-CDR))
     (38 38 (:REWRITE REDUCE-RATIONALP-+))
     (38 38 (:REWRITE REDUCE-RATIONALP-*))
     (38 38 (:REWRITE RATIONALP-MINUS-X))
     (38 38 (:META META-RATIONALP-CORRECT))
     (18 18
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (6 6 (:REWRITE THE-FLOOR-BELOW))
     (6 6 (:REWRITE THE-FLOOR-ABOVE))
     (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
     (5 5 (:REWRITE SIMPLIFY-SUMS-<))
     (5 5
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (5 5
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (5 5
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (5 5 (:REWRITE INTEGERP-<-CONSTANT))
     (5 5 (:REWRITE CONSTANT-<-INTEGERP))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< c (- x))|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (5 5
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (5 5 (:REWRITE |(< (/ x) (/ y))|))
     (5 5 (:REWRITE |(< (- x) c)|))
     (5 5 (:REWRITE |(< (- x) (- y))|))
     (4 2
        (:TYPE-PRESCRIPTION M1::NATP-CURRENT-SYM))
     (2 2 (:REWRITE |(< (if a b c) x)|))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(M1::TMI2-IS-TMI1
 (407
   407
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (407
  407
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (407 407
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (407
     407
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (407 407
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (407 407
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (186 6 (:LINEAR EXPT-<=-1-TWO))
 (180 6 (:LINEAR EXPT->-1-ONE))
 (156 6 (:LINEAR EXPT-X->=-X))
 (156 6 (:LINEAR EXPT-X->-X))
 (155 5 (:REWRITE ODD-EXPT-THM))
 (135 45
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (90 45 (:REWRITE SIMPLIFY-SUMS-<))
 (90 45
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (90 45 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (90 45 (:REWRITE DEFAULT-LESS-THAN-2))
 (64 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (48 6 (:REWRITE ACL2-NUMBERP-X))
 (45 45 (:REWRITE THE-FLOOR-BELOW))
 (45 45 (:REWRITE THE-FLOOR-ABOVE))
 (45 45
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (45 45
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (45 45
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (45 45 (:REWRITE INTEGERP-<-CONSTANT))
 (45 45 (:REWRITE DEFAULT-LESS-THAN-1))
 (45 45 (:REWRITE CONSTANT-<-INTEGERP))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< c (- x))|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (45 45
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (45 45 (:REWRITE |(< (/ x) (/ y))|))
 (45 45 (:REWRITE |(< (- x) c)|))
 (45 45 (:REWRITE |(< (- x) (- y))|))
 (42 9 (:REWRITE ZP-OPEN))
 (32 16 (:DEFINITION M1::NTH-ALT-DEF))
 (31 31 (:REWRITE DEFAULT-EXPT-2))
 (31 31 (:REWRITE DEFAULT-EXPT-1))
 (31 31 (:REWRITE |(expt 1/c n)|))
 (31 31 (:REWRITE |(expt (- x) n)|))
 (27 27 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (22 6
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (21 21 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE REDUCE-INTEGERP-+))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (20 20 (:META META-INTEGERP-CORRECT))
 (20 5 (:DEFINITION M1::TURING1-MACHINEP))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< 0 (/ x))|))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (16 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (14 2 (:REWRITE RATIONALP-X))
 (14 2
     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:REWRITE DEFAULT-PLUS-2))
 (8 8 (:REWRITE DEFAULT-PLUS-1))
 (7 7
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
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
 (6 6
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-TWO))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (3 3 (:REWRITE |(equal x (if a b c))|))
 (3 3 (:REWRITE |(equal (if a b c) x)|))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|)))
(M1::CONVERT-HALF-TAPE-TO-NAT)
(M1::CONVERT-TAPE-TO-TAPEN-POS
 (7
  7
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (7 7
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(M1::NAT-TO-HALF-TAPE (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                      (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                      (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                      (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                      (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                      (5 1 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                      (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
                      (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
                      (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
                      (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
                      (5 1
                         (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
                      (1 1 (:TYPE-PRESCRIPTION RATIONALP-MOD))
                      (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
                      (1 1 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                      (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                      (1 1 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                      (1 1 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                      (1 1 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
                      (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                      (1 1 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                      (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
                      (1 1 (:TYPE-PRESCRIPTION INTEGERP-MOD-1)))
(M1::DECODE-TAPE-AND-POS)
(M1::NATP-CONVERT-HALF-TAPE-TO-NAT
     (548 68 (:REWRITE ACL2-NUMBERP-X))
     (399 35
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (202 16 (:REWRITE DEFAULT-PLUS-1))
     (160 40 (:REWRITE RATIONALP-X))
     (160 40
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (85 85 (:REWRITE REDUCE-INTEGERP-+))
     (85 85 (:REWRITE INTEGERP-MINUS-X))
     (85 85 (:META META-INTEGERP-CORRECT))
     (63 35
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (52 52 (:REWRITE DEFAULT-CAR))
     (40 40
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (40 40 (:REWRITE REDUCE-RATIONALP-+))
     (40 40 (:REWRITE REDUCE-RATIONALP-*))
     (40 40 (:REWRITE RATIONALP-MINUS-X))
     (40 40 (:REWRITE M1::MEMBER-SUBSETP))
     (40 40 (:META META-RATIONALP-CORRECT))
     (35 35 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (35 35
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (35 35
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (35 35
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (35 35 (:REWRITE |(equal c (/ x))|))
     (35 35 (:REWRITE |(equal c (- x))|))
     (35 35 (:REWRITE |(equal (/ x) c)|))
     (35 35 (:REWRITE |(equal (/ x) (/ y))|))
     (35 35 (:REWRITE |(equal (- x) c)|))
     (35 35 (:REWRITE |(equal (- x) (- y))|))
     (28 16 (:REWRITE DEFAULT-PLUS-2))
     (16 10 (:REWRITE DEFAULT-TIMES-2))
     (14 14
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (11 11 (:REWRITE DEFAULT-CDR))
     (10 10
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (10 10 (:REWRITE DEFAULT-TIMES-1))
     (9 7
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 7 (:REWRITE DEFAULT-LESS-THAN-1))
     (8 8
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (8 8 (:REWRITE NORMALIZE-ADDENDS))
     (8 7
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (8 7
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (7 7 (:REWRITE THE-FLOOR-BELOW))
     (7 7 (:REWRITE THE-FLOOR-ABOVE))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (7 7 (:REWRITE SIMPLIFY-SUMS-<))
     (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (7 7 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (7 7 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (7 7 (:REWRITE INTEGERP-<-CONSTANT))
     (7 7 (:REWRITE DEFAULT-LESS-THAN-2))
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
     (7 7 (:REWRITE |(< (/ x) 0)|))
     (7 7 (:REWRITE |(< (/ x) (/ y))|))
     (7 7 (:REWRITE |(< (- x) c)|))
     (7 7 (:REWRITE |(< (- x) (- y))|))
     (7 7 (:REWRITE |(< (* x y) 0)|))
     (2 2 (:TYPE-PRESCRIPTION ABS))
     (2 1
        (:TYPE-PRESCRIPTION M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
     (1 1 (:REWRITE |(< (+ c/d x) y)|))
     (1 1 (:REWRITE |(< (+ (- c) x) y)|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::HALF-TAPE-CONVERSION
     (659 6 (:REWRITE DEFAULT-FLOOR-RATIO))
     (655 6 (:REWRITE DEFAULT-MOD-RATIO))
     (276 36 (:REWRITE ACL2-NUMBERP-X))
     (239 98 (:REWRITE DEFAULT-TIMES-2))
     (236 28 (:REWRITE REDUCE-RATIONALP-*))
     (235 24
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (223 28 (:REWRITE RATIONALP-X))
     (180 17
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (180 1 (:REWRITE |(floor (+ x r) i)|))
     (156 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (151 21 (:REWRITE |(* y x)|))
     (129 24
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (121 98 (:REWRITE DEFAULT-TIMES-1))
     (114 62 (:REWRITE INTEGERP-MINUS-X))
     (114 3 (:REWRITE ZP-OPEN))
     (102 32 (:REWRITE DEFAULT-PLUS-1))
     (97 97
         (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
     (87 16 (:REWRITE INTEGERP-<-CONSTANT))
     (73 1 (:REWRITE FLOOR-ZERO . 3))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (67 32 (:REWRITE DEFAULT-PLUS-2))
     (60 60 (:REWRITE REDUCE-INTEGERP-+))
     (60 60 (:META META-INTEGERP-CORRECT))
     (56 1 (:REWRITE CANCEL-MOD-+))
     (56 1 (:REWRITE CANCEL-FLOOR-+))
     (49 49
         (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (46 1 (:REWRITE |(< x (/ y)) with (< 0 y)|))
     (43 24
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (41 1 (:REWRITE MOD-X-Y-=-X . 3))
     (41 1 (:REWRITE FLOOR-ZERO . 4))
     (40 1 (:REWRITE MOD-X-Y-=-X . 4))
     (40 1 (:REWRITE FLOOR-ZERO . 5))
     (39 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (39 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
     (36 2 (:REWRITE |(* (* x y) z)|))
     (36 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (36 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
     (34 4 (:REWRITE |(* (- x) y)|))
     (30 15
         (:LINEAR M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (29 29 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (28 28 (:REWRITE RATIONALP-MINUS-X))
     (28 28 (:REWRITE DEFAULT-CAR))
     (28 1 (:REWRITE MOD-ZERO . 3))
     (28 1 (:REWRITE FLOOR-=-X/Y . 3))
     (28 1 (:REWRITE FLOOR-=-X/Y . 2))
     (27 24 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (26 10
         (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
     (25 1 (:REWRITE MOD-ZERO . 4))
     (24 24 (:REWRITE REDUCE-RATIONALP-+))
     (24 24
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (24 24
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (24 24 (:REWRITE |(equal c (/ x))|))
     (24 24 (:REWRITE |(equal c (- x))|))
     (24 24 (:REWRITE |(equal (/ x) c)|))
     (24 24 (:REWRITE |(equal (/ x) (/ y))|))
     (24 24 (:REWRITE |(equal (- x) c)|))
     (24 24 (:REWRITE |(equal (- x) (- y))|))
     (24 24 (:META META-RATIONALP-CORRECT))
     (24 17 (:REWRITE DEFAULT-LESS-THAN-1))
     (24 15
         (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (24 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (22 17 (:REWRITE DEFAULT-LESS-THAN-2))
     (20 20
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (20 20
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (20 20 (:REWRITE NORMALIZE-ADDENDS))
     (20 20 (:REWRITE M1::MEMBER-SUBSETP))
     (20 4 (:REWRITE DEFAULT-MINUS))
     (18 16
         (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (18 4 (:REWRITE |(- (* c x))|))
     (17 17 (:REWRITE THE-FLOOR-BELOW))
     (17 17 (:REWRITE THE-FLOOR-ABOVE))
     (16 16
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (16 16 (:REWRITE CONSTANT-<-INTEGERP))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< c (- x))|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (16 16
         (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (16 16 (:REWRITE |(< (/ x) (/ y))|))
     (16 16 (:REWRITE |(< (- x) c)|))
     (16 16 (:REWRITE |(< (- x) (- y))|))
     (15 15 (:REWRITE SIMPLIFY-SUMS-<))
     (15 15
         (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (13 6 (:REWRITE DEFAULT-MOD-1))
     (13 6 (:REWRITE DEFAULT-FLOOR-1))
     (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (11 11 (:REWRITE DEFAULT-CDR))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (7 7
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (7 7 (:REWRITE |(< 0 (/ x))|))
     (7 7 (:REWRITE |(< 0 (* x y))|))
     (6 6 (:REWRITE DEFAULT-MOD-2))
     (6 6 (:REWRITE DEFAULT-FLOOR-2))
     (5 5 (:TYPE-PRESCRIPTION ABS))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (5 5
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (5 5 (:REWRITE |(mod x 2)| . 2))
     (5 5 (:REWRITE |(floor x 2)| . 2))
     (5 5 (:REWRITE |(< (/ x) 0)|))
     (5 5 (:REWRITE |(< (* x y) 0)|))
     (5 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (5 1 (:REWRITE MOD-X-Y-=-X . 2))
     (5 1
        (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE MOD-CANCEL-*-CONST))
     (5 1 (:REWRITE FLOOR-ZERO . 2))
     (5 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
     (5 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
     (5 1
        (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
     (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
     (5 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
     (5 1
        (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (5 1
        (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (5 1
        (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
     (2 1 (:REWRITE |(< x (/ y)) with (< y 0)|))
     (1 1
        (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1
        (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (1 1 (:REWRITE |(mod x (- y))| . 3))
     (1 1 (:REWRITE |(mod x (- y))| . 2))
     (1 1 (:REWRITE |(mod x (- y))| . 1))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(mod (- x) y)| . 3))
     (1 1 (:REWRITE |(mod (- x) y)| . 2))
     (1 1 (:REWRITE |(mod (- x) y)| . 1))
     (1 1
        (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor x (- y))| . 2))
     (1 1 (:REWRITE |(floor x (- y))| . 1))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
     (1 1
        (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
     (1 1 (:REWRITE |(floor (- x) y)| . 2))
     (1 1 (:REWRITE |(floor (- x) y)| . 1))
     (1 1
        (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
     (1 1
        (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::HALF-TAPE-APPEND
     (2092 112
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1876 184 (:REWRITE ACL2-NUMBERP-X))
     (564 92 (:REWRITE RATIONALP-X))
     (564 92
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (400 112
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (283 161 (:REWRITE DEFAULT-CAR))
     (184 184 (:REWRITE REDUCE-INTEGERP-+))
     (184 184 (:REWRITE INTEGERP-MINUS-X))
     (184 184 (:META META-INTEGERP-CORRECT))
     (112 112 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (112 112
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (112 112
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (112 112
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (112 112 (:REWRITE |(equal c (/ x))|))
     (112 112 (:REWRITE |(equal c (- x))|))
     (112 112 (:REWRITE |(equal (/ x) c)|))
     (112 112 (:REWRITE |(equal (/ x) (/ y))|))
     (112 112 (:REWRITE |(equal (- x) c)|))
     (112 112 (:REWRITE |(equal (- x) (- y))|))
     (105 105
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (105 105 (:REWRITE M1::MEMBER-SUBSETP))
     (104 70 (:REWRITE DEFAULT-CDR))
     (92 92 (:REWRITE REDUCE-RATIONALP-+))
     (92 92 (:REWRITE REDUCE-RATIONALP-*))
     (92 92 (:REWRITE RATIONALP-MINUS-X))
     (92 92 (:META META-RATIONALP-CORRECT))
     (46 46
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::HALF-TAPE-REV (513 45
                        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
                   (504 72 (:REWRITE ACL2-NUMBERP-X))
                   (144 36 (:REWRITE RATIONALP-X))
                   (144 36
                        (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
                   (81 45
                       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
                   (76 76 (:REWRITE DEFAULT-CAR))
                   (72 72 (:REWRITE REDUCE-INTEGERP-+))
                   (72 72 (:REWRITE INTEGERP-MINUS-X))
                   (72 72 (:META META-INTEGERP-CORRECT))
                   (60 12 (:DEFINITION BINARY-APPEND))
                   (50 50
                       (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
                   (50 50 (:REWRITE M1::MEMBER-SUBSETP))
                   (45 45 (:REWRITE SIMPLIFY-SUMS-EQUAL))
                   (45 45
                       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
                   (45 45
                       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
                   (45 45
                       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
                   (45 45 (:REWRITE |(equal c (/ x))|))
                   (45 45 (:REWRITE |(equal c (- x))|))
                   (45 45 (:REWRITE |(equal (/ x) c)|))
                   (45 45 (:REWRITE |(equal (/ x) (/ y))|))
                   (45 45 (:REWRITE |(equal (- x) c)|))
                   (45 45 (:REWRITE |(equal (- x) (- y))|))
                   (36 36 (:REWRITE REDUCE-RATIONALP-+))
                   (36 36 (:REWRITE REDUCE-RATIONALP-*))
                   (36 36 (:REWRITE RATIONALP-MINUS-X))
                   (36 36 (:META META-RATIONALP-CORRECT))
                   (32 32 (:TYPE-PRESCRIPTION M1::REV))
                   (28 28 (:REWRITE DEFAULT-CDR))
                   (18 18
                       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0)))
(M1::CONVERT-HALF-TAPE-TO-NAT-APPEND
 (9978 23
       (:LINEAR M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (6946 622 (:REWRITE ACL2-NUMBERP-X))
 (5757 353
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3557 23 (:REWRITE M1::HALF-TAPE-APPEND))
 (2108 359 (:REWRITE RATIONALP-X))
 (2108 359
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1417 353
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1344 72
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1175 273 (:REWRITE DEFAULT-PLUS-2))
 (1002 18 (:LINEAR EXPT-X->=-X))
 (1002 18 (:LINEAR EXPT-X->-X))
 (730 474 (:REWRITE DEFAULT-CAR))
 (718 718 (:REWRITE REDUCE-INTEGERP-+))
 (718 718 (:REWRITE INTEGERP-MINUS-X))
 (718 718 (:META META-INTEGERP-CORRECT))
 (511
  511
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (511 511
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (511
     511
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (511 511
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (511 511
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (435 74 (:REWRITE DEFAULT-TIMES-2))
 (381 285 (:REWRITE DEFAULT-CDR))
 (359 359 (:REWRITE REDUCE-RATIONALP-+))
 (359 359 (:REWRITE REDUCE-RATIONALP-*))
 (359 359 (:REWRITE RATIONALP-MINUS-X))
 (359 359 (:META META-RATIONALP-CORRECT))
 (356 353
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (353 353
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (353 353
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (353 353 (:REWRITE |(equal c (/ x))|))
 (353 353 (:REWRITE |(equal c (- x))|))
 (353 353 (:REWRITE |(equal (/ x) c)|))
 (353 353 (:REWRITE |(equal (/ x) (/ y))|))
 (353 353 (:REWRITE |(equal (- x) c)|))
 (353 353 (:REWRITE |(equal (- x) (- y))|))
 (315 315
      (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (315 315 (:REWRITE M1::MEMBER-SUBSETP))
 (252 18 (:LINEAR EXPT-<=-1-TWO))
 (184 184 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (150 30 (:REWRITE |(+ c (+ d x))|))
 (144 72 (:REWRITE DEFAULT-LESS-THAN-2))
 (131 131
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (125 125
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (102 51 (:REWRITE DEFAULT-EXPT-2))
 (96 48
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (96 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (72 72 (:REWRITE THE-FLOOR-BELOW))
 (72 72 (:REWRITE THE-FLOOR-ABOVE))
 (72 72
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (72 72
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (72 72 (:REWRITE DEFAULT-LESS-THAN-1))
 (51 51 (:REWRITE DEFAULT-EXPT-1))
 (51 51 (:REWRITE |(expt 1/c n)|))
 (51 51 (:REWRITE |(expt (- x) n)|))
 (48 48 (:REWRITE SIMPLIFY-SUMS-<))
 (48 48
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (48 48 (:REWRITE INTEGERP-<-CONSTANT))
 (48 48 (:REWRITE CONSTANT-<-INTEGERP))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< c (- x))|))
 (48 48
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (48 48
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (48 48
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (48 48 (:REWRITE |(< (/ x) (/ y))|))
 (48 48 (:REWRITE |(< (- x) c)|))
 (48 48 (:REWRITE |(< (- x) (- y))|))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (36 36
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (36 36 (:REWRITE |(< 0 (/ x))|))
 (36 36 (:REWRITE |(< 0 (* x y))|))
 (36 36
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (36 36
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (36 36
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (36 36
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 18 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (36 18 (:LINEAR EXPT-<-1-TWO))
 (24 24 (:REWRITE |(< x (+ c/d y))|))
 (20 20 (:REWRITE |(equal (+ (- c) x) y)|))
 (18 18
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (18 18 (:LINEAR EXPT-LINEAR-UPPER-<))
 (18 18 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (18 18 (:LINEAR EXPT-LINEAR-LOWER-<))
 (18 18 (:LINEAR EXPT->=-1-TWO))
 (18 18 (:LINEAR EXPT->-1-TWO))
 (18 18 (:LINEAR EXPT-<=-1-ONE))
 (18 18 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (5 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (3 3 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+)))
(M1::HALF-TAPE-BELOW-EXPT
 (4258 7 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3797 7 (:REWRITE DEFAULT-MOD-RATIO))
 (2250 345 (:REWRITE DEFAULT-TIMES-2))
 (1470 32 (:REWRITE REDUCE-RATIONALP-+))
 (1326 204 (:REWRITE DEFAULT-PLUS-2))
 (1094 2 (:REWRITE CANCEL-FLOOR-+))
 (912 204 (:REWRITE DEFAULT-PLUS-1))
 (829 97 (:REWRITE REDUCE-INTEGERP-+))
 (801 21 (:REWRITE |(+ y x)|))
 (794 2 (:REWRITE CANCEL-MOD-+))
 (707 345 (:REWRITE DEFAULT-TIMES-1))
 (706
  706
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (706 706
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (706
     706
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (706 706
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (706 706
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (589 40 (:REWRITE RATIONALP-X))
 (520 12 (:REWRITE |(* (- x) y)|))
 (510 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (492 40 (:REWRITE REDUCE-RATIONALP-*))
 (486 6 (:REWRITE |(floor (+ x r) i)|))
 (439 109 (:REWRITE NORMALIZE-ADDENDS))
 (360 4 (:REWRITE |(* (* x y) z)|))
 (338 2 (:REWRITE FLOOR-ZERO . 3))
 (301 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (276 36 (:REWRITE ACL2-NUMBERP-X))
 (245 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (240 240
      (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (225 2 (:REWRITE MOD-ZERO . 3))
 (225 2 (:REWRITE FLOOR-=-X/Y . 3))
 (216 2 (:REWRITE FLOOR-=-X/Y . 2))
 (205 101 (:REWRITE INTEGERP-MINUS-X))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (193 28
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (168 78 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (164 2 (:REWRITE MOD-X-Y-=-X . 3))
 (161 30 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (155 2 (:REWRITE FLOOR-ZERO . 4))
 (152 2 (:REWRITE MOD-X-Y-=-X . 4))
 (150 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (150 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (146 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (146 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (143 30
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (143 2 (:REWRITE FLOOR-ZERO . 5))
 (140 30 (:REWRITE DEFAULT-LESS-THAN-1))
 (130 2 (:REWRITE MOD-ZERO . 4))
 (114 3 (:REWRITE ZP-OPEN))
 (99 99
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (93 93 (:META META-INTEGERP-CORRECT))
 (90 13 (:REWRITE DEFAULT-MINUS))
 (70 7 (:REWRITE DEFAULT-MOD-1))
 (70 7 (:REWRITE DEFAULT-FLOOR-1))
 (56 41 (:REWRITE DEFAULT-EXPT-2))
 (53 25
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (52 20
     (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (51 30 (:REWRITE DEFAULT-LESS-THAN-2))
 (41 41 (:REWRITE DEFAULT-EXPT-1))
 (41 41 (:REWRITE |(expt 1/c n)|))
 (41 41 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE RATIONALP-MINUS-X))
 (40 12 (:REWRITE |(- (* c x))|))
 (34 17
     (:LINEAR M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (32 32 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (32 32 (:REWRITE |(* c (* d x))|))
 (31 30
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (31 30
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (30 30 (:REWRITE THE-FLOOR-BELOW))
 (30 30 (:REWRITE THE-FLOOR-ABOVE))
 (30 30 (:REWRITE SIMPLIFY-SUMS-<))
 (30 30
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (30 30
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (30 30 (:REWRITE INTEGERP-<-CONSTANT))
 (30 30 (:REWRITE CONSTANT-<-INTEGERP))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< c (- x))|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (30 30
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (30 30 (:REWRITE |(< (/ x) (/ y))|))
 (30 30 (:REWRITE |(< (- x) c)|))
 (30 30 (:REWRITE |(< (- x) (- y))|))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 28 (:META META-RATIONALP-CORRECT))
 (28 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 2 (:REWRITE MOD-X-Y-=-X . 2))
 (28 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (28 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (25 25 (:REWRITE |(equal c (/ x))|))
 (25 25 (:REWRITE |(equal c (- x))|))
 (25 25 (:REWRITE |(equal (/ x) c)|))
 (25 25 (:REWRITE |(equal (/ x) (/ y))|))
 (25 25 (:REWRITE |(equal (- x) c)|))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (20 20
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (20 20 (:REWRITE M1::MEMBER-SUBSETP))
 (20 10 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (19 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (19 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (19 2 (:REWRITE FLOOR-ZERO . 2))
 (19 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (19 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (18 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (15 15
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< (/ x) 0)|))
 (15 15 (:REWRITE |(< (* x y) 0)|))
 (13 13 (:REWRITE DEFAULT-CDR))
 (12 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10 (:REWRITE |(+ x (- x))|))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (10 1 (:REWRITE |(- (- x))|))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (9 1 (:REWRITE |(* (/ x) (expt x n))|))
 (8 8 (:REWRITE |(< (+ c/d x) y)|))
 (8 8 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE DEFAULT-MOD-2))
 (7 7 (:REWRITE DEFAULT-FLOOR-2))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(mod x 2)| . 2))
 (6 6 (:REWRITE |(floor x 2)| . 2))
 (5 1
    (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE MOD-CANCEL-*-CONST))
 (5 1
    (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (5 1
    (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (5 1
    (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (2 2 (:TYPE-PRESCRIPTION FLOOR))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::LEN-REV (93 69 (:REWRITE DEFAULT-CDR))
             (80 40 (:REWRITE DEFAULT-PLUS-2))
             (45 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (45 15
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (45 15
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (40 40 (:REWRITE DEFAULT-PLUS-1))
             (38 38
                 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
             (38 38 (:REWRITE NORMALIZE-ADDENDS))
             (35 35 (:REWRITE DEFAULT-CAR))
             (15 15
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (15 15
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (15 15
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (15 15 (:REWRITE |(equal c (/ x))|))
             (15 15 (:REWRITE |(equal c (- x))|))
             (15 15 (:REWRITE |(equal (/ x) c)|))
             (15 15 (:REWRITE |(equal (/ x) (/ y))|))
             (15 15 (:REWRITE |(equal (- x) c)|))
             (15 15 (:REWRITE |(equal (- x) (- y))|))
             (8 8 (:REWRITE |(equal (+ (- c) x) y)|)))
(M1::REV-REV (117 90 (:REWRITE DEFAULT-CDR))
             (108 81 (:REWRITE DEFAULT-CAR))
             (32 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
             (32 16
                 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
             (32 16
                 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
             (16 16
                 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
             (16 16
                 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
             (16 16
                 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
             (16 16 (:REWRITE |(equal c (/ x))|))
             (16 16 (:REWRITE |(equal c (- x))|))
             (16 16 (:REWRITE |(equal (/ x) c)|))
             (16 16 (:REWRITE |(equal (/ x) (/ y))|))
             (16 16 (:REWRITE |(equal (- x) c)|))
             (16 16 (:REWRITE |(equal (- x) (- y))|)))
(M1::HALF-TAPE-IMPLIES-TRUE-LISTP
     (171 15
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (168 24 (:REWRITE ACL2-NUMBERP-X))
     (48 12 (:REWRITE RATIONALP-X))
     (48 12
         (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (27 15
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (24 24 (:REWRITE REDUCE-INTEGERP-+))
     (24 24 (:REWRITE INTEGERP-MINUS-X))
     (24 24 (:META META-INTEGERP-CORRECT))
     (15 15
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (15 15
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (15 15
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (15 15 (:REWRITE M1::MEMBER-SUBSETP))
     (15 15
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (15 15 (:REWRITE DEFAULT-CAR))
     (15 15 (:REWRITE |(equal c (/ x))|))
     (15 15 (:REWRITE |(equal c (- x))|))
     (15 15 (:REWRITE |(equal (/ x) c)|))
     (15 15 (:REWRITE |(equal (/ x) (/ y))|))
     (15 15 (:REWRITE |(equal (- x) c)|))
     (15 15 (:REWRITE |(equal (- x) (- y))|))
     (12 12 (:REWRITE REDUCE-RATIONALP-+))
     (12 12 (:REWRITE REDUCE-RATIONALP-*))
     (12 12 (:REWRITE RATIONALP-MINUS-X))
     (12 12 (:META META-RATIONALP-CORRECT))
     (6 6
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 2 (:DEFINITION TRUE-LISTP)))
(M1::CONVERT-HALF-TAPE-TO-NAT-UPPER-BOUND
 (320 8 (:LINEAR EXPT-<=-1-TWO))
 (312 8 (:LINEAR EXPT->-1-ONE))
 (280 8 (:LINEAR EXPT-X->=-X))
 (280 8 (:LINEAR EXPT-X->-X))
 (276 36 (:REWRITE ACL2-NUMBERP-X))
 (243
  243
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (243 243
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (243
     243
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (243 243
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (243 243
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (228 20
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (134 40 (:REWRITE DEFAULT-LESS-THAN-2))
 (118 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (108 5 (:REWRITE ODD-EXPT-THM))
 (84 38 (:REWRITE SIMPLIFY-SUMS-<))
 (84 14 (:REWRITE DEFAULT-PLUS-1))
 (80 20 (:REWRITE RATIONALP-X))
 (80 20
     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (48 40 (:REWRITE DEFAULT-LESS-THAN-1))
 (46 10 (:REWRITE DEFAULT-TIMES-2))
 (41 41 (:REWRITE REDUCE-INTEGERP-+))
 (41 41 (:REWRITE INTEGERP-MINUS-X))
 (41 41 (:META META-INTEGERP-CORRECT))
 (40 40 (:REWRITE THE-FLOOR-BELOW))
 (40 40 (:REWRITE THE-FLOOR-ABOVE))
 (40 40
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (40 40
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< c (- x))|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< (/ x) (/ y))|))
 (40 40 (:REWRITE |(< (- x) c)|))
 (40 40 (:REWRITE |(< (- x) (- y))|))
 (36 20
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (36 14 (:REWRITE DEFAULT-PLUS-2))
 (24 24 (:REWRITE DEFAULT-CAR))
 (20 20
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (20 20 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (20 20 (:REWRITE REDUCE-RATIONALP-+))
 (20 20 (:REWRITE REDUCE-RATIONALP-*))
 (20 20
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (20 20
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (20 20 (:REWRITE RATIONALP-MINUS-X))
 (20 20 (:REWRITE M1::MEMBER-SUBSETP))
 (20 20
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (20 20 (:REWRITE |(equal c (/ x))|))
 (20 20 (:REWRITE |(equal c (- x))|))
 (20 20 (:REWRITE |(equal (/ x) c)|))
 (20 20 (:REWRITE |(equal (/ x) (/ y))|))
 (20 20 (:REWRITE |(equal (- x) c)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:META META-RATIONALP-CORRECT))
 (18 18 (:REWRITE |arith (expt x c)|))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (18 18
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (18 18 (:REWRITE |(< 0 (/ x))|))
 (18 18 (:REWRITE |(< 0 (* x y))|))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 8 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (16 8 (:LINEAR EXPT-<-1-TWO))
 (15 15 (:REWRITE |arith (expt 1/c n)|))
 (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 6 (:REWRITE DEFAULT-EXPT-2))
 (11 10 (:REWRITE DEFAULT-TIMES-1))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (8 8
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (6 6 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (3 1
    (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (2 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1 1 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1 1 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::CONVERT-HALF-TAPE-TO-NAT-UPPER-BOUND-COROLLARY
 (1221 65
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1218 114 (:REWRITE ACL2-NUMBERP-X))
 (624 4 (:REWRITE M1::HALF-TAPE-APPEND))
 (380 63 (:REWRITE RATIONALP-X))
 (368 62
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (338 5 (:REWRITE ODD-EXPT-THM))
 (283
  283
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (283 283
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (283
     283
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (283 283
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (283 283
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (260 5
      (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (240 6 (:LINEAR EXPT-<=-1-TWO))
 (237 65
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (234 6 (:LINEAR EXPT->-1-ONE))
 (210 23 (:REWRITE DEFAULT-PLUS-1))
 (210 6 (:LINEAR EXPT-X->=-X))
 (210 6 (:LINEAR EXPT-X->-X))
 (200 1
      (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (170 110 (:REWRITE DEFAULT-CAR))
 (169 5
      (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (142 32
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (142 32 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (140 33
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (126 126 (:REWRITE REDUCE-INTEGERP-+))
 (126 126 (:REWRITE INTEGERP-MINUS-X))
 (126 126 (:META META-INTEGERP-CORRECT))
 (112 32 (:REWRITE SIMPLIFY-SUMS-<))
 (109 33 (:REWRITE DEFAULT-LESS-THAN-2))
 (100 20 (:DEFINITION BINARY-APPEND))
 (91 23 (:REWRITE DEFAULT-PLUS-2))
 (71 33 (:REWRITE DEFAULT-LESS-THAN-1))
 (65 65
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (65 65 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (65 65
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (65 65
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (65 65 (:REWRITE M1::MEMBER-SUBSETP))
 (65 65
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (65 65 (:REWRITE |(equal c (/ x))|))
 (65 65 (:REWRITE |(equal c (- x))|))
 (65 65 (:REWRITE |(equal (/ x) c)|))
 (65 65 (:REWRITE |(equal (/ x) (/ y))|))
 (65 65 (:REWRITE |(equal (- x) c)|))
 (65 65 (:REWRITE |(equal (- x) (- y))|))
 (62 62 (:REWRITE REDUCE-RATIONALP-+))
 (62 62 (:REWRITE REDUCE-RATIONALP-*))
 (62 62 (:REWRITE RATIONALP-MINUS-X))
 (62 62 (:META META-RATIONALP-CORRECT))
 (60 32
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (52 40 (:REWRITE DEFAULT-CDR))
 (42 7 (:REWRITE DEFAULT-TIMES-2))
 (36 36 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (33 33 (:REWRITE THE-FLOOR-BELOW))
 (33 33 (:REWRITE THE-FLOOR-ABOVE))
 (33 33
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (33 33
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (32 32 (:REWRITE INTEGERP-<-CONSTANT))
 (32 32 (:REWRITE CONSTANT-<-INTEGERP))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (32 32 (:REWRITE |(< c (- x))|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (32 32
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (32 32 (:REWRITE |(< (/ x) (/ y))|))
 (32 32 (:REWRITE |(< (- x) c)|))
 (32 32 (:REWRITE |(< (- x) (- y))|))
 (27 1 (:REWRITE |(+ y (+ x z))|))
 (26 26
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 24 (:REWRITE |arith (expt x c)|))
 (20 20 (:REWRITE |arith (expt 1/c n)|))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (14 14
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (14 14 (:REWRITE |(< 0 (/ x))|))
 (14 14 (:REWRITE |(< 0 (* x y))|))
 (14 7 (:REWRITE DEFAULT-EXPT-2))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (12 12
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (12 12
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (12 6 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (12 6 (:LINEAR EXPT-<-1-TWO))
 (12 1 (:REWRITE |(+ c (+ d x))|))
 (7 7 (:REWRITE DEFAULT-TIMES-1))
 (7 7 (:REWRITE DEFAULT-EXPT-1))
 (7 7 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (7 7 (:REWRITE |(expt 1/c n)|))
 (7 7 (:REWRITE |(expt (- x) n)|))
 (6 6
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-UPPER-<))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (6 6 (:LINEAR EXPT-LINEAR-LOWER-<))
 (6 6 (:LINEAR EXPT->=-1-TWO))
 (6 6 (:LINEAR EXPT->-1-TWO))
 (6 6 (:LINEAR EXPT-<=-1-ONE))
 (6 6 (:LINEAR EXPT-<-1-ONE))
 (5 5
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4 4
    (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|)))
(M1::HINT (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
          (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
          (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
          (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
          (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
          (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
          (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
          (15 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
          (15 3
              (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1)))
(M1::LOG2-SUM
 (1640 1 (:REWRITE |(floor (if a b c) x)|))
 (1323 12 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1069 205 (:REWRITE DEFAULT-TIMES-2))
 (1066 13 (:REWRITE |(* y x)|))
 (923
  923
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (923 923
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (923
     923
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (923 923
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (923 923
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (660 137 (:REWRITE DEFAULT-PLUS-2))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (326 205 (:REWRITE DEFAULT-TIMES-1))
 (269 1 (:REWRITE |(* (if a b c) x)|))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (246 246
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (239 56
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (211 5 (:REWRITE ZP-OPEN))
 (198 3 (:REWRITE |(integerp (expt x n))|))
 (197 8 (:REWRITE |(floor (+ x r) i)|))
 (196 61 (:REWRITE DEFAULT-LESS-THAN-2))
 (190 20 (:REWRITE REDUCE-INTEGERP-+))
 (185 50
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (181 137 (:REWRITE DEFAULT-PLUS-1))
 (171 7 (:LINEAR EXPT-X->=-X))
 (171 7 (:LINEAR EXPT-X->-X))
 (152 44 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (134 44 (:REWRITE SIMPLIFY-SUMS-<))
 (123 1 (:REWRITE |(< x (if a b c))|))
 (105 20 (:META META-INTEGERP-CORRECT))
 (102 102
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (102 102 (:REWRITE NORMALIZE-ADDENDS))
 (102 11 (:REWRITE ODD-EXPT-THM))
 (90 13
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (90 13
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (84 12 (:REWRITE DEFAULT-FLOOR-1))
 (82 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (66 10
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (66 10
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (66 10
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (61 61 (:REWRITE THE-FLOOR-BELOW))
 (61 61 (:REWRITE THE-FLOOR-ABOVE))
 (61 61 (:REWRITE DEFAULT-LESS-THAN-1))
 (61 61 (:REWRITE DEFAULT-EXPT-2))
 (61 61 (:REWRITE DEFAULT-EXPT-1))
 (61 61 (:REWRITE |(expt 1/c n)|))
 (61 61 (:REWRITE |(expt (- x) n)|))
 (57 56
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (57 56
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (50 50 (:REWRITE INTEGERP-<-CONSTANT))
 (50 50 (:REWRITE CONSTANT-<-INTEGERP))
 (50 50
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (50 50
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (50 50
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (50 50
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (50 50 (:REWRITE |(< c (- x))|))
 (50 50
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (50 50
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (50 50
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (50 50
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (50 50 (:REWRITE |(< (/ x) (/ y))|))
 (50 50 (:REWRITE |(< (- x) c)|))
 (50 50 (:REWRITE |(< (- x) (- y))|))
 (50 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (50 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (50 10 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (50 10
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (40 10 (:REWRITE |(* c (* d x))|))
 (31 31 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (30 6
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (22 22 (:REWRITE |(< (* x y) 0)|))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (20 20 (:REWRITE INTEGERP-MINUS-X))
 (18 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (14 14
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (14 14
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (13 13
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:REWRITE DEFAULT-FLOOR-2))
 (11 11 (:REWRITE |(floor x 2)| . 2))
 (11 11
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 2))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE |(equal (+ (- c) x) y)|))
 (9 9 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (9 9
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (8 8 (:REWRITE |(< x (+ c/d y))|))
 (7 7 (:LINEAR EXPT-LINEAR-UPPER-<))
 (7 7 (:LINEAR EXPT-LINEAR-LOWER-<))
 (7 7 (:LINEAR EXPT->=-1-TWO))
 (7 7 (:LINEAR EXPT->-1-TWO))
 (7 7 (:LINEAR EXPT-<=-1-ONE))
 (7 7 (:LINEAR EXPT-<-1-TWO))
 (7 7 (:LINEAR EXPT-<-1-ONE))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::LOG2-SUM-COROLLARY
 (31815 3 (:DEFINITION M1::LOG2))
 (29907 6 (:REWRITE DEFAULT-FLOOR-RATIO))
 (10452 42 (:REWRITE |(* y x)|))
 (10260 72 (:REWRITE |(* x (+ y z))|))
 (8400 165 (:REWRITE RATIONALP-X))
 (7021 328 (:META META-INTEGERP-CORRECT))
 (5979 255
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (4578 111
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (4350 39 (:REWRITE |(integerp (expt x n))|))
 (4163 495 (:REWRITE DEFAULT-TIMES-2))
 (3780 756
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3723 120 (:META META-RATIONALP-CORRECT))
 (3042 3 (:REWRITE FLOOR-ZERO . 5))
 (3042 3 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (3042 3 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (3036 3 (:REWRITE CANCEL-FLOOR-+))
 (2880 108 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (2772 72 (:REWRITE |(* (/ c) (expt d n))|))
 (2685 120 (:REWRITE REDUCE-RATIONALP-+))
 (2400 302 (:REWRITE DEFAULT-PLUS-2))
 (2304 36 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1971 138
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1677 3 (:REWRITE FLOOR-=-X/Y . 2))
 (1599 3 (:REWRITE FLOOR-=-X/Y . 3))
 (1494
  1494
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1494
      1494
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1494
     1494
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1494 1494
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1494 1494
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1465 302 (:REWRITE DEFAULT-PLUS-1))
 (1428 3
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (1428 3 (:REWRITE FLOOR-CANCEL-*-CONST))
 (1428 3
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (1377 3 (:REWRITE ZP-OPEN))
 (1155 147 (:REWRITE RATIONALP-MINUS-X))
 (840 138 (:REWRITE REDUCE-RATIONALP-*))
 (764 341 (:REWRITE INTEGERP-MINUS-X))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (756 756
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (668 495 (:REWRITE DEFAULT-TIMES-1))
 (556 4 (:DEFINITION M1::HALF-TAPE))
 (544 4 (:DEFINITION M1::SYMP))
 (532 12 (:DEFINITION MEMBER-EQUAL))
 (510 10
      (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (484 52 (:REWRITE ACL2-NUMBERP-X))
 (468 6 (:REWRITE |(floor (+ x r) i)|))
 (394 121 (:REWRITE |(+ c (+ d x))|))
 (387 138 (:REWRITE DEFAULT-LESS-THAN-1))
 (375 99 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (357 99
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (333 3
      (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (243 138 (:REWRITE DEFAULT-LESS-THAN-2))
 (239 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (202 81 (:REWRITE DEFAULT-EXPT-2))
 (198 198
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (180 72 (:REWRITE |(* 1 x)|))
 (162 18 (:REWRITE DEFAULT-MINUS))
 (160 4 (:LINEAR EXPT-<=-1-TWO))
 (156 4 (:LINEAR EXPT->-1-ONE))
 (147 21 (:DEFINITION LEN))
 (147 3
      (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (144 18 (:REWRITE |(- (* c x))|))
 (141 3 (:REWRITE |(floor x 2)| . 1))
 (140 4 (:LINEAR EXPT-X->=-X))
 (140 4 (:LINEAR EXPT-X->-X))
 (138 138 (:REWRITE THE-FLOOR-BELOW))
 (138 138 (:REWRITE THE-FLOOR-ABOVE))
 (138 138
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (138 138
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (128 112 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (120 120 (:TYPE-PRESCRIPTION FIX))
 (119 119 (:REWRITE |(< (+ c/d x) y)|))
 (110 99 (:REWRITE SIMPLIFY-SUMS-<))
 (105 15 (:REWRITE INTP-2))
 (99 99
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (99 99 (:REWRITE INTEGERP-<-CONSTANT))
 (99 99 (:REWRITE CONSTANT-<-INTEGERP))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (99 99 (:REWRITE |(< c (- x))|))
 (99 99
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (99 99
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (99 99
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (99 99 (:REWRITE |(< (/ x) (/ y))|))
 (99 99 (:REWRITE |(< (- x) c)|))
 (99 99 (:REWRITE |(< (- x) (- y))|))
 (96 6 (:REWRITE INTP-4))
 (90 18 (:REWRITE |(* a (/ a) b)|))
 (87 87 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (81 81 (:REWRITE DEFAULT-EXPT-1))
 (81 81 (:REWRITE |(expt 1/c n)|))
 (81 81 (:REWRITE |(expt (- x) n)|))
 (80 80 (:REWRITE |(< (+ (- c) x) y)|))
 (78 78 (:REWRITE FOLD-CONSTS-IN-+))
 (66 3 (:REWRITE NINTP-4))
 (58 58 (:REWRITE |arith (expt x c)|))
 (54 54 (:TYPE-PRESCRIPTION INTP-+))
 (54 54 (:REWRITE |arith (expt 1/c n)|))
 (54 54 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (54 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (47 47
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (47 25
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (45 45 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE DEFAULT-CAR))
 (40 40 (:REWRITE |(< (* x y) 0)|))
 (40 5 (:DEFINITION M1::REV))
 (36 36 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (36 36 (:REWRITE |(* c (* d x))|))
 (35 35
     (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (33 3 (:REWRITE NINTP-3))
 (31 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (30 30 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (26 26 (:REWRITE |arith (* c (* d x))|))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (25 25 (:REWRITE |(equal c (/ x))|))
 (25 25 (:REWRITE |(equal c (- x))|))
 (25 25 (:REWRITE |(equal (/ x) c)|))
 (25 25 (:REWRITE |(equal (/ x) (/ y))|))
 (25 25 (:REWRITE |(equal (- x) c)|))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (25 5 (:DEFINITION BINARY-APPEND))
 (20 20
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (20 20 (:REWRITE M1::MEMBER-SUBSETP))
 (20 1 (:REWRITE ODD-EXPT-THM))
 (12 12 (:REWRITE |arith (- (* c x))|))
 (12 12 (:REWRITE |arith (* (- x) y)|))
 (12 12 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (11 11
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (11 11 (:REWRITE |(< 0 (/ x))|))
 (11 11 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8 4 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (8 4 (:LINEAR EXPT-<-1-TWO))
 (6 6 (:REWRITE DEFAULT-FLOOR-2))
 (6 6 (:REWRITE DEFAULT-FLOOR-1))
 (5 5 (:REWRITE |(equal (+ (- c) x) y)|))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 2))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE |arith (+ c (+ d x))|))
 (3 3 (:REWRITE FLOOR-ZERO . 4))
 (3 3 (:REWRITE FLOOR-ZERO . 3))
 (3 3 (:REWRITE FLOOR-ZERO . 2))
 (3 3 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3 3 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (3 3
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3 3 (:REWRITE |(floor x 2)| . 2))
 (3 3 (:REWRITE |(floor x (- y))| . 2))
 (3 3 (:REWRITE |(floor x (- y))| . 1))
 (3 3
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (3 3
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(floor (- x) y)| . 2))
 (3 3 (:REWRITE |(floor (- x) y)| . 1))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (3 3
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (3 3
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< (/ x) 0)|)))
(M1::FLOOR-LEMMA-1
 (5831 863 (:REWRITE DEFAULT-TIMES-2))
 (5696 10 (:REWRITE FLOOR-ZERO . 3))
 (5351 863 (:REWRITE DEFAULT-TIMES-1))
 (5021 15 (:REWRITE FLOOR-=-X/Y . 3))
 (4991 15 (:REWRITE FLOOR-=-X/Y . 2))
 (4176 15 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4036 805 (:REWRITE DEFAULT-PLUS-2))
 (3608
  3608
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3608
      3608
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3608
     3608
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3608 3608
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3608 3608
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3065 15 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2940 805 (:REWRITE DEFAULT-PLUS-1))
 (1274 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1226 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1156 202 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1027 1027
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1027 1027
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1027 1027
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1027 1027
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1027 1027
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (930 93 (:REWRITE DEFAULT-DIVIDE))
 (728 49
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (728 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (707 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (615 15 (:REWRITE FLOOR-ZERO . 5))
 (600 15 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (580 62 (:META META-INTEGERP-CORRECT))
 (539 49 (:REWRITE DEFAULT-LESS-THAN-1))
 (509 41
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (509 41
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (509 41
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (508 49 (:REWRITE SIMPLIFY-SUMS-<))
 (479 214 (:REWRITE DEFAULT-MINUS))
 (465 15 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (465 15 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (416 416
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (415 10 (:REWRITE |(floor (+ x r) i)|))
 (366 15
      (:REWRITE |(* (expt x m) (expt x n))|))
 (340 10 (:REWRITE FLOOR-ZERO . 2))
 (321 21 (:REWRITE ODD-EXPT-THM))
 (287 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (287 41 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (287 41
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (238 49 (:REWRITE DEFAULT-LESS-THAN-2))
 (182 182 (:REWRITE DEFAULT-EXPT-2))
 (182 182 (:REWRITE DEFAULT-EXPT-1))
 (182 182 (:REWRITE |(expt 1/c n)|))
 (182 182 (:REWRITE |(expt (- x) n)|))
 (181 181
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (150 15 (:REWRITE DEFAULT-FLOOR-2))
 (150 15 (:REWRITE DEFAULT-FLOOR-1))
 (82 22 (:LINEAR EXPT-<=-1-TWO))
 (80 22 (:LINEAR EXPT->-1-ONE))
 (80 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (72 22 (:LINEAR EXPT-X->=-X))
 (72 22 (:LINEAR EXPT-X->-X))
 (67 49
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (62 62 (:REWRITE REDUCE-INTEGERP-+))
 (62 62 (:REWRITE INTEGERP-MINUS-X))
 (49 49 (:REWRITE THE-FLOOR-BELOW))
 (49 49 (:REWRITE THE-FLOOR-ABOVE))
 (49 49
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (49 49 (:REWRITE INTEGERP-<-CONSTANT))
 (49 49 (:REWRITE CONSTANT-<-INTEGERP))
 (49 49
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (49 49
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (49 49
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (49 49
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (49 49 (:REWRITE |(< c (- x))|))
 (49 49
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (49 49
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (49 49
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (49 49
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (49 49 (:REWRITE |(< (/ x) (/ y))|))
 (49 49 (:REWRITE |(< (- x) c)|))
 (49 49 (:REWRITE |(< (- x) (- y))|))
 (44 44
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (44 44
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (44 44
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (40 40 (:REWRITE |(+ c (+ d x))|))
 (35 35 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (30 30 (:REWRITE |(< (+ (- c) x) y)|))
 (24 24
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (23 23 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (22 22 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (22 22
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (22 22 (:LINEAR EXPT-LINEAR-UPPER-<))
 (22 22 (:LINEAR EXPT-LINEAR-LOWER-<))
 (22 22 (:LINEAR EXPT->=-1-TWO))
 (22 22 (:LINEAR EXPT->-1-TWO))
 (22 22 (:LINEAR EXPT-<=-1-ONE))
 (22 22 (:LINEAR EXPT-<-1-TWO))
 (22 22 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (10 10
     (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (10 10 (:REWRITE |(< 0 (/ x))|))
 (10 10 (:REWRITE |(< 0 (* x y))|))
 (10 10 (:REWRITE |(- (* c x))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|)))
(M1::GET-THE-UPPER-HALF-TAPE
 (4265 7 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3975 7 (:REWRITE DEFAULT-MOD-RATIO))
 (2327 32 (:REWRITE |(* y x)|))
 (1489 266 (:REWRITE DEFAULT-TIMES-2))
 (1470 32 (:REWRITE REDUCE-RATIONALP-+))
 (1325 203 (:REWRITE DEFAULT-PLUS-2))
 (1044 2 (:REWRITE CANCEL-FLOOR-+))
 (911 203 (:REWRITE DEFAULT-PLUS-1))
 (824 92 (:REWRITE REDUCE-INTEGERP-+))
 (801 21 (:REWRITE |(+ y x)|))
 (744 2 (:REWRITE CANCEL-MOD-+))
 (646
  646
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (646 646
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (646
     646
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (646 646
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (646 646
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (589 40 (:REWRITE RATIONALP-X))
 (560 266 (:REWRITE DEFAULT-TIMES-1))
 (510 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (492 40 (:REWRITE REDUCE-RATIONALP-*))
 (439 109 (:REWRITE NORMALIZE-ADDENDS))
 (420 12 (:REWRITE |(* (- x) y)|))
 (347 2 (:REWRITE FLOOR-ZERO . 3))
 (301 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (282 2 (:REWRITE MOD-ZERO . 4))
 (276 36 (:REWRITE ACL2-NUMBERP-X))
 (245 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (240 240
      (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (240 2 (:REWRITE MOD-X-Y-=-X . 3))
 (231 11 (:LINEAR EXPT->-1-ONE))
 (231 2 (:REWRITE FLOOR-ZERO . 4))
 (228 2 (:REWRITE MOD-X-Y-=-X . 4))
 (226 2 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (226 2 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (222 2 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (222 2 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (219 2 (:REWRITE FLOOR-ZERO . 5))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (202 202
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (200 96 (:REWRITE INTEGERP-MINUS-X))
 (197 2 (:REWRITE MOD-ZERO . 3))
 (197 2 (:REWRITE FLOOR-=-X/Y . 3))
 (193 28
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (188 2 (:REWRITE FLOOR-=-X/Y . 2))
 (154 11 (:LINEAR EXPT->=-1-ONE))
 (152 22
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (151 6 (:REWRITE |(floor (+ x r) i)|))
 (136 46 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (114 3 (:REWRITE ZP-OPEN))
 (113 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (99 99
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (95 21
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (92 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (90 13 (:REWRITE DEFAULT-MINUS))
 (88 88 (:META META-INTEGERP-CORRECT))
 (87 72 (:REWRITE DEFAULT-EXPT-2))
 (72 72 (:REWRITE DEFAULT-EXPT-1))
 (72 72 (:REWRITE |(expt 1/c n)|))
 (72 72 (:REWRITE |(expt (- x) n)|))
 (70 7 (:REWRITE DEFAULT-MOD-1))
 (70 7 (:REWRITE DEFAULT-FLOOR-1))
 (53 25
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (52 20
     (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (42 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (40 40 (:REWRITE RATIONALP-MINUS-X))
 (36 8 (:REWRITE |(- (* c x))|))
 (34 17
     (:LINEAR M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 28 (:META META-RATIONALP-CORRECT))
 (28 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 2 (:REWRITE MOD-X-Y-=-X . 2))
 (28 2 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (28 2
     (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (25 25
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (25 25 (:REWRITE |(equal c (/ x))|))
 (25 25 (:REWRITE |(equal c (- x))|))
 (25 25 (:REWRITE |(equal (/ x) c)|))
 (25 25 (:REWRITE |(equal (/ x) (/ y))|))
 (25 25 (:REWRITE |(equal (- x) c)|))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (22 22
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (22 22
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (22 21
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (22 21
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (21 21
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
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
 (20 20
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (20 20 (:REWRITE M1::MEMBER-SUBSETP))
 (20 10 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (20 10
     (:LINEAR M1::CONVERT-HALF-TAPE-TO-NAT-UPPER-BOUND-COROLLARY))
 (20 10
     (:LINEAR M1::CONVERT-HALF-TAPE-TO-NAT-UPPER-BOUND))
 (19 2 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (19 2 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (19 2 (:REWRITE FLOOR-ZERO . 2))
 (19 2 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (19 2 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (18 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (18 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (17 17 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13 (:REWRITE DEFAULT-CDR))
 (12 12
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (11 11 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (11 11
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (11 11 (:LINEAR EXPT-X->=-X))
 (11 11 (:LINEAR EXPT-X->-X))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (11 11 (:LINEAR EXPT-LINEAR-UPPER-<))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (11 11 (:LINEAR EXPT-LINEAR-LOWER-<))
 (11 11 (:LINEAR EXPT->=-1-TWO))
 (11 11 (:LINEAR EXPT->-1-TWO))
 (11 11 (:LINEAR EXPT-<=-1-TWO))
 (11 11 (:LINEAR EXPT-<=-1-ONE))
 (11 11 (:LINEAR EXPT-<-1-TWO))
 (11 11 (:LINEAR EXPT-<-1-ONE))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE |(+ x (- x))|))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (10 2 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (10 2
     (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (10 1 (:REWRITE |(- (- x))|))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (9 1 (:REWRITE |(* (/ x) (expt x n))|))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (7 7 (:REWRITE DEFAULT-MOD-2))
 (7 7 (:REWRITE DEFAULT-FLOOR-2))
 (7 7 (:REWRITE |(< 0 (/ x))|))
 (7 7 (:REWRITE |(< 0 (* x y))|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (6 6 (:REWRITE |(mod x 2)| . 2))
 (6 6 (:REWRITE |(floor x 2)| . 2))
 (5 1
    (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE MOD-CANCEL-*-CONST))
 (5 1
    (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (5 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (5 1
    (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (5 1
    (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (2 2 (:TYPE-PRESCRIPTION FLOOR))
 (2 2 (:TYPE-PRESCRIPTION ABS))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 (1 1
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|)))
(M1::TAPE-CONVERSION-THEOREM
 (19806 2080 (:REWRITE DEFAULT-TIMES-2))
 (13240 388
        (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (9374 424 (:REWRITE REDUCE-RATIONALP-+))
 (8000 992 (:META META-INTEGERP-CORRECT))
 (6623 2080 (:REWRITE DEFAULT-TIMES-1))
 (6123
  6123
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (6123
      6123
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (6123
     6123
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (6123 6123
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (6123 6123
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (6101 730 (:REWRITE DEFAULT-PLUS-2))
 (5032 6 (:REWRITE MOD-X-Y-=-X . 4))
 (5032 6
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (4888 6 (:REWRITE MOD-ZERO . 4))
 (4888 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (4888 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (4888 6 (:REWRITE FLOOR-ZERO . 5))
 (4888 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (4888 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (4888 6 (:REWRITE CANCEL-FLOOR-+))
 (4308 730 (:REWRITE DEFAULT-PLUS-1))
 (4040 520 (:REWRITE RATIONALP-MINUS-X))
 (3380 6 (:REWRITE CANCEL-MOD-+))
 (3380 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (3236 6
       (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3236 6 (:REWRITE MOD-CANCEL-*-CONST))
 (3236 6
       (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (3236 6 (:REWRITE FLOOR-CANCEL-*-CONST))
 (3236 6
       (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (3236 6
       (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (3066 3066
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3066 3066
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3066 3066
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2970 138
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (2802 6 (:REWRITE MOD-ZERO . 3))
 (2802 6 (:REWRITE FLOOR-=-X/Y . 3))
 (2722 6 (:REWRITE FLOOR-=-X/Y . 2))
 (2433 1023 (:REWRITE INTEGERP-MINUS-X))
 (1414 10 (:DEFINITION M1::HALF-TAPE))
 (1384 10 (:DEFINITION M1::SYMP))
 (1354 30 (:DEFINITION MEMBER-EQUAL))
 (1028 116 (:REWRITE ACL2-NUMBERP-X))
 (920 18
      (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (864 12 (:REWRITE |(floor (+ x r) i)|))
 (714 6
      (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (714 6
      (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (703 703
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (580 57
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (558 6 (:REWRITE |(mod x 2)| . 1))
 (558 6 (:REWRITE |(floor x 2)| . 1))
 (546 63 (:REWRITE DEFAULT-MINUS))
 (515 332 (:REWRITE DEFAULT-EXPT-2))
 (486 471 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (480 60 (:REWRITE |(- (* c x))|))
 (348 348 (:TYPE-PRESCRIPTION FIX))
 (336 48 (:REWRITE INTP-2))
 (332 332 (:REWRITE DEFAULT-EXPT-1))
 (332 332 (:REWRITE |(expt 1/c n)|))
 (332 332 (:REWRITE |(expt (- x) n)|))
 (330 24 (:REWRITE INTP-4))
 (322 322 (:REWRITE |(+ c (+ d x))|))
 (320 320 (:REWRITE FOLD-CONSTS-IN-+))
 (310 6
      (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (310 6
      (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (300 12 (:REWRITE DEFAULT-MOD-1))
 (300 12 (:REWRITE DEFAULT-FLOOR-1))
 (196 28 (:DEFINITION LEN))
 (169 169
      (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (156 156 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (156 156 (:REWRITE |(* c (* d x))|))
 (138 138
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (138 138
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (138 138
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (138 12 (:REWRITE NINTP-4))
 (133 133 (:REWRITE DEFAULT-CAR))
 (120 14 (:DEFINITION M1::REV))
 (118 118 (:REWRITE DEFAULT-CDR))
 (100 57
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (72 12 (:REWRITE NINTP-3))
 (70 14 (:DEFINITION BINARY-APPEND))
 (60 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (57 57
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (57 57
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (57 57
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (57 57 (:REWRITE |(equal c (/ x))|))
 (57 57 (:REWRITE |(equal c (- x))|))
 (57 57 (:REWRITE |(equal (/ x) c)|))
 (57 57 (:REWRITE |(equal (/ x) (/ y))|))
 (57 57 (:REWRITE |(equal (- x) c)|))
 (57 57 (:REWRITE |(equal (- x) (- y))|))
 (50 50
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (50 50 (:REWRITE M1::MEMBER-SUBSETP))
 (20 20
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (12 12 (:REWRITE DEFAULT-MOD-2))
 (12 12 (:REWRITE DEFAULT-FLOOR-2))
 (12 6
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (12 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (12 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (6 6
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (6 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (6 6 (:REWRITE MOD-X-Y-=-X . 3))
 (6 6 (:REWRITE MOD-X-Y-=-X . 2))
 (6 6
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE INTEGERP-<-CONSTANT))
 (6 6 (:REWRITE FLOOR-ZERO . 4))
 (6 6 (:REWRITE FLOOR-ZERO . 3))
 (6 6 (:REWRITE FLOOR-ZERO . 2))
 (6 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (6 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (6 6
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (6 6 (:REWRITE CONSTANT-<-INTEGERP))
 (6 6 (:REWRITE |(mod x 2)| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 3))
 (6 6 (:REWRITE |(mod x (- y))| . 2))
 (6 6 (:REWRITE |(mod x (- y))| . 1))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(mod (- x) y)| . 3))
 (6 6 (:REWRITE |(mod (- x) y)| . 2))
 (6 6 (:REWRITE |(mod (- x) y)| . 1))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (6 6
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (6 6
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor x 2)| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 2))
 (6 6 (:REWRITE |(floor x (- y))| . 1))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (6 6
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (6 6 (:REWRITE |(floor (- x) y)| . 2))
 (6 6 (:REWRITE |(floor (- x) y)| . 1))
 (6 6
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (6 6
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (6 6
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (6 6
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (6 6
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (- x))|))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) c)|))
 (6 6 (:REWRITE |(< (- x) (- y))|)))
(M1::CURRENT-SYMN (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
                  (25 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
                  (25 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
                  (25 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
                  (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
                  (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
                  (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
                  (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
                  (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
                  (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD-2)))
(M1::CURRENT-SYMN-CONVERT-TAPE-TO-TAPEN-POS
 (1179 147 (:REWRITE ACL2-NUMBERP-X))
 (875 77
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (641 93 (:REWRITE DEFAULT-PLUS-1))
 (520 93 (:REWRITE DEFAULT-PLUS-2))
 (390 5 (:REWRITE |(integerp (expt x n))|))
 (344 86 (:REWRITE RATIONALP-X))
 (344 86
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (193 43 (:REWRITE DEFAULT-TIMES-2))
 (190
  190
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (190 190
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (190
     190
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (190 190
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (190 190
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (183 183 (:REWRITE INTEGERP-MINUS-X))
 (182 182 (:META META-INTEGERP-CORRECT))
 (155 77
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (141 141
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (141 141
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (141 141
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (141 1 (:REWRITE DEFAULT-MOD-RATIO))
 (125 125 (:REWRITE DEFAULT-CAR))
 (96 96 (:REWRITE DEFAULT-CDR))
 (86 86 (:REWRITE REDUCE-RATIONALP-+))
 (86 86 (:REWRITE REDUCE-RATIONALP-*))
 (86 86 (:REWRITE RATIONALP-MINUS-X))
 (86 86 (:META META-RATIONALP-CORRECT))
 (80 80
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (80 80 (:REWRITE M1::MEMBER-SUBSETP))
 (78 43 (:REWRITE DEFAULT-TIMES-1))
 (77 77
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (77 77
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (77 77
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (77 77 (:REWRITE |(equal c (/ x))|))
 (77 77 (:REWRITE |(equal c (- x))|))
 (77 77 (:REWRITE |(equal (/ x) c)|))
 (77 77 (:REWRITE |(equal (/ x) (/ y))|))
 (77 77 (:REWRITE |(equal (- x) c)|))
 (77 77 (:REWRITE |(equal (- x) (- y))|))
 (61 61
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (34 16 (:REWRITE DEFAULT-EXPT-2))
 (33 33
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (24 3 (:DEFINITION M1::REV))
 (20 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (20 10 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16 (:REWRITE DEFAULT-EXPT-1))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (15 10
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 3 (:DEFINITION BINARY-APPEND))
 (12 1 (:REWRITE DEFAULT-MOD-1))
 (11 5 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (10 10 (:REWRITE THE-FLOOR-BELOW))
 (10 10 (:REWRITE THE-FLOOR-ABOVE))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE SIMPLIFY-SUMS-<))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (10 10
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (10 10
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (10 10 (:REWRITE INTEGERP-<-CONSTANT))
 (10 10 (:REWRITE DEFAULT-LESS-THAN-2))
 (10 10 (:REWRITE CONSTANT-<-INTEGERP))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< c (- x))|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (10 10
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (/ x) (/ y))|))
 (10 10 (:REWRITE |(< (- x) c)|))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (10 10 (:REWRITE |(< (+ c/d x) y)|))
 (10 10 (:REWRITE |(< (+ (- c) x) y)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 2 (:REWRITE DEFAULT-MINUS))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(equal x (if a b c))|))
 (1 1 (:REWRITE |(equal (if a b c) x)|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|)))
(M1::NEW-TAPE2
 (15
  15
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (15 15
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A)))
(M1::HALF-TAPE-BELOW-EXPT-RULE1
 (17599 1 (:DEFINITION M1::NAT-TO-HALF-TAPE))
 (9631 2 (:REWRITE DEFAULT-MOD-RATIO))
 (7808 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3459 87 (:REWRITE RATIONALP-X))
 (3105 351 (:REWRITE DEFAULT-TIMES-2))
 (2634 60 (:META META-RATIONALP-CORRECT))
 (2567 857
       (:TYPE-PRESCRIPTION M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (2555 511
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2004 54
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1612 52 (:REWRITE |(* (/ c) (expt d n))|))
 (1485 60 (:REWRITE REDUCE-RATIONALP-+))
 (1456 26 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1256 144 (:META META-INTEGERP-CORRECT))
 (1075 351 (:REWRITE DEFAULT-TIMES-1))
 (1010
  1010
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1010
      1010
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1010
     1010
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1010 1010
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1010 1010
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (873 114 (:REWRITE DEFAULT-PLUS-2))
 (857 857
      (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (765 1 (:REWRITE MOD-X-Y-=-X . 4))
 (765 1
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (743 1 (:REWRITE MOD-ZERO . 4))
 (743 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (743 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (743 1 (:REWRITE FLOOR-ZERO . 5))
 (743 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (743 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (743 1 (:REWRITE CANCEL-FLOOR-+))
 (636 76 (:REWRITE RATIONALP-MINUS-X))
 (605 114 (:REWRITE DEFAULT-PLUS-1))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (511 1 (:REWRITE CANCEL-MOD-+))
 (511 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (500 71 (:REWRITE REDUCE-RATIONALP-*))
 (489 1
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (489 1 (:REWRITE MOD-CANCEL-*-CONST))
 (489 1
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (489 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (489 1
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (489 1
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (457 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (422 1 (:REWRITE MOD-ZERO . 3))
 (422 1 (:REWRITE FLOOR-=-X/Y . 3))
 (422 1 (:REWRITE FLOOR-=-X/Y . 2))
 (384 149 (:REWRITE INTEGERP-MINUS-X))
 (144 144 (:REWRITE REDUCE-INTEGERP-+))
 (132 2 (:REWRITE |(floor (+ x r) i)|))
 (113 113
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (113 113 (:REWRITE NORMALIZE-ADDENDS))
 (111 1
      (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (111 1
      (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (90 10 (:REWRITE DEFAULT-MINUS))
 (88 79 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (87 1 (:REWRITE |(mod x 2)| . 1))
 (87 1 (:REWRITE |(floor x 2)| . 1))
 (80 10 (:REWRITE |(- (* c x))|))
 (58 58 (:TYPE-PRESCRIPTION FIX))
 (58 56 (:REWRITE DEFAULT-EXPT-2))
 (56 56 (:REWRITE DEFAULT-EXPT-1))
 (56 56 (:REWRITE |(expt 1/c n)|))
 (56 56 (:REWRITE |(expt (- x) n)|))
 (56 8 (:REWRITE INTP-2))
 (55 11 (:REWRITE |(* a (/ a) b)|))
 (55 4 (:REWRITE INTP-4))
 (53 53 (:REWRITE FOLD-CONSTS-IN-+))
 (53 53 (:REWRITE |(+ c (+ d x))|))
 (52 1
     (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (49 1
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (49 1
     (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (46 2 (:REWRITE DEFAULT-MOD-1))
 (46 2 (:REWRITE DEFAULT-FLOOR-1))
 (45 15
     (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (38 1 (:REWRITE ZP-OPEN))
 (30 30 (:TYPE-PRESCRIPTION INTP-+))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (26 26 (:REWRITE |(* c (* d x))|))
 (26 2 (:REWRITE ACL2-NUMBERP-X))
 (24 3 (:DEFINITION M1::REV))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (23 2 (:REWRITE NINTP-4))
 (15 3 (:DEFINITION BINARY-APPEND))
 (14 2 (:DEFINITION LEN))
 (12 2 (:REWRITE NINTP-3))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
 (7 7 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-FLOOR-2))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE FLOOR-ZERO . 4))
 (1 1 (:REWRITE FLOOR-ZERO . 3))
 (1 1 (:REWRITE FLOOR-ZERO . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor x 2)| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|)))
(M1::HALF-TAPE-BELOW-EXPT-RULE2
 (17651 1 (:DEFINITION M1::NAT-TO-HALF-TAPE))
 (9659 2 (:REWRITE DEFAULT-MOD-RATIO))
 (7832 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (7104 30 (:REWRITE |(* y x)|))
 (6396 52 (:REWRITE |(* x (+ y z))|))
 (3475 91 (:REWRITE RATIONALP-X))
 (3083 348 (:REWRITE DEFAULT-TIMES-2))
 (2638 64 (:META META-RATIONALP-CORRECT))
 (2567 857
       (:TYPE-PRESCRIPTION M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (2555 511
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2020 58
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1664 52 (:REWRITE |(* (/ c) (expt d n))|))
 (1508 26 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1489 64 (:REWRITE REDUCE-RATIONALP-+))
 (1264 152 (:META META-INTEGERP-CORRECT))
 (1033 348 (:REWRITE DEFAULT-TIMES-1))
 (1002
  1002
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1002
      1002
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1002
     1002
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1002 1002
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1002 1002
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (860 116 (:REWRITE DEFAULT-PLUS-2))
 (857 857
      (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (767 1 (:REWRITE MOD-X-Y-=-X . 4))
 (767 1
      (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (745 1 (:REWRITE MOD-ZERO . 4))
 (745 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (745 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (745 1 (:REWRITE FLOOR-ZERO . 5))
 (745 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (745 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (745 1 (:REWRITE CANCEL-FLOOR-+))
 (640 80 (:REWRITE RATIONALP-MINUS-X))
 (607 116 (:REWRITE DEFAULT-PLUS-1))
 (513 1 (:REWRITE CANCEL-MOD-+))
 (513 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (504 75 (:REWRITE REDUCE-RATIONALP-*))
 (491 1
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (491 1 (:REWRITE MOD-CANCEL-*-CONST))
 (491 1
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (491 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (491 1
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (491 1
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (457 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (424 1 (:REWRITE MOD-ZERO . 3))
 (424 1 (:REWRITE FLOOR-=-X/Y . 3))
 (424 1 (:REWRITE FLOOR-=-X/Y . 2))
 (392 157 (:REWRITE INTEGERP-MINUS-X))
 (152 152 (:REWRITE REDUCE-INTEGERP-+))
 (132 2 (:REWRITE |(floor (+ x r) i)|))
 (115 115
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (115 115 (:REWRITE NORMALIZE-ADDENDS))
 (111 1
      (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (111 1
      (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (90 10 (:REWRITE DEFAULT-MINUS))
 (88 79 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (87 1 (:REWRITE |(mod x 2)| . 1))
 (87 1 (:REWRITE |(floor x 2)| . 1))
 (82 10 (:REWRITE ACL2-NUMBERP-X))
 (80 80 (:REWRITE FOLD-CONSTS-IN-+))
 (80 80 (:REWRITE |(+ c (+ d x))|))
 (80 10 (:REWRITE |(- (* c x))|))
 (60 57 (:REWRITE DEFAULT-EXPT-2))
 (58 58 (:TYPE-PRESCRIPTION FIX))
 (57 57 (:REWRITE DEFAULT-EXPT-1))
 (57 57 (:REWRITE |(expt 1/c n)|))
 (57 57 (:REWRITE |(expt (- x) n)|))
 (57 5
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (56 8 (:REWRITE INTP-2))
 (55 11 (:REWRITE |(* a (/ a) b)|))
 (55 4 (:REWRITE INTP-4))
 (52 1
     (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (49 1
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (49 1
     (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (46 2 (:REWRITE DEFAULT-MOD-1))
 (46 2 (:REWRITE DEFAULT-FLOOR-1))
 (45 15
     (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (38 1 (:REWRITE ZP-OPEN))
 (30 30 (:TYPE-PRESCRIPTION INTP-+))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (26 26 (:REWRITE |(* c (* d x))|))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (23 2 (:REWRITE NINTP-4))
 (21 3 (:DEFINITION LEN))
 (16 2 (:DEFINITION M1::REV))
 (15 15 (:REWRITE M1::HALF-TAPE-REV))
 (12 2 (:REWRITE NINTP-3))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 2 (:DEFINITION BINARY-APPEND))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 5
    (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
 (5 5 (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5 5
    (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5 5 (:REWRITE M1::MEMBER-SUBSETP))
 (5 5
    (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE |(equal c (/ x))|))
 (5 5 (:REWRITE |(equal c (- x))|))
 (5 5 (:REWRITE |(equal (/ x) c)|))
 (5 5 (:REWRITE |(equal (/ x) (/ y))|))
 (5 5 (:REWRITE |(equal (- x) c)|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-FLOOR-2))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE FLOOR-ZERO . 4))
 (1 1 (:REWRITE FLOOR-ZERO . 3))
 (1 1 (:REWRITE FLOOR-ZERO . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor x 2)| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|)))
(M1::FLOOR-LEMMA-1-SPECIAL-CASE
 (6924 12 (:REWRITE FLOOR-ZERO . 3))
 (6685 1015 (:REWRITE DEFAULT-TIMES-2))
 (6062 1015 (:REWRITE DEFAULT-TIMES-1))
 (6006 18 (:REWRITE FLOOR-=-X/Y . 3))
 (5916 18 (:REWRITE FLOOR-=-X/Y . 2))
 (4938 18 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4818 1062 (:REWRITE DEFAULT-PLUS-2))
 (4577
  4577
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4577
      4577
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4577
     4577
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4577 4577
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4577 4577
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4131 18 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (3542 1062 (:REWRITE DEFAULT-PLUS-1))
 (1355 239 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1280 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1256 1256
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1256 1256
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1256 1256
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (1214 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1100 110 (:REWRITE DEFAULT-DIVIDE))
 (880 58
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (880 58 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (811 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (792 18 (:REWRITE FLOOR-ZERO . 5))
 (774 26 (:LINEAR EXPT->-1-ONE))
 (774 18 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (664 72 (:META META-INTEGERP-CORRECT))
 (646 58 (:REWRITE DEFAULT-LESS-THAN-1))
 (616 58 (:REWRITE SIMPLIFY-SUMS-<))
 (612 18 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (612 18 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (589 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (589 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (589 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (570 252 (:REWRITE DEFAULT-MINUS))
 (498 12 (:REWRITE |(floor (+ x r) i)|))
 (492 18
      (:REWRITE |(* (expt x m) (expt x n))|))
 (484 484
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (484 484
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (484 484
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (484 484
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (462 12 (:REWRITE FLOOR-ZERO . 2))
 (356 26 (:REWRITE ODD-EXPT-THM))
 (343 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (343 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (292 58 (:REWRITE DEFAULT-LESS-THAN-2))
 (244 244 (:REWRITE DEFAULT-EXPT-2))
 (244 244 (:REWRITE DEFAULT-EXPT-1))
 (244 244 (:REWRITE |(expt 1/c n)|))
 (244 244 (:REWRITE |(expt (- x) n)|))
 (232 232
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (180 18 (:REWRITE DEFAULT-FLOOR-2))
 (180 18 (:REWRITE DEFAULT-FLOOR-1))
 (108 12
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (86 26 (:LINEAR EXPT-<=-1-TWO))
 (85 58
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (76 26 (:LINEAR EXPT-X->=-X))
 (76 26 (:LINEAR EXPT-X->-X))
 (72 72 (:REWRITE REDUCE-INTEGERP-+))
 (72 72 (:REWRITE INTEGERP-MINUS-X))
 (58 58 (:REWRITE THE-FLOOR-BELOW))
 (58 58 (:REWRITE THE-FLOOR-ABOVE))
 (58 58
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (58 58
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (58 58
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (58 58 (:REWRITE INTEGERP-<-CONSTANT))
 (58 58 (:REWRITE CONSTANT-<-INTEGERP))
 (58 58
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (58 58
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (58 58
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (58 58
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (58 58 (:REWRITE |(< c (- x))|))
 (58 58
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (58 58
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (58 58
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (58 58
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (58 58 (:REWRITE |(< (/ x) (/ y))|))
 (58 58 (:REWRITE |(< (- x) c)|))
 (58 58 (:REWRITE |(< (- x) (- y))|))
 (52 52
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (52 52
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (52 52
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (48 48 (:REWRITE |(+ c (+ d x))|))
 (42 42 (:REWRITE FOLD-CONSTS-IN-+))
 (36 36 (:REWRITE |(< (+ c/d x) y)|))
 (36 36 (:REWRITE |(< (+ (- c) x) y)|))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (26 26
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (26 26 (:LINEAR EXPT-LINEAR-UPPER-<))
 (26 26 (:LINEAR EXPT-LINEAR-LOWER-<))
 (26 26 (:LINEAR EXPT->=-1-TWO))
 (26 26 (:LINEAR EXPT->-1-TWO))
 (26 26 (:LINEAR EXPT-<=-1-ONE))
 (26 26 (:LINEAR EXPT-<-1-TWO))
 (26 26 (:LINEAR EXPT-<-1-ONE))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (12 12
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (12 12
     (:REWRITE EXPT-EXCEEDS-ANOTHER-BY-MORE-THAN-Y))
 (12 12 (:REWRITE |(< 0 (/ x))|))
 (12 12 (:REWRITE |(< 0 (* x y))|))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (1 1 (:REWRITE |(* c (* d x))|)))
(M1::LOG2-SUM-COROLLARY2
 (51
   51
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (51
  51
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 2))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::HALF-TAPE-BELOW-EXPT-RULE3
 (23552 1 (:DEFINITION M1::NAT-TO-HALF-TAPE))
 (12842 2 (:REWRITE DEFAULT-MOD-RATIO))
 (10505 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4705 464 (:REWRITE DEFAULT-TIMES-2))
 (3963 87 (:REWRITE RATIONALP-X))
 (2841 60 (:META META-RATIONALP-CORRECT))
 (2567 857
       (:TYPE-PRESCRIPTION M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (2555 511
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2444 78 (:REWRITE |(* (/ c) (expt d n))|))
 (2328 54
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (1704 175 (:REWRITE DEFAULT-PLUS-2))
 (1614
  1614
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1614
      1614
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1614
     1614
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1614 1614
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1614 1614
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1508 144 (:META META-INTEGERP-CORRECT))
 (1508 26 (:REWRITE BUBBLE-DOWN-*-BUBBLE-DOWN))
 (1498 464 (:REWRITE DEFAULT-TIMES-1))
 (1485 60 (:REWRITE REDUCE-RATIONALP-+))
 (1040 1 (:REWRITE MOD-X-Y-=-X . 4))
 (1040 1
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1009 1 (:REWRITE MOD-ZERO . 4))
 (1009 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1009 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1009 1 (:REWRITE FLOOR-ZERO . 5))
 (1009 1 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (1009 1 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (1009 1 (:REWRITE CANCEL-FLOOR-+))
 (930 175 (:REWRITE DEFAULT-PLUS-1))
 (857 857
      (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (714 1 (:REWRITE CANCEL-MOD-+))
 (714 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (683 1
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (683 1 (:REWRITE MOD-CANCEL-*-CONST))
 (683 1
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (683 1 (:REWRITE FLOOR-CANCEL-*-CONST))
 (683 1
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (683 1
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (636 76 (:REWRITE RATIONALP-MINUS-X))
 (628 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (616 1 (:REWRITE MOD-ZERO . 3))
 (616 1 (:REWRITE FLOOR-=-X/Y . 3))
 (616 1 (:REWRITE FLOOR-=-X/Y . 2))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (511 511
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (500 71 (:REWRITE REDUCE-RATIONALP-*))
 (384 149 (:REWRITE INTEGERP-MINUS-X))
 (186 2 (:REWRITE |(floor (+ x r) i)|))
 (172 172
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (172 172 (:REWRITE NORMALIZE-ADDENDS))
 (144 144 (:REWRITE REDUCE-INTEGERP-+))
 (125 106 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (114 1 (:REWRITE |(mod x 2)| . 1))
 (114 1 (:REWRITE |(floor x 2)| . 1))
 (111 1
      (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (111 1
      (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 1))
 (109 109 (:REWRITE FOLD-CONSTS-IN-+))
 (109 109 (:REWRITE |(+ c (+ d x))|))
 (90 10 (:REWRITE DEFAULT-MINUS))
 (88 85 (:REWRITE DEFAULT-EXPT-2))
 (85 85 (:REWRITE DEFAULT-EXPT-1))
 (85 85 (:REWRITE |(expt 1/c n)|))
 (85 85 (:REWRITE |(expt (- x) n)|))
 (80 10 (:REWRITE |(- (* c x))|))
 (64 2 (:REWRITE DEFAULT-MOD-1))
 (64 2 (:REWRITE DEFAULT-FLOOR-1))
 (58 58 (:TYPE-PRESCRIPTION FIX))
 (56 8 (:REWRITE INTP-2))
 (55 11 (:REWRITE |(* a (/ a) b)|))
 (55 4 (:REWRITE INTP-4))
 (52 1
     (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (49 1
     (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (49 1
     (:REWRITE |(floor (+ x y) z) where (< z 0)| . 1))
 (45 15
     (:REWRITE M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (38 1 (:REWRITE ZP-OPEN))
 (30 30 (:TYPE-PRESCRIPTION INTP-+))
 (28 28
     (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (26 26 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (26 26 (:REWRITE |(* c (* d x))|))
 (26 2 (:REWRITE ACL2-NUMBERP-X))
 (24 3 (:DEFINITION M1::REV))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (23 2 (:REWRITE NINTP-4))
 (15 3 (:DEFINITION BINARY-APPEND))
 (14 2 (:DEFINITION LEN))
 (12 2 (:REWRITE NINTP-3))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE META-INTEGERP-UNHIDE-HIDE))
 (7 7 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-MOD-2))
 (2 2 (:REWRITE DEFAULT-FLOOR-2))
 (2 1
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 1 (:REWRITE DEFAULT-LESS-THAN-2))
 (1 1 (:REWRITE THE-FLOOR-BELOW))
 (1 1 (:REWRITE THE-FLOOR-ABOVE))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1 1
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1 1
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE INTEGERP-<-CONSTANT))
 (1 1 (:REWRITE FLOOR-ZERO . 4))
 (1 1 (:REWRITE FLOOR-ZERO . 3))
 (1 1 (:REWRITE FLOOR-ZERO . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1 1 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (1 1
    (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
 (1 1 (:REWRITE CONSTANT-<-INTEGERP))
 (1 1 (:REWRITE |(mod x 2)| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (1 1
    (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor x 2)| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 2))
 (1 1 (:REWRITE |(floor x (- y))| . 1))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(floor (- x) y)| . 2))
 (1 1 (:REWRITE |(floor (- x) y)| . 1))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< z 0)| . 2))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 3))
 (1 1
    (:REWRITE |(floor (+ x y) z) where (< 0 z)| . 2))
 (1 1
    (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< c (- x))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1 1
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1 1 (:REWRITE |(< (/ x) (/ y))|))
 (1 1 (:REWRITE |(< (- x) c)|))
 (1 1 (:REWRITE |(< (- x) (- y))|)))
(M1::FLOOR-LEMMA-1-SPECIAL-CASE-2
 (7814 952 (:REWRITE DEFAULT-PLUS-2))
 (6822 6 (:REWRITE FLOOR-ZERO . 3))
 (6808 886 (:REWRITE DEFAULT-TIMES-2))
 (5689 886 (:REWRITE DEFAULT-TIMES-1))
 (5607 6 (:REWRITE FLOOR-ZERO . 4))
 (5490 6 (:REWRITE FLOOR-=-X/Y . 3))
 (5424 6 (:REWRITE FLOOR-=-X/Y . 2))
 (4488 6 (:REWRITE DEFAULT-FLOOR-RATIO))
 (4480
  4480
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4480
      4480
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4480
     4480
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4480 4480
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4480 4480
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (3718 40 (:REWRITE SIMPLIFY-SUMS-<))
 (3573 952 (:REWRITE DEFAULT-PLUS-1))
 (3390 6 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2144 32
       (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1896 2 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (1846 46
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1830 2 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (1383 249 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1158 1158
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1158 1158
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1158 1158
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1158 1158
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-2))
 (1158 1158
       (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (859 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (742 46 (:REWRITE DEFAULT-LESS-THAN-1))
 (730 40
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (730 40 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (634 42 (:META META-INTEGERP-CORRECT))
 (613 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (613 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (613 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (500 50 (:REWRITE DEFAULT-DIVIDE))
 (492 6 (:REWRITE |(floor (+ x r) i)|))
 (474 20 (:LINEAR EXPT->-1-ONE))
 (472 472
      (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (472 472
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (472 472
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (472 472
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (420 6 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (371 14 (:REWRITE ODD-EXPT-THM))
 (366 6 (:REWRITE FLOOR-ZERO . 5))
 (354 18
      (:REWRITE |(* (expt x m) (expt x n))|))
 (343 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (343 49 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (343 49
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (279 279
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (258 6 (:REWRITE FLOOR-ZERO . 2))
 (258 6 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (258 6 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (224 146 (:REWRITE DEFAULT-MINUS))
 (172 46 (:REWRITE DEFAULT-LESS-THAN-2))
 (168 6 (:REWRITE DEFAULT-FLOOR-1))
 (155 155 (:REWRITE DEFAULT-EXPT-2))
 (155 155 (:REWRITE DEFAULT-EXPT-1))
 (155 155 (:REWRITE |(expt 1/c n)|))
 (155 155 (:REWRITE |(expt (- x) n)|))
 (146 146 (:REWRITE FOLD-CONSTS-IN-+))
 (80 20 (:LINEAR EXPT-<=-1-TWO))
 (80 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (72 6 (:REWRITE |(* x (expt x n))|))
 (70 20 (:LINEAR EXPT-X->=-X))
 (70 20 (:LINEAR EXPT-X->-X))
 (67 40
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (60 6 (:REWRITE DEFAULT-FLOOR-2))
 (46 46 (:REWRITE THE-FLOOR-BELOW))
 (46 46 (:REWRITE THE-FLOOR-ABOVE))
 (46 46
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (46 46
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (42 42 (:REWRITE REDUCE-INTEGERP-+))
 (42 42 (:REWRITE INTEGERP-MINUS-X))
 (40 40 (:REWRITE INTEGERP-<-CONSTANT))
 (40 40 (:REWRITE CONSTANT-<-INTEGERP))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< c (- x))|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (40 40
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (40 40 (:REWRITE |(< (/ x) (/ y))|))
 (40 40 (:REWRITE |(< (- x) c)|))
 (40 40 (:REWRITE |(< (- x) (- y))|))
 (40 40
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (30 30 (:REWRITE |(< (+ c/d x) y)|))
 (24 24 (:REWRITE |(< (+ (- c) x) y)|))
 (20 20 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (20 20
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (20 20 (:LINEAR EXPT-LINEAR-UPPER-<))
 (20 20 (:LINEAR EXPT-LINEAR-LOWER-<))
 (20 20 (:LINEAR EXPT->=-1-TWO))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT-<=-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-TWO))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< (/ x) 0)|))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (6 6 (:REWRITE |(- (* c x))|))
 (1 1 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (1 1 (:REWRITE |(* c (* d x))|)))
(M1::LOG2-SUM-COROLLARY3
 (51
   51
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (51
  51
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (51 51
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (31 1 (:LINEAR EXPT-<=-1-TWO))
 (30 1 (:LINEAR EXPT->-1-ONE))
 (26 1 (:LINEAR EXPT-X->=-X))
 (26 1 (:LINEAR EXPT-X->-X))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4
    (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4
    (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4
    (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (4 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (- x))|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4
    (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-EXPT-1))
 (3 3 (:REWRITE |(expt 1/c n)|))
 (3 3 (:REWRITE |(expt (- x) n)|))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 2))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1 1 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::HALF-TAPE-BELOW-EXPT-RULE4
 (164 20 (:REWRITE ACL2-NUMBERP-X))
 (114 10
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (100 2
      (:DEFINITION M1::CONVERT-HALF-TAPE-TO-NAT))
 (82 10 (:REWRITE DEFAULT-PLUS-1))
 (48 12 (:REWRITE RATIONALP-X))
 (48 12
     (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (46 10 (:REWRITE DEFAULT-PLUS-2))
 (28 4 (:DEFINITION LEN))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (19 3 (:REWRITE DEFAULT-TIMES-2))
 (18 10
     (:TYPE-PRESCRIPTION M1::NATP-CONVERT-HALF-TAPE-TO-NAT))
 (18 10
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (12 12 (:REWRITE REDUCE-RATIONALP-+))
 (12 12 (:REWRITE REDUCE-RATIONALP-*))
 (12 12 (:REWRITE RATIONALP-MINUS-X))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:META META-RATIONALP-CORRECT))
 (10 10
     (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10 (:REWRITE M1::MEMBER-SUBSETP))
 (10 10
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (8 8
    (:TYPE-PRESCRIPTION M1::CONVERT-HALF-TAPE-TO-NAT))
 (8 8
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-CDR))
 (4
  4
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (4 4
    (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:REWRITE DEFAULT-TIMES-1))
 (2 2
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|)))
(M1::LOG2-SUM-COROLLARY4)
(M1::FLOOR-LEMMA-1-SPECIAL-CASE-3
 (4122 36 (:REWRITE |(* y x)|))
 (3882 12 (:REWRITE |(* x (+ y z))|))
 (2916 3 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (2796 3 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (2592 24 (:REWRITE |(* y (* x z))|))
 (1872 54
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1626 198 (:REWRITE DEFAULT-TIMES-2))
 (1146 198 (:REWRITE DEFAULT-TIMES-1))
 (1051
  1051
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1051
      1051
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1051
     1051
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1051 1051
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1051 1051
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (1050 30 (:REWRITE BUBBLE-DOWN-*-MATCH-1))
 (903 903
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (903 903
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (903 903
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (651 39 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (588 588
      (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (528 18 (:REWRITE |(+ y (+ x z))|))
 (516 6 (:REWRITE |(/ (* x y))|))
 (447 39
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (447 39
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (447 39
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (444 12
      (:REWRITE |(* (expt c m) (expt d n))|))
 (414 90 (:REWRITE DEFAULT-PLUS-2))
 (384 12 (:REWRITE |(* (/ c) (expt d n))|))
 (264 90 (:REWRITE DEFAULT-PLUS-1))
 (243 39 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (243 39 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (243 39
      (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (192 6 (:REWRITE |(* c (expt d n))|))
 (186 12 (:META META-INTEGERP-CORRECT))
 (150 42 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (138 6 (:REWRITE |(+ y x)|))
 (120 12 (:REWRITE DEFAULT-DIVIDE))
 (114 42 (:REWRITE NORMALIZE-ADDENDS))
 (91 4 (:LINEAR EXPT->-1-ONE))
 (79 4 (:LINEAR EXPT-X->=-X))
 (79 4 (:LINEAR EXPT-X->-X))
 (77 16 (:REWRITE |(< (- x) c)|))
 (56 4 (:LINEAR EXPT-<-1-TWO))
 (42 42 (:REWRITE |(* 1 x)|))
 (41 41 (:REWRITE |arith (expt x c)|))
 (37 37 (:REWRITE |arith (expt 1/c n)|))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (36 36 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (36 6 (:REWRITE |(/ (expt x n))|))
 (30 30
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 12 (:REWRITE |(+ c (+ d x))|))
 (30 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4E-EXPT))
 (30 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3E-EXPT))
 (30 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2E-EXPT))
 (30 6
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1E-EXPT))
 (30 6 (:REWRITE |(* x (- y))|))
 (24 24 (:REWRITE DEFAULT-EXPT-2))
 (24 24 (:REWRITE DEFAULT-EXPT-1))
 (24 24 (:REWRITE |(expt 1/c n)|))
 (24 24 (:REWRITE |(expt (- x) n)|))
 (24 12 (:REWRITE BUBBLE-DOWN-+-MATCH-1))
 (16 16 (:REWRITE THE-FLOOR-BELOW))
 (16 16 (:REWRITE THE-FLOOR-ABOVE))
 (16 16
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (16 16
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (16 16 (:REWRITE DEFAULT-LESS-THAN-2))
 (16 16 (:REWRITE DEFAULT-LESS-THAN-1))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< c (- x))|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (16 16
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (16 16 (:REWRITE |(< (/ x) (/ y))|))
 (16 16 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE SIMPLIFY-SUMS-<))
 (14 14
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (14 14
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 14 (:REWRITE INTEGERP-<-CONSTANT))
 (14 14 (:REWRITE DEFAULT-MINUS))
 (14 14 (:REWRITE CONSTANT-<-INTEGERP))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-4B-EXPT))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3B-EXPT))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2B-EXPT))
 (12 12
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1B-EXPT))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:REWRITE |(+ x (- x))|))
 (8 8 (:REWRITE |arith (+ c (+ d x))|))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-4G-EXPT-B))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-3G-EXPT-B))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-2G-EXPT-B))
 (6 6
    (:TYPE-PRESCRIPTION NOT-INTEGERP-1G-EXPT-B))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE |(+ 0 x)|))
 (6 6 (:REWRITE |(* a (/ a) b)|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (4 4
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (2 2 (:REWRITE |(- (- x))|))
 (1 1 (:REWRITE |arith (- (* c x))|))
 (1 1 (:REWRITE |arith (* (- x) y)|)))
(M1::RATIONALP-INTP-+ (1 1
                         (:TYPE-PRESCRIPTION M1::RATIONALP-INTP-+)))
(M1::NEW-TAPE2-CONVERT-TAPE-TO-TAPEN-TRANSFORMED
 (4283 659 (:REWRITE DEFAULT-PLUS-1))
 (4134 659 (:REWRITE DEFAULT-PLUS-2))
 (3132 348 (:REWRITE ACL2-NUMBERP-X))
 (1875 3 (:REWRITE M1::LOG2-SUM-COROLLARY2))
 (1721 174
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1711 293 (:REWRITE DEFAULT-TIMES-2))
 (928 232 (:REWRITE RATIONALP-X))
 (928 232
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (792
  792
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (792 792
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (792
     792
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (792 792
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (792 792
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (741 293 (:REWRITE DEFAULT-TIMES-1))
 (702 629 (:REWRITE DEFAULT-CDR))
 (556 483 (:REWRITE DEFAULT-CAR))
 (475 475 (:REWRITE INTEGERP-MINUS-X))
 (474 474 (:META META-INTEGERP-CORRECT))
 (437 437
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (329 174
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (232 232 (:REWRITE REDUCE-RATIONALP-+))
 (232 232 (:REWRITE REDUCE-RATIONALP-*))
 (232 232 (:REWRITE RATIONALP-MINUS-X))
 (232 232 (:META META-RATIONALP-CORRECT))
 (226 101 (:REWRITE DEFAULT-EXPT-2))
 (175 35 (:DEFINITION BINARY-APPEND))
 (174 174
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (174 174
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (174 174
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (174 174 (:REWRITE |(equal c (/ x))|))
 (174 174 (:REWRITE |(equal c (- x))|))
 (174 174 (:REWRITE |(equal (/ x) c)|))
 (174 174 (:REWRITE |(equal (/ x) (/ y))|))
 (174 174 (:REWRITE |(equal (- x) c)|))
 (174 174 (:REWRITE |(equal (- x) (- y))|))
 (156 2 (:REWRITE |(integerp (expt x n))|))
 (150 3 (:REWRITE ODD-EXPT-THM))
 (141 1 (:REWRITE DEFAULT-MOD-RATIO))
 (140 140
      (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (140 140 (:REWRITE M1::MEMBER-SUBSETP))
 (138 3 (:LINEAR EXPT->-1-ONE))
 (138 3 (:LINEAR EXPT-<=-1-TWO))
 (134 25 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (132 25
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (126 3 (:LINEAR EXPT-X->=-X))
 (126 3 (:LINEAR EXPT-X->-X))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (118 118
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (103 25 (:REWRITE SIMPLIFY-SUMS-<))
 (101 101 (:REWRITE DEFAULT-EXPT-1))
 (101 101 (:REWRITE |(expt 1/c n)|))
 (101 101 (:REWRITE |(expt (- x) n)|))
 (85 25 (:REWRITE DEFAULT-LESS-THAN-2))
 (80 40 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (74 25 (:REWRITE DEFAULT-LESS-THAN-1))
 (67 67
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (66 66 (:REWRITE FOLD-CONSTS-IN-+))
 (66 3 (:LINEAR EXPT->=-1-ONE))
 (48 6 (:REWRITE DEFAULT-MINUS))
 (25 25 (:REWRITE THE-FLOOR-BELOW))
 (25 25 (:REWRITE THE-FLOOR-ABOVE))
 (25 25
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (25 25
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (25 25
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (25 25 (:REWRITE INTEGERP-<-CONSTANT))
 (25 25 (:REWRITE CONSTANT-<-INTEGERP))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< c (- x))|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (25 25
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (25 25 (:REWRITE |(< (/ x) (/ y))|))
 (25 25 (:REWRITE |(< (- x) c)|))
 (25 25 (:REWRITE |(< (- x) (- y))|))
 (14 14 (:REWRITE |(< y (+ (- c) x))|))
 (14 14 (:REWRITE |(< x (+ c/d y))|))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (13 13 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (13 13 (:REWRITE |(* c (* d x))|))
 (12 1 (:REWRITE DEFAULT-MOD-1))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (9 9
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (9 9 (:REWRITE |(< 0 (/ x))|))
 (9 9 (:REWRITE |(< 0 (* x y))|))
 (9 3 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (9 3 (:LINEAR EXPT-<-1-TWO))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (7 7
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (7 7 (:REWRITE |(< (/ x) 0)|))
 (7 7 (:REWRITE |(< (+ c/d x) y)|))
 (7 7 (:REWRITE |(< (+ (- c) x) y)|))
 (7 7 (:REWRITE |(< (* x y) 0)|))
 (6 6 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (6 6
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (6 6
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-UPPER-<))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (3 3 (:LINEAR EXPT-LINEAR-LOWER-<))
 (3 3 (:LINEAR EXPT->=-1-TWO))
 (3 3 (:LINEAR EXPT->-1-TWO))
 (3 3 (:LINEAR EXPT-<=-1-ONE))
 (3 3 (:LINEAR EXPT-<-1-ONE))
 (2 2 (:REWRITE |(equal x (if a b c))|))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE |(mod x 2)| . 2)))
(M1::NEW-TAPE2-CONVERT-TAPE-TO-TAPEN-POS
     (456 40
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (448 64 (:REWRITE ACL2-NUMBERP-X))
     (128 32 (:REWRITE RATIONALP-X))
     (128 32
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (72 40
         (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (65 65 (:REWRITE REDUCE-INTEGERP-+))
     (65 65 (:REWRITE INTEGERP-MINUS-X))
     (65 65 (:META META-INTEGERP-CORRECT))
     (60 60 (:REWRITE DEFAULT-CAR))
     (40 40
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (40 40 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (40 40
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (40 40
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (40 40 (:REWRITE M1::MEMBER-SUBSETP))
     (40 40
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (40 40 (:REWRITE |(equal c (/ x))|))
     (40 40 (:REWRITE |(equal c (- x))|))
     (40 40 (:REWRITE |(equal (/ x) c)|))
     (40 40 (:REWRITE |(equal (/ x) (/ y))|))
     (40 40 (:REWRITE |(equal (- x) c)|))
     (40 40 (:REWRITE |(equal (- x) (- y))|))
     (32 32 (:REWRITE REDUCE-RATIONALP-+))
     (32 32 (:REWRITE REDUCE-RATIONALP-*))
     (32 32 (:REWRITE RATIONALP-MINUS-X))
     (32 32 (:META META-RATIONALP-CORRECT))
     (28 28 (:REWRITE DEFAULT-CDR))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (1 1 (:REWRITE THE-FLOOR-BELOW))
     (1 1 (:REWRITE THE-FLOOR-ABOVE))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (1 1
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (1 1 (:REWRITE SIMPLIFY-SUMS-<))
     (1 1
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (1 1 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (1 1
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (1 1
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1 1 (:REWRITE INTEGERP-<-CONSTANT))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-2))
     (1 1 (:REWRITE DEFAULT-LESS-THAN-1))
     (1 1 (:REWRITE CONSTANT-<-INTEGERP))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< c (- x))|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (1 1
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (1 1 (:REWRITE |(< (/ x) 0)|))
     (1 1 (:REWRITE |(< (/ x) (/ y))|))
     (1 1 (:REWRITE |(< (- x) c)|))
     (1 1 (:REWRITE |(< (- x) (- y))|))
     (1 1 (:REWRITE |(< (* x y) 0)|)))
(M1::TMI3 (104 1 (:DEFINITION M1::NINSTR))
          (34 1 (:DEFINITION NATP))
          (21 4
              (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
          (15 3 (:REWRITE ACL2-NUMBERP-X))
          (10 8 (:REWRITE DEFAULT-PLUS-1))
          (9 4
             (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
          (8 8 (:REWRITE DEFAULT-PLUS-2))
          (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
          (5 5
             (:TYPE-PRESCRIPTION M1::POSITIVE-NATP-NNIL))
          (5 5 (:TYPE-PRESCRIPTION M1::NSYM))
          (5 5 (:REWRITE THE-FLOOR-BELOW))
          (5 5 (:REWRITE THE-FLOOR-ABOVE))
          (5 5
             (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
          (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES))
          (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
          (5 5
             (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
          (5 5
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
          (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
          (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
          (5 5 (:REWRITE INTEGERP-<-CONSTANT))
          (5 5 (:REWRITE DEFAULT-LESS-THAN-2))
          (5 5 (:REWRITE DEFAULT-LESS-THAN-1))
          (5 5 (:REWRITE CONSTANT-<-INTEGERP))
          (5 5
             (:REWRITE |(< c (/ x)) positive c --- present in goal|))
          (5 5
             (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
          (5 5
             (:REWRITE |(< c (/ x)) negative c --- present in goal|))
          (5 5
             (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
          (5 5 (:REWRITE |(< c (- x))|))
          (5 5
             (:REWRITE |(< (/ x) c) positive c --- present in goal|))
          (5 5
             (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
          (5 5
             (:REWRITE |(< (/ x) c) negative c --- present in goal|))
          (5 5
             (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
          (5 5 (:REWRITE |(< (/ x) (/ y))|))
          (5 5 (:REWRITE |(< (- x) c)|))
          (5 5 (:REWRITE |(< (- x) (- y))|))
          (4 4
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
          (4 4
             (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
          (4 4
             (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
          (4 4 (:REWRITE REDUCE-INTEGERP-+))
          (4 4
             (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
          (4 4 (:REWRITE INTEGERP-MINUS-X))
          (4 4
             (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
          (4 4 (:REWRITE |(equal c (/ x))|))
          (4 4 (:REWRITE |(equal c (- x))|))
          (4 4 (:REWRITE |(equal (/ x) c)|))
          (4 4 (:REWRITE |(equal (/ x) (/ y))|))
          (4 4 (:REWRITE |(equal (- x) c)|))
          (4 4 (:REWRITE |(equal (- x) (- y))|))
          (4 4 (:REWRITE |(< (/ x) 0)|))
          (4 4 (:REWRITE |(< (* x y) 0)|))
          (4 4 (:META META-INTEGERP-CORRECT))
          (4 1 (:REWRITE RATIONALP-X))
          (4 1
             (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
          (2 2 (:TYPE-PRESCRIPTION M1::NST-IN))
          (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
          (2 2 (:REWRITE ZP-OPEN))
          (2 2 (:REWRITE |(< (+ c/d x) y)|))
          (2 2 (:REWRITE |(< (+ (- c) x) y)|))
          (1 1 (:REWRITE REDUCE-RATIONALP-+))
          (1 1 (:REWRITE REDUCE-RATIONALP-*))
          (1 1 (:REWRITE RATIONALP-MINUS-X))
          (1 1
             (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
          (1 1 (:META META-RATIONALP-CORRECT)))
(M1::NOP-NINSTR
 (861
  861
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (861 861
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (861
     861
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (861 861
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (861 861
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (310 10 (:REWRITE ODD-EXPT-THM))
 (310 10 (:LINEAR EXPT-<=-1-TWO))
 (300 10 (:LINEAR EXPT->-1-ONE))
 (260 10 (:LINEAR EXPT-X->=-X))
 (260 10 (:LINEAR EXPT-X->-X))
 (217 113
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (217 113
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (211 120 (:REWRITE DEFAULT-LESS-THAN-2))
 (203 113 (:REWRITE SIMPLIFY-SUMS-<))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (156 156
      (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (135 120 (:REWRITE DEFAULT-LESS-THAN-1))
 (125 120
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (120 120 (:REWRITE THE-FLOOR-BELOW))
 (120 120 (:REWRITE THE-FLOOR-ABOVE))
 (120 120
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (120 120
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (120 120
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (120 120 (:REWRITE INTEGERP-<-CONSTANT))
 (120 120 (:REWRITE CONSTANT-<-INTEGERP))
 (120 120
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (120 120
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (120 120
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (120 120
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (120 120 (:REWRITE |(< c (- x))|))
 (120 120
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (120 120
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (120 120
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (120 120 (:REWRITE |(< (/ x) (/ y))|))
 (120 120 (:REWRITE |(< (- x) c)|))
 (120 120 (:REWRITE |(< (- x) (- y))|))
 (119 21 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (119 21 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (119 21
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (119 21
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (86 43
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (86 43
     (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80 80
     (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (77 43 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (66 1 (:REWRITE CANCEL-MOD-+))
 (62 34 (:REWRITE INTEGERP-MINUS-X))
 (44 1 (:REWRITE MOD-X-Y-=-X . 4))
 (44 1 (:REWRITE MOD-X-Y-=-X . 3))
 (43 43
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (43 43
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (43 43
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (43 43 (:REWRITE |(equal c (/ x))|))
 (43 43 (:REWRITE |(equal c (- x))|))
 (43 43 (:REWRITE |(equal (/ x) c)|))
 (43 43 (:REWRITE |(equal (/ x) (/ y))|))
 (43 43 (:REWRITE |(equal (- x) c)|))
 (43 43 (:REWRITE |(equal (- x) (- y))|))
 (42 1 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (40 40 (:REWRITE DEFAULT-EXPT-2))
 (40 40 (:REWRITE DEFAULT-EXPT-1))
 (40 40 (:REWRITE |(expt 1/c n)|))
 (40 40 (:REWRITE |(expt (- x) n)|))
 (40 40 (:REWRITE |(< (/ x) 0)|))
 (40 40 (:REWRITE |(< (* x y) 0)|))
 (39 1 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (35 35
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (33 33 (:REWRITE REDUCE-INTEGERP-+))
 (33 33 (:META META-INTEGERP-CORRECT))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (31 31
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (31 31 (:REWRITE |(< 0 (/ x))|))
 (31 31 (:REWRITE |(< 0 (* x y))|))
 (30 2 (:TYPE-PRESCRIPTION M1::NOP-NINSTR))
 (27 1 (:REWRITE MOD-ZERO . 4))
 (27 1 (:REWRITE MOD-ZERO . 3))
 (27 1 (:LINEAR MOD-BOUNDS-3))
 (24 24 (:TYPE-PRESCRIPTION NATP))
 (22 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (21 21 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (21 21
     (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (21 21 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (21 21
     (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (21 2 (:REWRITE |(* (- x) y)|))
 (20 20
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (20 20
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (20 20
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (20 4 (:REWRITE |(* y x)|))
 (17 11 (:REWRITE DEFAULT-TIMES-2))
 (16 11 (:REWRITE DEFAULT-TIMES-1))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (14 1 (:REWRITE DEFAULT-MOD-RATIO))
 (12 2 (:REWRITE DEFAULT-MINUS))
 (12 2 (:LINEAR MOD-BOUNDS-2))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (11 11 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (11 11 (:REWRITE ZP-OPEN))
 (11 2 (:REWRITE |(- (* c x))|))
 (10 10 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (10 10
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (10 10 (:LINEAR EXPT-LINEAR-UPPER-<))
 (10 10 (:LINEAR EXPT-LINEAR-LOWER-<))
 (10 10 (:LINEAR EXPT->=-1-TWO))
 (10 10 (:LINEAR EXPT->-1-TWO))
 (10 10 (:LINEAR EXPT-<=-1-ONE))
 (10 10 (:LINEAR EXPT-<-1-TWO))
 (10 10 (:LINEAR EXPT-<-1-ONE))
 (7 1 (:REWRITE MOD-X-Y-=-X . 2))
 (7 1 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (7 1
    (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (6 6
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 1 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (6 1 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (6 1
    (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (6 1 (:REWRITE MOD-CANCEL-*-CONST))
 (6 1
    (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (2 1 (:REWRITE DEFAULT-MOD-1))
 (1 1
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1
    (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (1 1 (:REWRITE DEFAULT-MOD-2))
 (1 1 (:REWRITE |(mod x (- y))| . 3))
 (1 1 (:REWRITE |(mod x (- y))| . 2))
 (1 1 (:REWRITE |(mod x (- y))| . 1))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (1 1
    (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (1 1 (:REWRITE |(mod (- x) y)| . 3))
 (1 1 (:REWRITE |(mod (- x) y)| . 2))
 (1 1 (:REWRITE |(mod (- x) y)| . 1))
 (1 1
    (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|)))
(M1::NST-OUT-NINSTR
 (31259 34 (:REWRITE MOD-X-Y-=-X . 3))
 (23509 34 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (18673 25 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (17336 1378 (:REWRITE DEFAULT-TIMES-2))
 (16882 16882
        (:TYPE-PRESCRIPTION INTEGERP-/-EXPT-1))
 (16870 16870
        (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (16870 16870
        (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (16870 16870
        (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (16276 986 (:REWRITE DEFAULT-PLUS-2))
 (15109 34 (:REWRITE MOD-X-Y-=-X . 4))
 (13748 34 (:REWRITE MOD-ZERO . 4))
 (13641 723 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (12246 34 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (11701
  11701
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (11701
      11701
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (11701
     11701
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (11701 11701
        (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (11123 986 (:REWRITE DEFAULT-PLUS-1))
 (9351 723
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9351 723
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9351 723
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (7307 34 (:REWRITE MOD-ZERO . 3))
 (7288 1378 (:REWRITE DEFAULT-TIMES-1))
 (6795 56
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5066 34 (:REWRITE DEFAULT-MOD-RATIO))
 (5061 723 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5061 723 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5061 723
       (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (4074 32 (:REWRITE CANCEL-FLOOR-+))
 (3399 370 (:REWRITE DEFAULT-LESS-THAN-2))
 (2986 169 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2800 32 (:REWRITE FLOOR-ZERO . 3))
 (2787 370 (:REWRITE DEFAULT-LESS-THAN-1))
 (2688 32 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2592 635 (:REWRITE DEFAULT-MINUS))
 (2561 257 (:REWRITE DEFAULT-DIVIDE))
 (2349 32 (:REWRITE FLOOR-ZERO . 4))
 (2029 34 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (2029 34
       (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (2015 377 (:REWRITE THE-FLOOR-BELOW))
 (1832 32 (:REWRITE FLOOR-=-X/Y . 2))
 (1723 34 (:REWRITE MOD-X-Y-=-X . 2))
 (1606 32 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1566 369 (:REWRITE |(< (- x) (- y))|))
 (1561 223 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (1561 223 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1501 223
       (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1501 223
       (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1282 34 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (1282 34 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (1158 32 (:REWRITE FLOOR-=-X/Y . 3))
 (1101 363 (:REWRITE |(< (- x) c)|))
 (1009 32 (:REWRITE FLOOR-ZERO . 5))
 (900 32 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (850 32 (:REWRITE FLOOR-ZERO . 2))
 (850 32 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (850 32 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (844 56
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (718 718 (:REWRITE DEFAULT-EXPT-2))
 (718 718 (:REWRITE DEFAULT-EXPT-1))
 (718 718 (:REWRITE |(expt 1/c n)|))
 (718 718 (:REWRITE |(expt (- x) n)|))
 (672 33
      (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (657 33 (:REWRITE MOD-CANCEL-*-CONST))
 (655 363
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (586 88 (:REWRITE |(< 0 (/ x))|))
 (552 72 (:LINEAR EXPT-<=-1-TWO))
 (532 32 (:REWRITE FLOOR-CANCEL-*-CONST))
 (527 527
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (516 363 (:REWRITE |(< c (- x))|))
 (512 32
      (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (512 32
      (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (475 34 (:REWRITE DEFAULT-MOD-1))
 (407 32
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (406 31
      (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (406 31
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (403 13 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (394 55 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (377 369
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (369 369
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (369 369
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (369 369
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (369 369
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (369 369
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (369 369
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (369 369
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (369 369
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (369 369
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (369 369
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (369 369 (:REWRITE |(< (/ x) (/ y))|))
 (363 363 (:REWRITE INTEGERP-<-CONSTANT))
 (363 363 (:REWRITE CONSTANT-<-INTEGERP))
 (340 34 (:REWRITE DEFAULT-MOD-2))
 (325 181 (:REWRITE INTEGERP-MINUS-X))
 (320 32 (:REWRITE DEFAULT-FLOOR-2))
 (278 14
      (:REWRITE |(* (expt x m) (expt x n))|))
 (223 223 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (223 223
      (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (223 223
      (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (223 223
      (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (210 57 (:REWRITE |(equal (- x) (- y))|))
 (209 56 (:REWRITE |(equal (- x) c)|))
 (208 13 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (187 32
      (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (185 2 (:REWRITE FLOOR-=-X/Y . 4))
 (177 177 (:META META-INTEGERP-CORRECT))
 (144 144
      (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (144 144
      (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (144 144
      (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (121 31
      (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (121 31
      (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (88 88 (:REWRITE |(< 0 (* x y))|))
 (85 1 (:LINEAR MOD-BOUNDS-3))
 (84 84 (:REWRITE |(< (/ x) 0)|))
 (84 84 (:REWRITE |(< (* x y) 0)|))
 (82 32 (:REWRITE DEFAULT-FLOOR-1))
 (79 79
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (79 79
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (77 77
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (77 77
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (72 72 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (72 72
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (72 72 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (72 72 (:LINEAR EXPT-LINEAR-UPPER-<))
 (72 72 (:LINEAR EXPT-LINEAR-LOWER-<))
 (72 72 (:LINEAR EXPT->=-1-TWO))
 (72 72 (:LINEAR EXPT->-1-TWO))
 (72 72 (:LINEAR EXPT-<=-1-ONE))
 (72 72 (:LINEAR EXPT-<-1-TWO))
 (72 72 (:LINEAR EXPT-<-1-ONE))
 (71 57 (:REWRITE |(equal (/ x) c)|))
 (57 57
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (57 57
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (57 57 (:REWRITE |(equal c (/ x))|))
 (57 57 (:REWRITE |(equal (/ x) (/ y))|))
 (56 56 (:TYPE-PRESCRIPTION NATP))
 (56 56
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (56 56 (:REWRITE |(equal c (- x))|))
 (56 8
     (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (50 2 (:LINEAR MOD-BOUNDS-2))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-3A-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-2A-EXPT))
 (38 38
     (:TYPE-PRESCRIPTION NOT-INTEGERP-1A-EXPT))
 (34 1 (:REWRITE FLOOR-POSITIVE . 3))
 (33 33
     (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (32 32 (:REWRITE |(mod x (- y))| . 3))
 (32 32 (:REWRITE |(mod x (- y))| . 2))
 (32 32 (:REWRITE |(mod x (- y))| . 1))
 (32 32
     (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (32 32 (:REWRITE |(mod (- x) y)| . 3))
 (32 32 (:REWRITE |(mod (- x) y)| . 2))
 (32 32 (:REWRITE |(mod (- x) y)| . 1))
 (32 32
     (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (32 2
     (:REWRITE |(equal (floor (+ x y) z) x)|))
 (31 31 (:REWRITE |(floor x (- y))| . 2))
 (31 31 (:REWRITE |(floor x (- y))| . 1))
 (31 31 (:REWRITE |(floor (- x) y)| . 2))
 (31 31 (:REWRITE |(floor (- x) y)| . 1))
 (31 1 (:REWRITE MOD-POSITIVE . 3))
 (31 1 (:REWRITE FLOOR-POSITIVE . 2))
 (31 1 (:REWRITE FLOOR-NONPOSITIVE . 1))
 (30 2
     (:TYPE-PRESCRIPTION M1::NST-OUT-NINSTR))
 (25 1 (:REWRITE MOD-NONPOSITIVE))
 (25 1 (:REWRITE FLOOR-POSITIVE . 4))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 3))
 (25 1 (:REWRITE FLOOR-NONPOSITIVE . 2))
 (18 18 (:REWRITE |(< (+ c/d x) y)|))
 (18 18 (:REWRITE |(< (+ (- c) x) y)|))
 (11 11 (:REWRITE |(< y (+ (- c) x))|))
 (11 11 (:REWRITE |(< x (+ c/d y))|))
 (10 10 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (10 10 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (10 10 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (10 10 (:REWRITE |(* c (* d x))|))
 (10 1 (:REWRITE MOD-POSITIVE . 2))
 (5 5 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (4 4
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE |(equal (+ (- c) x) y)|))
 (3 3
    (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2
    (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE FLOOR-ZERO . 1))
 (1 1 (:REWRITE FLOOR-POSITIVE . 1))
 (1 1 (:REWRITE |(not (equal x (/ y)))|))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE |(/ (/ x))|)))
(M1::TMI3-IS-TMI2
 (2938 534
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1552 534
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1525 139 (:REWRITE ACL2-NUMBERP-X))
 (1515 534 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1090
   1090
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (1090
  1090
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (1090
      1090
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (1090
     1090
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (1090 1090
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (1090 1090
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (534 534
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (534 534
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (534 534
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (534 534 (:REWRITE |(equal c (/ x))|))
 (534 534 (:REWRITE |(equal c (- x))|))
 (534 534 (:REWRITE |(equal (/ x) c)|))
 (534 534 (:REWRITE |(equal (/ x) (/ y))|))
 (534 534 (:REWRITE |(equal (- x) c)|))
 (534 534 (:REWRITE |(equal (- x) (- y))|))
 (525 195 (:REWRITE ZP-OPEN))
 (496 16 (:LINEAR EXPT-<=-1-TWO))
 (480 16 (:LINEAR EXPT->-1-ONE))
 (470 16 (:REWRITE ODD-EXPT-THM))
 (462 48 (:REWRITE RATIONALP-X))
 (462 48
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (416 16 (:LINEAR EXPT-X->=-X))
 (416 16 (:LINEAR EXPT-X->-X))
 (399 147
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (299 147 (:REWRITE SIMPLIFY-SUMS-<))
 (299 147
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (291 147 (:REWRITE DEFAULT-LESS-THAN-2))
 (286 147
      (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (155 147 (:REWRITE DEFAULT-LESS-THAN-1))
 (147 147 (:REWRITE THE-FLOOR-BELOW))
 (147 147 (:REWRITE THE-FLOOR-ABOVE))
 (147 147
      (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (147 147
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (147 147
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (147 147 (:REWRITE INTEGERP-<-CONSTANT))
 (147 147 (:REWRITE CONSTANT-<-INTEGERP))
 (147 147
      (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (147 147
      (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (147 147
      (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (147 147
      (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (147 147 (:REWRITE |(< c (- x))|))
 (147 147
      (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (147 147
      (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (147 147
      (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (147 147
      (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (147 147 (:REWRITE |(< (/ x) (/ y))|))
 (147 147 (:REWRITE |(< (- x) c)|))
 (147 147 (:REWRITE |(< (- x) (- y))|))
 (138 138 (:REWRITE REDUCE-INTEGERP-+))
 (138 138 (:REWRITE INTEGERP-MINUS-X))
 (138 138 (:META META-INTEGERP-CORRECT))
 (99 99 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (67 67 (:REWRITE DEFAULT-EXPT-2))
 (67 67 (:REWRITE DEFAULT-EXPT-1))
 (67 67 (:REWRITE |(expt 1/c n)|))
 (67 67 (:REWRITE |(expt (- x) n)|))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (57 57
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (57 57 (:REWRITE |(< 0 (/ x))|))
 (57 57 (:REWRITE |(< 0 (* x y))|))
 (54 54 (:REWRITE DEFAULT-PLUS-2))
 (54 54 (:REWRITE DEFAULT-PLUS-1))
 (50 10 (:REWRITE |(+ c (+ d x))|))
 (48 48 (:REWRITE REDUCE-RATIONALP-+))
 (48 48 (:REWRITE REDUCE-RATIONALP-*))
 (48 48 (:REWRITE RATIONALP-MINUS-X))
 (48 48 (:META META-RATIONALP-CORRECT))
 (44 44
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (44 44 (:REWRITE NORMALIZE-ADDENDS))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (42 42
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (42 42 (:REWRITE |(< (/ x) 0)|))
 (42 42 (:REWRITE |(< (* x y) 0)|))
 (32 32
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 16 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (16 16
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (16 16 (:LINEAR EXPT->=-1-TWO))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<=-1-ONE))
 (16 16 (:LINEAR EXPT-<-1-TWO))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (10 10 (:REWRITE |(< y (+ (- c) x))|))
 (10 10 (:REWRITE |(< x (+ c/d y))|))
 (3 3
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (3 3 (:REWRITE |(equal x (if a b c))|)))
(M1::TAPEP-TMI2
 (533
   533
   (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (533
  533
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (533
     533
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (533 533
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (248 8 (:LINEAR EXPT-<=-1-TWO))
 (240 8 (:LINEAR EXPT->-1-ONE))
 (217 7 (:REWRITE ODD-EXPT-THM))
 (208 8 (:LINEAR EXPT-X->=-X))
 (208 8 (:LINEAR EXPT-X->-X))
 (200 87
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (200 87
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (193 67
      (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (191 87 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (130 67 (:REWRITE SIMPLIFY-SUMS-<))
 (130 67
      (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (130 67 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (130 67 (:REWRITE DEFAULT-LESS-THAN-2))
 (87 87
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (87 87
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (87 87
     (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (87 87 (:REWRITE |(equal c (/ x))|))
 (87 87 (:REWRITE |(equal c (- x))|))
 (87 87 (:REWRITE |(equal (/ x) c)|))
 (87 87 (:REWRITE |(equal (/ x) (/ y))|))
 (87 87 (:REWRITE |(equal (- x) c)|))
 (87 87 (:REWRITE |(equal (- x) (- y))|))
 (67 67 (:REWRITE THE-FLOOR-BELOW))
 (67 67 (:REWRITE THE-FLOOR-ABOVE))
 (67 67
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (67 67
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (67 67
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (67 67 (:REWRITE INTEGERP-<-CONSTANT))
 (67 67 (:REWRITE DEFAULT-LESS-THAN-1))
 (67 67 (:REWRITE CONSTANT-<-INTEGERP))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< c (- x))|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (67 67
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (67 67 (:REWRITE |(< (/ x) (/ y))|))
 (67 67 (:REWRITE |(< (- x) c)|))
 (67 67 (:REWRITE |(< (- x) (- y))|))
 (43 43 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (36 36 (:REWRITE ZP-OPEN))
 (32 32 (:REWRITE DEFAULT-EXPT-2))
 (32 32 (:REWRITE DEFAULT-EXPT-1))
 (32 32 (:REWRITE |(expt 1/c n)|))
 (32 32 (:REWRITE |(expt (- x) n)|))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (23 23
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (23 23 (:REWRITE |(< 0 (/ x))|))
 (23 23 (:REWRITE |(< 0 (* x y))|))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (21 21
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:REWRITE |(< (/ x) 0)|))
 (21 21 (:REWRITE |(< (* x y) 0)|))
 (21 21 (:META META-INTEGERP-CORRECT))
 (16 16
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (8 8 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (8 8
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (8 8 (:LINEAR EXPT-LINEAR-UPPER-<))
 (8 8 (:LINEAR EXPT-LINEAR-LOWER-<))
 (8 8 (:LINEAR EXPT->=-1-TWO))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT-<=-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (6 6
    (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE NORMALIZE-ADDENDS))
 (6 6 (:REWRITE DEFAULT-PLUS-2))
 (6 6 (:REWRITE DEFAULT-PLUS-1)))
(M1::NATP-CDR-ASSOC-MAP
     (10323 16 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (10279 16 (:DEFINITION M1::TURING-MACHINEP))
     (10188 15 (:DEFINITION M1::TURING-4-TUPLE))
     (9111 177 (:DEFINITION MEMBER-EQUAL))
     (5784 39 (:DEFINITION M1::SYMP))
     (5281 69 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (4507 55
           (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (4227 27
           (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
     (4146 27 (:DEFINITION M1::HALF-TAPE))
     (4103 551 (:REWRITE ACL2-NUMBERP-X))
     (3813 330
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (3480 12 (:DEFINITION M1::OPERATIONP))
     (3039 16
           (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
     (2516 28 (:DEFINITION ALISTP))
     (2415 755 (:REWRITE DEFAULT-CDR))
     (1974 15 (:DEFINITION TRUE-LISTP))
     (1710 10 (:REWRITE M1::CONSP-ASSOC))
     (1238 269 (:REWRITE RATIONALP-X))
     (1238 269
           (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (976 976 (:REWRITE DEFAULT-CAR))
     (688 688 (:REWRITE REDUCE-INTEGERP-+))
     (688 688 (:REWRITE INTEGERP-MINUS-X))
     (688 688 (:META META-INTEGERP-CORRECT))
     (609 330
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (488 8
          (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 2))
     (345 330 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (335 335
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (330 330
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (330 330
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (330 330
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (330 330 (:REWRITE |(equal c (/ x))|))
     (330 330 (:REWRITE |(equal c (- x))|))
     (330 330 (:REWRITE |(equal (/ x) c)|))
     (330 330 (:REWRITE |(equal (/ x) (/ y))|))
     (330 330 (:REWRITE |(equal (- x) c)|))
     (330 330 (:REWRITE |(equal (- x) (- y))|))
     (324 4
          (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
     (303 303
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (303 303 (:REWRITE M1::MEMBER-SUBSETP))
     (269 269 (:REWRITE REDUCE-RATIONALP-+))
     (269 269 (:REWRITE REDUCE-RATIONALP-*))
     (269 269 (:REWRITE RATIONALP-MINUS-X))
     (269 269 (:META META-RATIONALP-CORRECT))
     (252 252 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (216 72 (:REWRITE M1::NTH-ADD1!))
     (162 2
          (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 1))
     (152 152 (:REWRITE THE-FLOOR-BELOW))
     (152 152 (:REWRITE THE-FLOOR-ABOVE))
     (152 152 (:REWRITE DEFAULT-LESS-THAN-2))
     (151 151
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (151 151
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (151 151 (:REWRITE SIMPLIFY-SUMS-<))
     (151 151
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (151 151 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (151 151
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (151 151
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (151 151
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (151 151
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (151 151
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (151 151 (:REWRITE INTEGERP-<-CONSTANT))
     (151 151 (:REWRITE CONSTANT-<-INTEGERP))
     (151 151
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (151 151
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (151 151
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (151 151
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (151 151 (:REWRITE |(< c (- x))|))
     (151 151
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (151 151
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (151 151
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (151 151
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (151 151 (:REWRITE |(< (/ x) 0)|))
     (151 151 (:REWRITE |(< (/ x) (/ y))|))
     (151 151 (:REWRITE |(< (- x) c)|))
     (151 151 (:REWRITE |(< (- x) (- y))|))
     (151 151 (:REWRITE |(< (* x y) 0)|))
     (135 135 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
     (120 120 (:TYPE-PRESCRIPTION LEN))
     (102 102
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (96 48 (:DEFINITION M1::NTH-ALT-DEF))
     (84 12 (:DEFINITION LEN))
     (64 64
         (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
     (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (24 24 (:DEFINITION M1::STATE-NAMEP))
     (24 12 (:REWRITE DEFAULT-PLUS-2))
     (12 12
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (12 12 (:REWRITE NORMALIZE-ADDENDS))
     (12 12 (:REWRITE DEFAULT-PLUS-1))
     (2 1
        (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP)))
(M1::NATP-MAP-RENAMING-MAP-TOP
     (3246 1 (:DEFINITION M1::RENAMING-MAP1))
     (2708 4 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (2698 3 (:DEFINITION M1::TURING-MACHINEP))
     (2681 3 (:DEFINITION M1::TURING-4-TUPLE))
     (1563 1 (:DEFINITION ASSOC-EQUAL))
     (1546 6 (:DEFINITION M1::SYMP))
     (1064 4
           (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
     (1052 4 (:DEFINITION M1::HALF-TAPE))
     (1035 175 (:REWRITE ACL2-NUMBERP-X))
     (1018 93
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (986 2 (:DEFINITION M1::OPERATIONP))
     (546 2 (:DEFINITION TRUE-LISTP))
     (373 5
          (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (359 5 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (306 9 (:DEFINITION NATP))
     (293 293 (:REWRITE DEFAULT-CAR))
     (292 73 (:REWRITE RATIONALP-X))
     (284 71
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (179 3 (:DEFINITION ALISTP))
     (166 93
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (153 153 (:REWRITE REDUCE-INTEGERP-+))
     (153 153 (:REWRITE INTEGERP-MINUS-X))
     (153 153 (:META META-INTEGERP-CORRECT))
     (124 93 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (112 112 (:REWRITE DEFAULT-CDR))
     (93 93
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (93 93
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (93 93
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (93 93 (:REWRITE |(equal c (/ x))|))
     (93 93 (:REWRITE |(equal c (- x))|))
     (93 93 (:REWRITE |(equal (/ x) c)|))
     (93 93 (:REWRITE |(equal (/ x) (/ y))|))
     (93 93 (:REWRITE |(equal (- x) c)|))
     (93 93 (:REWRITE |(equal (- x) (- y))|))
     (71 71 (:REWRITE REDUCE-RATIONALP-+))
     (71 71 (:REWRITE REDUCE-RATIONALP-*))
     (71 71 (:REWRITE RATIONALP-MINUS-X))
     (71 71 (:META META-RATIONALP-CORRECT))
     (52 52
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (52 52 (:REWRITE M1::MEMBER-SUBSETP))
     (44 15 (:REWRITE M1::NTH-ADD1!))
     (40 40 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (21 21
         (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (20 20 (:TYPE-PRESCRIPTION LEN))
     (20 20 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
     (20 10 (:DEFINITION M1::NTH-ALT-DEF))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 2 (:DEFINITION LEN))
     (12 12
         (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
     (11 4 (:REWRITE DEFAULT-PLUS-2))
     (10 1 (:REWRITE |(+ y x)|))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< c (- x))|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 4 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (7 1 (:DEFINITION STRIP-CARS))
     (4 4 (:DEFINITION M1::STATE-NAMEP))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(M1::ASSOC-ST-RENAMING-MAP
     (14485 67 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (14469 5 (:DEFINITION M1::TURING-MACHINEP))
     (14442 5 (:DEFINITION M1::TURING-4-TUPLE))
     (14206 21 (:DEFINITION M1::RENAMING-MAP1))
     (8562 9 (:DEFINITION M1::SYMP))
     (7883 107
           (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (7586 106 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (6460 190 (:DEFINITION NATP))
     (5758 6
           (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
     (5740 6 (:DEFINITION M1::HALF-TAPE))
     (5663 21 (:DEFINITION ASSOC-EQUAL))
     (5656 3 (:DEFINITION M1::OPERATIONP))
     (2900 3 (:DEFINITION TRUE-LISTP))
     (2415 435 (:REWRITE ACL2-NUMBERP-X))
     (2144 178
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (1092 1092 (:REWRITE DEFAULT-CAR))
     (772 193 (:REWRITE RATIONALP-X))
     (604 151
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (551 551 (:REWRITE DEFAULT-CDR))
     (534 534 (:REWRITE REDUCE-INTEGERP-+))
     (534 534 (:REWRITE INTEGERP-MINUS-X))
     (534 534 (:META META-INTEGERP-CORRECT))
     (442 442
          (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (332 178
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (269 178 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (222 81 (:REWRITE M1::NTH-ADD1!))
     (210 21 (:REWRITE |(+ y x)|))
     (190 190 (:REWRITE THE-FLOOR-BELOW))
     (190 190 (:REWRITE THE-FLOOR-ABOVE))
     (190 190
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (190 190
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (190 190 (:REWRITE SIMPLIFY-SUMS-<))
     (190 190
          (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (190 190 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (190 190
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (190 190
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (190 190
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (190 190
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (190 190
          (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (190 190 (:REWRITE INTEGERP-<-CONSTANT))
     (190 190 (:REWRITE DEFAULT-LESS-THAN-2))
     (190 190 (:REWRITE DEFAULT-LESS-THAN-1))
     (190 190 (:REWRITE CONSTANT-<-INTEGERP))
     (190 190
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (190 190
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (190 190
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (190 190
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (190 190 (:REWRITE |(< c (- x))|))
     (190 190
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (190 190
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (190 190
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (190 190
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (190 190 (:REWRITE |(< (/ x) 0)|))
     (190 190 (:REWRITE |(< (/ x) (/ y))|))
     (190 190 (:REWRITE |(< (- x) c)|))
     (190 190 (:REWRITE |(< (- x) (- y))|))
     (190 190 (:REWRITE |(< (* x y) 0)|))
     (178 178
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (178 178
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (178 178
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (178 178 (:REWRITE |(equal c (/ x))|))
     (178 178 (:REWRITE |(equal c (- x))|))
     (178 178 (:REWRITE |(equal (/ x) c)|))
     (178 178 (:REWRITE |(equal (/ x) (/ y))|))
     (178 178 (:REWRITE |(equal (- x) c)|))
     (178 178 (:REWRITE |(equal (- x) (- y))|))
     (153 45 (:REWRITE DEFAULT-PLUS-2))
     (151 151 (:REWRITE REDUCE-RATIONALP-+))
     (151 151 (:REWRITE REDUCE-RATIONALP-*))
     (151 151 (:REWRITE RATIONALP-MINUS-X))
     (151 151 (:META META-RATIONALP-CORRECT))
     (150 45 (:REWRITE DEFAULT-PLUS-1))
     (138 138
          (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (138 138 (:REWRITE M1::MEMBER-SUBSETP))
     (118 118
          (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
     (108 54 (:DEFINITION M1::NTH-ALT-DEF))
     (60 60 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (30 30 (:TYPE-PRESCRIPTION LEN))
     (30 30 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
     (24 24
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (24 24
         (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (24 24 (:REWRITE NORMALIZE-ADDENDS))
     (21 3 (:DEFINITION LEN))
     (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (6 6 (:DEFINITION M1::STATE-NAMEP)))
(M1::TURING1-MACHINEP-TM-TO-TM1
 (133192 194 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
 (129944 1748
         (:DEFINITION M1::NAT-TO-NAT-ALISTP))
 (115100 1500
         (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
 (109042 17580 (:REWRITE DEFAULT-CDR))
 (94338 778 (:REWRITE M1::CONSP-ASSOC))
 (82242 426
        (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
 (80992 434 (:DEFINITION M1::HALF-TAPE))
 (62050 750 (:DEFINITION ALISTP))
 (57318 5988
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (55259 8063 (:REWRITE ACL2-NUMBERP-X))
 (27734 194
        (:REWRITE M1::ASSOC-IS-MEMBER-STRIP-CARS))
 (27435 336 (:DEFINITION M1::LOG2))
 (22144 22064 (:REWRITE DEFAULT-CAR))
 (15732 3933 (:REWRITE RATIONALP-X))
 (15732 3933
        (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (11806 11806 (:REWRITE REDUCE-INTEGERP-+))
 (11806 11806 (:REWRITE INTEGERP-MINUS-X))
 (11806 11806 (:META META-INTEGERP-CORRECT))
 (10206 126
        (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
 (10122 5988
        (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9952 4625 (:REWRITE DEFAULT-LESS-THAN-2))
 (9882 122
       (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 1))
 (8740 8740
       (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
 (8400 336 (:REWRITE |(floor x 2)| . 1))
 (7974 219 (:REWRITE ZP-OPEN))
 (7317 4462
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7149 4462
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7098 4462 (:REWRITE SIMPLIFY-SUMS-<))
 (6185 5988 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5988 5988
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (5988 5988
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (5988 5988
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5988 5988 (:REWRITE |(equal c (/ x))|))
 (5988 5988 (:REWRITE |(equal c (- x))|))
 (5988 5988 (:REWRITE |(equal (/ x) c)|))
 (5988 5988 (:REWRITE |(equal (/ x) (/ y))|))
 (5988 5988 (:REWRITE |(equal (- x) c)|))
 (5988 5988 (:REWRITE |(equal (- x) (- y))|))
 (5974
  5974
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (5974
      5974
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (5974
     5974
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (5974 5974
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (5974 5974
       (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (5137 4625 (:REWRITE DEFAULT-LESS-THAN-1))
 (4625 4625 (:REWRITE THE-FLOOR-BELOW))
 (4625 4625 (:REWRITE THE-FLOOR-ABOVE))
 (4543 4463
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4519 4519
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4519 4519
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4472 4472
       (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (4472 4472 (:REWRITE M1::MEMBER-SUBSETP))
 (4463 4463 (:REWRITE INTEGERP-<-CONSTANT))
 (4463 4463 (:REWRITE CONSTANT-<-INTEGERP))
 (4463 4463
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4463 4463
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4463 4463
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4463 4463
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4463 4463 (:REWRITE |(< c (- x))|))
 (4463 4463
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4463 4463
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4463 4463
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4463 4463
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4463 4463 (:REWRITE |(< (/ x) (/ y))|))
 (4463 4463 (:REWRITE |(< (- x) c)|))
 (4463 4463 (:REWRITE |(< (- x) (- y))|))
 (3933 3933 (:REWRITE REDUCE-RATIONALP-+))
 (3933 3933 (:REWRITE REDUCE-RATIONALP-*))
 (3933 3933 (:REWRITE RATIONALP-MINUS-X))
 (3933 3933 (:META META-RATIONALP-CORRECT))
 (3912 1715 (:REWRITE DEFAULT-PLUS-2))
 (3696 336 (:REWRITE DEFAULT-FLOOR-RATIO))
 (3584 3584 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3572 3572 (:REWRITE |(< (/ x) 0)|))
 (3572 3572 (:REWRITE |(< (* x y) 0)|))
 (3571 3571
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3571 3571
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (2034 2034 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
 (1731 1715 (:REWRITE DEFAULT-PLUS-1))
 (1680 1680 (:REWRITE DEFAULT-TIMES-2))
 (1680 1680 (:REWRITE DEFAULT-TIMES-1))
 (1492 1492
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1449 1449
       (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1449 1449 (:REWRITE NORMALIZE-ADDENDS))
 (1344 1344
       (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1344 336 (:REWRITE |(* y x)|))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1008 1008
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (912 24 (:DEFINITION M1::NATP-MAP))
 (655 473 (:REWRITE DEFAULT-EXPT-2))
 (624 228 (:REWRITE ODD-EXPT-THM))
 (473 473 (:REWRITE DEFAULT-EXPT-1))
 (473 473 (:REWRITE |(expt 1/c n)|))
 (473 473 (:REWRITE |(expt (- x) n)|))
 (336 336 (:REWRITE DEFAULT-FLOOR-2))
 (336 336 (:REWRITE DEFAULT-FLOOR-1))
 (336 336 (:REWRITE |(floor x 2)| . 2))
 (274 274 (:REWRITE |(< x (+ c/d y))|))
 (229 229
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (229 229
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (229 229 (:REWRITE |(< 0 (/ x))|))
 (229 229 (:REWRITE |(< 0 (* x y))|))
 (218 218 (:REWRITE |(< y (+ (- c) x))|))
 (121 48 (:LINEAR EXPT-<=-1-TWO))
 (117 80 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (96 96
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (85 48 (:LINEAR EXPT-<-1-TWO))
 (64 64
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (48 48 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (48 48 (:LINEAR EXPT-LINEAR-UPPER-<))
 (48 48 (:LINEAR EXPT-LINEAR-LOWER-<))
 (48 48 (:LINEAR EXPT->=-1-TWO))
 (48 48 (:LINEAR EXPT->-1-TWO))
 (48 48 (:LINEAR EXPT-<=-1-ONE))
 (48 48 (:LINEAR EXPT-<-1-ONE))
 (4 4 (:REWRITE |(equal (+ (- c) x) y)|)))
(M1::TOTAL-MAP-RENAMING-MAP-TOP
     (3246 1 (:DEFINITION M1::RENAMING-MAP1))
     (2708 4 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
     (2698 3 (:DEFINITION M1::TURING-MACHINEP))
     (2681 3 (:DEFINITION M1::TURING-4-TUPLE))
     (1563 1 (:DEFINITION ASSOC-EQUAL))
     (1546 6 (:DEFINITION M1::SYMP))
     (1064 4
           (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
     (1052 4 (:DEFINITION M1::HALF-TAPE))
     (1035 175 (:REWRITE ACL2-NUMBERP-X))
     (1018 93
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (986 2 (:DEFINITION M1::OPERATIONP))
     (546 2 (:DEFINITION TRUE-LISTP))
     (373 5
          (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
     (359 5 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
     (306 9 (:DEFINITION NATP))
     (292 292 (:REWRITE DEFAULT-CAR))
     (292 73 (:REWRITE RATIONALP-X))
     (284 71
          (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
     (179 3 (:DEFINITION ALISTP))
     (166 93
          (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (153 153 (:REWRITE REDUCE-INTEGERP-+))
     (153 153 (:REWRITE INTEGERP-MINUS-X))
     (153 153 (:META META-INTEGERP-CORRECT))
     (124 93 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (110 110 (:REWRITE DEFAULT-CDR))
     (93 93
         (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (93 93
         (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (93 93
         (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (93 93 (:REWRITE |(equal c (/ x))|))
     (93 93 (:REWRITE |(equal c (- x))|))
     (93 93 (:REWRITE |(equal (/ x) c)|))
     (93 93 (:REWRITE |(equal (/ x) (/ y))|))
     (93 93 (:REWRITE |(equal (- x) c)|))
     (93 93 (:REWRITE |(equal (- x) (- y))|))
     (71 71 (:REWRITE REDUCE-RATIONALP-+))
     (71 71 (:REWRITE REDUCE-RATIONALP-*))
     (71 71 (:REWRITE RATIONALP-MINUS-X))
     (71 71 (:META META-RATIONALP-CORRECT))
     (52 52
         (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
     (52 52 (:REWRITE M1::MEMBER-SUBSETP))
     (44 15 (:REWRITE M1::NTH-ADD1!))
     (40 40 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (21 21
         (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
     (20 20 (:TYPE-PRESCRIPTION LEN))
     (20 20 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
     (20 10 (:DEFINITION M1::NTH-ALT-DEF))
     (16 16
         (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (14 2 (:DEFINITION LEN))
     (12 12
         (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
     (11 4 (:REWRITE DEFAULT-PLUS-2))
     (10 1 (:REWRITE |(+ y x)|))
     (9 9 (:REWRITE THE-FLOOR-BELOW))
     (9 9 (:REWRITE THE-FLOOR-ABOVE))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (9 9
        (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (9 9 (:REWRITE SIMPLIFY-SUMS-<))
     (9 9
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (9 9 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (9 9 (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (9 9
        (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (9 9
        (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (9 9 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (9 9 (:REWRITE INTEGERP-<-CONSTANT))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-2))
     (9 9 (:REWRITE DEFAULT-LESS-THAN-1))
     (9 9 (:REWRITE CONSTANT-<-INTEGERP))
     (9 9 (:REWRITE CAR-CONS))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< c (- x))|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (9 9
        (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (9 9 (:REWRITE |(< (/ x) 0)|))
     (9 9 (:REWRITE |(< (/ x) (/ y))|))
     (9 9 (:REWRITE |(< (- x) c)|))
     (9 9 (:REWRITE |(< (- x) (- y))|))
     (9 9 (:REWRITE |(< (* x y) 0)|))
     (9 4 (:REWRITE DEFAULT-PLUS-1))
     (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (7 1 (:DEFINITION STRIP-CARS))
     (5 5 (:REWRITE CDR-CONS))
     (4 4 (:DEFINITION M1::STATE-NAMEP))
     (3 3
        (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
     (3 3 (:REWRITE NORMALIZE-ADDENDS)))
(M1::CDR-ASSOC-RENAMING-MAP-UPPERBOUND
 (6487 2 (:DEFINITION M1::RENAMING-MAP1))
 (5423 15 (:REWRITE M1::INSTR-IMPLIES-ASSOC))
 (5396 6 (:DEFINITION M1::TURING-MACHINEP))
 (5362 6 (:DEFINITION M1::TURING-4-TUPLE))
 (3092 12 (:DEFINITION M1::SYMP))
 (2368 408 (:REWRITE ACL2-NUMBERP-X))
 (2324 214
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2128 8
       (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
 (2104 8 (:DEFINITION M1::HALF-TAPE))
 (1972 4 (:DEFINITION M1::OPERATIONP))
 (1562 1 (:DEFINITION M1::TM-TO-TM1))
 (1456 21 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
 (1431 23
       (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
 (1296 38 (:DEFINITION NATP))
 (1092 4 (:DEFINITION TRUE-LISTP))
 (812 311 (:REWRITE DEFAULT-CDR))
 (717 717 (:REWRITE DEFAULT-CAR))
 (664 166 (:REWRITE RATIONALP-X))
 (648 162
      (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (516 6 (:REWRITE M1::CONSP-ASSOC))
 (407 1 (:DEFINITION M1::MAX-WIDTH1))
 (380 214
      (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (370 370 (:REWRITE REDUCE-INTEGERP-+))
 (370 370 (:REWRITE INTEGERP-MINUS-X))
 (370 370 (:META META-INTEGERP-CORRECT))
 (294 214 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (214 214
      (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (214 214
      (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (214 214
      (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (214 214 (:REWRITE |(equal c (/ x))|))
 (214 214 (:REWRITE |(equal c (- x))|))
 (214 214 (:REWRITE |(equal (/ x) c)|))
 (214 214 (:REWRITE |(equal (/ x) (/ y))|))
 (214 214 (:REWRITE |(equal (- x) c)|))
 (214 214 (:REWRITE |(equal (- x) (- y))|))
 (184 2 (:DEFINITION M1::LOG2))
 (182 2 (:DEFINITION MAX))
 (162 162 (:REWRITE REDUCE-RATIONALP-+))
 (162 162 (:REWRITE REDUCE-RATIONALP-*))
 (162 162 (:REWRITE RATIONALP-MINUS-X))
 (162 162 (:META META-RATIONALP-CORRECT))
 (123 123
      (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (123 123 (:REWRITE M1::MEMBER-SUBSETP))
 (114 39 (:REWRITE M1::NTH-ADD1!))
 (92 92 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (85 1
     (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
 (81 81
     (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
 (75 1 (:REWRITE |(< x (if a b c))|))
 (74 50 (:REWRITE DEFAULT-LESS-THAN-2))
 (70 2 (:REWRITE ZP-OPEN))
 (69 49 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (61 21
     (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
 (59 49
     (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (57 57 (:TYPE-PRESCRIPTION M1::LOG2))
 (54 50 (:REWRITE DEFAULT-LESS-THAN-1))
 (54 49 (:REWRITE SIMPLIFY-SUMS-<))
 (52 26 (:DEFINITION M1::NTH-ALT-DEF))
 (50 50 (:REWRITE THE-FLOOR-BELOW))
 (50 50 (:REWRITE THE-FLOOR-ABOVE))
 (50 2 (:REWRITE |(floor x 2)| . 1))
 (49 49
     (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (49 49
     (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (49 49
     (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (49 49 (:REWRITE INTEGERP-<-CONSTANT))
 (49 49 (:REWRITE CONSTANT-<-INTEGERP))
 (49 49
     (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (49 49
     (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (49 49
     (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (49 49
     (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (49 49 (:REWRITE |(< c (- x))|))
 (49 49
     (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (49 49
     (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (49 49
     (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (49 49
     (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (49 49 (:REWRITE |(< (/ x) (/ y))|))
 (49 49 (:REWRITE |(< (- x) c)|))
 (49 49 (:REWRITE |(< (- x) (- y))|))
 (48 1 (:LINEAR M1::NATP-CDR-ASSOC-MAP))
 (46 46 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (45 1 (:DEFINITION M1::NATP-MAP))
 (40 40 (:TYPE-PRESCRIPTION LEN))
 (40 40 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
 (39 15 (:REWRITE DEFAULT-PLUS-2))
 (39 1 (:REWRITE ODD-EXPT-THM))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (38 38
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (38 38 (:REWRITE |(< (/ x) 0)|))
 (38 38 (:REWRITE |(< (* x y) 0)|))
 (38 1
     (:REWRITE M1::LOG2-IMPLIES-EXPT-UPPERBOUND))
 (38 1 (:LINEAR EXPT-<=-1-TWO))
 (37 1 (:LINEAR EXPT->-1-ONE))
 (36
  36
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (36 36
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (33 1 (:LINEAR EXPT-X->=-X))
 (33 1 (:LINEAR EXPT-X->-X))
 (32 32
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (28 4 (:DEFINITION LEN))
 (27 27
     (:TYPE-PRESCRIPTION M1::RENAMING-MAP2))
 (26 26 (:TYPE-PRESCRIPTION M1::NATP-MAP))
 (25 15 (:REWRITE DEFAULT-PLUS-1))
 (24 24
     (:TYPE-PRESCRIPTION M1::TURING-MACHINEP))
 (22 2 (:REWRITE DEFAULT-FLOOR-RATIO))
 (20 2 (:REWRITE |(+ y x)|))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 1 (:REWRITE |(+ x (if a b c))|))
 (12 12
     (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (10 10 (:REWRITE DEFAULT-TIMES-2))
 (10 10 (:REWRITE DEFAULT-TIMES-1))
 (8 8
    (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:DEFINITION M1::STATE-NAMEP))
 (8 2 (:REWRITE |(* y x)|))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6
    (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (4 2 (:REWRITE DEFAULT-EXPT-2))
 (3 3 (:TYPE-PRESCRIPTION M1::TM-TO-TM1))
 (2 2 (:REWRITE DEFAULT-FLOOR-2))
 (2 2 (:REWRITE DEFAULT-FLOOR-1))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(floor x 2)| . 2))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2 2
    (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2 2
    (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:DEFINITION NOT))
 (2 1 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (2 1 (:LINEAR EXPT-<-1-TWO))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1
    (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
             . 1))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-UPPER-<))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (1 1 (:LINEAR EXPT-LINEAR-LOWER-<))
 (1 1 (:LINEAR EXPT->=-1-TWO))
 (1 1 (:LINEAR EXPT->-1-TWO))
 (1 1 (:LINEAR EXPT-<=-1-ONE))
 (1 1 (:LINEAR EXPT-<-1-ONE)))
(M1::TMI3-IS-TMI
 (72302 7 (:DEFINITION M1::TMI3))
 (72007 21 (:REWRITE M1::NINSTR-NCODE))
 (50510 67 (:DEFINITION M1::TM-TO-TM1))
 (45225 56 (:DEFINITION M1::MAX-WIDTH1))
 (43287 4310 (:REWRITE DEFAULT-CDR))
 (40357 477 (:REWRITE M1::CONSP-ASSOC))
 (40306 607 (:DEFINITION M1::NAT-TO-NAT-ALISTP))
 (37672 552
        (:REWRITE M1::NAT-TO-NAT-ALISTP-TO-ALISTP))
 (32984 112 (:DEFINITION M1::LOG2))
 (20492 276 (:DEFINITION ALISTP))
 (20375 2837 (:REWRITE ACL2-NUMBERP-X))
 (16711 2295 (:REWRITE DEFAULT-LESS-THAN-2))
 (15372 84 (:DEFINITION M1::DESCENDING-MAP))
 (14139 477 (:DEFINITION ASSOC-EQUAL))
 (13859 2211 (:REWRITE DEFAULT-LESS-THAN-1))
 (12782 1134
        (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10190 130 (:DEFINITION M1::INSTR))
 (9961 112 (:DEFINITION MAX))
 (6657 42 (:REWRITE M1::MAPPED-INSTR))
 (6657 42
       (:REWRITE M1::INSTR-IMPLIES-MAPPED-INSTR-VICE-VERSA))
 (6434 1445 (:REWRITE RATIONALP-X))
 (6203 4271 (:REWRITE INTEGERP-MINUS-X))
 (5914 5914 (:REWRITE DEFAULT-CAR))
 (5796 84 (:REWRITE FLOOR-ZERO . 3))
 (5300 1319
       (:REWRITE M1::INTEGERP-IMPLIES-RATIONALP))
 (4452 84 (:REWRITE CANCEL-FLOOR-+))
 (4200 56 (:REWRITE |(< x (if a b c))|))
 (4187 4187 (:REWRITE REDUCE-INTEGERP-+))
 (4187 4187 (:META META-INTEGERP-CORRECT))
 (3943 135 (:REWRITE ZP-OPEN))
 (3920 5 (:DEFINITION M1::TURING-MACHINEP))
 (3900 5 (:DEFINITION M1::TURING-4-TUPLE))
 (3692 16 (:REWRITE M1::OP-INSTR))
 (3510 70 (:DEFINITION MEMBER-EQUAL))
 (3192 3192 (:TYPE-PRESCRIPTION M1::LOG2))
 (3035 3035
       (:TYPE-PRESCRIPTION M1::NAT-TO-NAT-ALISTP))
 (2930 1134
       (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2754 34
       (:LINEAR M1::NAT-TO-NAT-ALISTP-PROPERTY))
 (2739 1987
       (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2739 1987
       (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2667 21
       (:REWRITE M1::INSTR-IMPLIES-MAPPED-INSTR))
 (2604 84 (:REWRITE FLOOR-ZERO . 4))
 (2604 84 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2597 1134 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2360 1180
       (:TYPE-PRESCRIPTION M1::NATP-CDR-ASSOC-MAP))
 (2295 2295 (:REWRITE THE-FLOOR-BELOW))
 (2295 2295 (:REWRITE THE-FLOOR-ABOVE))
 (2267 1987 (:REWRITE SIMPLIFY-SUMS-<))
 (2200 66 (:LINEAR M1::PROPERTIES-OF-INSTR))
 (2180 15 (:DEFINITION M1::SYMP))
 (2071 1987
       (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (2071 1987
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1987 1987
       (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1987 1987
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1987 1987 (:REWRITE INTEGERP-<-CONSTANT))
 (1987 1987 (:REWRITE CONSTANT-<-INTEGERP))
 (1987 1987
       (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1987 1987
       (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1987 1987
       (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1987 1987
       (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1987 1987 (:REWRITE |(< c (- x))|))
 (1987 1987
       (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1987 1987
       (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1987 1987
       (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1987 1987
       (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1987 1987 (:REWRITE |(< (/ x) (/ y))|))
 (1987 1987 (:REWRITE |(< (- x) c)|))
 (1987 1987 (:REWRITE |(< (- x) (- y))|))
 (1897 56
       (:REWRITE M1::LOG2-IMPLIES-EXPT-UPPERBOUND))
 (1848 84 (:REWRITE FLOOR-=-X/Y . 3))
 (1848 84 (:REWRITE FLOOR-=-X/Y . 2))
 (1792 448 (:REWRITE |(* y x)|))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1764 1764
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1714 34
       (:REWRITE M1::NAT-TO-NAT-ALISTP-PROPERTY . 1))
 (1624 112 (:REWRITE |(floor x 2)| . 2))
 (1550 10
       (:REWRITE M1::HALF-TAPE-IMPLIES-TRUE-LISTP))
 (1520 10 (:DEFINITION M1::HALF-TAPE))
 (1428 168 (:REWRITE |(* (- x) y)|))
 (1390 5 (:DEFINITION M1::OPERATIONP))
 (1381 1381
       (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (1319 1319 (:REWRITE REDUCE-RATIONALP-+))
 (1319 1319 (:REWRITE REDUCE-RATIONALP-*))
 (1319 1319 (:REWRITE RATIONALP-MINUS-X))
 (1319 1319 (:META META-RATIONALP-CORRECT))
 (1316 1316 (:REWRITE DEFAULT-TIMES-2))
 (1316 1316 (:REWRITE DEFAULT-TIMES-1))
 (1292 34 (:LINEAR EXPT-<=-1-TWO))
 (1260 1260
       (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (1260 1260
       (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1260 1260
       (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1260 1260
       (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1258 34 (:LINEAR EXPT->-1-ONE))
 (1232 112 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1151 1151
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1151 1151
       (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1151 1151 (:REWRITE |(< (/ x) 0)|))
 (1151 1151 (:REWRITE |(< (* x y) 0)|))
 (1134 1134
       (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1134 1134
       (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1134 1134
       (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1134 1134 (:REWRITE |(equal c (/ x))|))
 (1134 1134 (:REWRITE |(equal c (- x))|))
 (1134 1134 (:REWRITE |(equal (/ x) c)|))
 (1134 1134 (:REWRITE |(equal (/ x) (/ y))|))
 (1134 1134 (:REWRITE |(equal (- x) c)|))
 (1134 1134 (:REWRITE |(equal (- x) (- y))|))
 (1122 34 (:LINEAR EXPT-X->=-X))
 (1122 34 (:LINEAR EXPT-X->-X))
 (1093 1093
       (:TYPE-PRESCRIPTION M1::NATP-CURRENT-SYM))
 (901 336 (:REWRITE DEFAULT-PLUS-2))
 (896 56 (:REWRITE |(+ x (if a b c))|))
 (840 168 (:REWRITE DEFAULT-MINUS))
 (795 5 (:DEFINITION TRUE-LISTP))
 (784 784
      (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (784 112 (:REWRITE |(floor x 2)| . 1))
 (756 168 (:REWRITE |(- (* c x))|))
 (544 212
      (:TYPE-PRESCRIPTION M1::PROPERTIES-OF-INSTR . 1))
 (420 420
      (:TYPE-PRESCRIPTION M1::DESCENDING-MAP))
 (420 84 (:REWRITE FLOOR-ZERO . 5))
 (420 84 (:REWRITE FLOOR-ZERO . 2))
 (420 84 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (420 84 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (420 84 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (420 84
      (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (420 84 (:REWRITE FLOOR-CANCEL-*-CONST))
 (420 84
      (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (336 336 (:REWRITE DEFAULT-PLUS-1))
 (280 280
      (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (280 280 (:REWRITE NORMALIZE-ADDENDS))
 (264 264
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (264 264
      (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (264 264 (:REWRITE |(< 0 (/ x))|))
 (264 264 (:REWRITE |(< 0 (* x y))|))
 (168 168 (:TYPE-PRESCRIPTION ABS))
 (136
  136
  (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (136 136
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (136
     136
     (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (136 136
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (136 136
      (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (136 68 (:REWRITE DEFAULT-EXPT-2))
 (126 63 (:LINEAR M1::NATP-CURRENT-SYM))
 (120 120
      (:REWRITE M1::SUBSETP-IMPLIES-MEMBER))
 (120 120 (:REWRITE M1::MEMBER-SUBSETP))
 (112 112 (:REWRITE DEFAULT-FLOOR-2))
 (112 112 (:REWRITE DEFAULT-FLOOR-1))
 (112 112 (:REWRITE |(< y (+ (- c) x))|))
 (112 112 (:REWRITE |(< x (+ c/d y))|))
 (84 84
     (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (84 84 (:REWRITE |(floor x (- y))| . 2))
 (84 84 (:REWRITE |(floor x (- y))| . 1))
 (84 84
     (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (84 84
     (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (84 84 (:REWRITE |(floor (- x) y)| . 2))
 (84 84 (:REWRITE |(floor (- x) y)| . 1))
 (84 84
     (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (84 84
     (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (84 84
     (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (84 28
     (:TYPE-PRESCRIPTION M1::NATP-MAKE-CELL))
 (70 14 (:DEFINITION M1::NCODE))
 (68 68 (:REWRITE DEFAULT-EXPT-1))
 (68 68 (:REWRITE |(expt 1/c n)|))
 (68 68 (:REWRITE |(expt (- x) n)|))
 (68 68
     (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (68 68
     (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (68 68
     (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (68 68
     (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (68 34 (:LINEAR EXPT-<-1-TWO))
 (52 52
     (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (50 50 (:TYPE-PRESCRIPTION M1::HALF-TAPE))
 (40 40
     (:TYPE-PRESCRIPTION M1::TURING1-4-TUPLE))
 (40 40 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (35 5 (:DEFINITION LEN))
 (34 34
     (:LINEAR M1::LOG2-IMPLIES-EXPT-UPPERBOUND-COROLLARY
              . 1))
 (34 34 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (34 34 (:LINEAR EXPT-LINEAR-UPPER-<))
 (34 34 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (34 34 (:LINEAR EXPT-LINEAR-LOWER-<))
 (34 34 (:LINEAR EXPT->=-1-TWO))
 (34 34 (:LINEAR EXPT->-1-TWO))
 (34 34 (:LINEAR EXPT-<=-1-ONE))
 (34 34 (:LINEAR EXPT-<-1-ONE))
 (30 30 (:TYPE-PRESCRIPTION LEN))
 (24 12
     (:TYPE-PRESCRIPTION M1::CELLP-MAKE-CELL))
 (21 21 (:TYPE-PRESCRIPTION M1::NCODE))
 (21 21
     (:REWRITE M1::CURRENT-SYMN-CONVERT-TAPE-TO-TAPEN-POS))
 (14 7
     (:REWRITE M1::NEW-TAPE2-CONVERT-TAPE-TO-TAPEN-TRANSFORMED))
 (12 12 (:TYPE-PRESCRIPTION M1::MAKE-CELL))
 (10 10 (:DEFINITION M1::STATE-NAMEP))
 (8 8 (:REWRITE |(equal x (if a b c))|))
 (8 8 (:REWRITE |(equal (if a b c) x)|))
 (7 7 (:TYPE-PRESCRIPTION M1::NOP))
 (2 2 (:TYPE-PRESCRIPTION M1::TMI2)))
