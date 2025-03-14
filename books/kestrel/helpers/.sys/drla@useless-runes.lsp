(HELP::MAP-CONS)
(HELP::MAP-LIST)
(HELP::CROSS
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(HELP::CROSS-N)
(HELP::FILTER-OUT)
(HELP::MAKE-TEMPLATES-AUX)
(HELP::MAKE-TEMPLATES)
(HELP::TEMPLATE-SLOTS)
(HELP::VARS-FROM-BINDINGS)
(HELP::ALL-TRUE)
(HELP::ALL-FALSE)
(HELP::SEPARATES)
(HELP::GET-ARG-LIST
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION ACL2S::MOD-NONNEGATIVE-INTEGER-ARGS))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2 2 (:TYPE-PRESCRIPTION ACL2S::INTEGERP-MOD))
 )
(HELP::FILL-TEMPLATE)
(HELP::REDUNDANT-BOOLEAN-EXPR)
(HELP::SUBST-PAIRWISE
 (6 6 (:TYPE-PRESCRIPTION SUBST))
 )
(HELP::APPLY-LAMBDAS
 (2415 46 (:DEFINITION INTEGER-ABS))
 (861 317 (:REWRITE DEFAULT-PLUS-1))
 (810 317 (:REWRITE DEFAULT-PLUS-2))
 (805 23 (:REWRITE |(+ (if a b c) x)|))
 (713 23 (:REWRITE NUMERATOR-NEGATIVE))
 (253 23 (:DEFINITION LENGTH))
 (209 209 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (209 209 (:REWRITE NORMALIZE-ADDENDS))
 (207 207 (:TYPE-PRESCRIPTION NUMERATOR-ZERO))
 (207 207 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
 (207 207 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
 (207 207 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
 (207 207 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
 (204 79 (:REWRITE DEFAULT-LESS-THAN-1))
 (184 23 (:DEFINITION LEN))
 (161 46 (:REWRITE DEFAULT-MINUS))
 (104 26 (:REWRITE RATIONALP-X))
 (89 86 (:REWRITE DEFAULT-CDR))
 (89 79 (:REWRITE DEFAULT-LESS-THAN-2))
 (79 79 (:REWRITE THE-FLOOR-BELOW))
 (79 79 (:REWRITE THE-FLOOR-ABOVE))
 (79 79 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (79 79 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (79 79 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (79 79 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (79 79 (:REWRITE INTEGERP-<-CONSTANT))
 (79 79 (:REWRITE CONSTANT-<-INTEGERP))
 (79 79 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (79 79 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (79 79 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (79 79 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (79 79 (:REWRITE |(< c (- x))|))
 (79 79 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (79 79 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (79 79 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (79 79 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (79 79 (:REWRITE |(< (/ x) (/ y))|))
 (79 79 (:REWRITE |(< (- x) c)|))
 (79 79 (:REWRITE |(< (- x) (- y))|))
 (76 56 (:REWRITE SIMPLIFY-SUMS-<))
 (76 56 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (76 56 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (75 72 (:REWRITE DEFAULT-CAR))
 (72 72 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (69 69 (:REWRITE |(< (/ x) 0)|))
 (69 69 (:REWRITE |(< (* x y) 0)|))
 (63 63 (:REWRITE FIELD-NOT-EMPTY-IMPLIES-RECORD-NOT-EMPTY1))
 (60 60 (:REWRITE FOLD-CONSTS-IN-+))
 (49 49 (:REWRITE REDUCE-INTEGERP-+))
 (49 49 (:REWRITE INTEGERP-MINUS-X))
 (49 49 (:META META-INTEGERP-CORRECT))
 (46 46 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (46 46 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (30 6 (:REWRITE ACL2-NUMBERP-X))
 (30 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (26 26 (:REWRITE REDUCE-RATIONALP-+))
 (26 26 (:REWRITE REDUCE-RATIONALP-*))
 (26 26 (:REWRITE RATIONALP-MINUS-X))
 (26 26 (:META META-RATIONALP-CORRECT))
 (23 23 (:TYPE-PRESCRIPTION LEN))
 (23 23 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (23 23 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (23 23 (:REWRITE DEFAULT-REALPART))
 (23 23 (:REWRITE DEFAULT-RATIONAL-NUMERATOR))
 (23 23 (:REWRITE DEFAULT-RATIONAL-DENOMINATOR))
 (23 23 (:REWRITE DEFAULT-IMAGPART))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (3 3 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (3 3 (:REWRITE |(equal c (/ x))|))
 (3 3 (:REWRITE |(equal c (- x))|))
 (3 3 (:REWRITE |(equal (/ x) c)|))
 (3 3 (:REWRITE |(equal (/ x) (/ y))|))
 (3 3 (:REWRITE |(equal (- x) c)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 )
(HELP::TERM-SIZE)
(HELP::SIMPLER-TERM)
(HELP::MORE-GENERAL)
(HELP::PREVIOUS-ALREADY-MORE-GENERAL)
(HELP::FILTER-LESS-GENERAL-TERMS)
(HELP::GET-TERMS-SEPARATING-TEMPLATE-AUX)
(HELP::GET-TERMS-SEPARATING-TEMPLATE)
(HELP::GET-TERMS-SEPARATING-LOGICAL-TEMPLATE-AUX)
(HELP::GET-TERMS-SEPARATING-LOGICAL-TEMPLATE)
(HELP::GET-TERMS-SEPARATING-ALL-LOGICAL-TEMPLATES)
(HELP::SET-DIFFERENCE)
(HELP::GET-ALL-FNNAMES-USED-TO-DEFINE)
(HELP::GET-ALL-FNNAMES-IN-FNNAMES)
(HELP::GET-ALL-FNNAMES-IN-TERM)
(HELP::GET-NAMES)
(HELP::COUNT-REAL-ARGS-AUX)
(HELP::COUNT-REAL-ARGS)
(HELP::GET-ARITIES)
(HELP::GET-TERM-TEMPLATES)
(HELP::GET-BOOLEAN-TEMPLATES)
(HELP::COMBINE-TEMPLATES-AUX
 (33 1 (:REWRITE |(< (if a b c) x)|))
 (18 2 (:REWRITE ACL2-NUMBERP-X))
 (14 12 (:REWRITE DEFAULT-PLUS-1))
 (8 2 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (6 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (5 5 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 5 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5 (:REWRITE INTEGERP-<-CONSTANT))
 (5 5 (:REWRITE CONSTANT-<-INTEGERP))
 (5 5 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (- x))|))
 (5 5 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5 5 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) c)|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(< (/ x) 0)|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2 2 (:REWRITE REDUCE-RATIONALP-+))
 (2 2 (:REWRITE REDUCE-RATIONALP-*))
 (2 2 (:REWRITE RATIONALP-MINUS-X))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:META META-RATIONALP-CORRECT))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 )
(HELP::COMBINE-TEMPLATES
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 )
(HELP::ADD-QUOTES-TO-VALUES-AUX)
(HELP::ADD-QUOTES-TO-VALUES)
(HELP::GET-COUNTEREXAMPLES-AND-WITNESSES-FROM-RESULT)
(HELP::INVOKE-CGEN-FN)
(HELP::STRIP-CONSTANTS)
(HELP::REAL-ALL-VARS)
(HELP::FILTER-SUGGESTIONS)
(HELP::DISPLAY-LIST-OF-SUGGESTIONS)
(HELP::DISPLAY-MISSING-HYPOTHESIS-RESULT)
(HELP::DERIVE-MISSING-HYPOTHESIS-FN)
