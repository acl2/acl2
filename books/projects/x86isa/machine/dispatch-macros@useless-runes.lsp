(X86ISA::CHK-EXC-FN
     (10824 132 (:REWRITE MOD-X-Y-=-X . 4))
     (8712 132 (:REWRITE CANCEL-MOD-+))
     (6600 132 (:REWRITE MOD-ZERO . 4))
     (6204 132 (:REWRITE MOD-X-Y-=-X . 3))
     (5940 132 (:REWRITE MOD-X-Y-=-X+Y . 2))
     (5148 132 (:REWRITE MOD-X-Y-=-X-Y . 2))
     (5148 132 (:REWRITE IFIX-POSITIVE-TO-NON-ZP))
     (5130 5130
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
     (5130 5130
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
     (5130 5130
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
     (4770 1074 (:REWRITE INTEGERP-MINUS-X))
     (4620 132 (:REWRITE ZP-OPEN))
     (3564 132 (:REWRITE MOD-ZERO . 3))
     (2904 132 (:REWRITE IFIX-EQUAL-TO-0))
     (2772 264 (:REWRITE |(* (- x) y)|))
     (2772 132 (:REWRITE ZIP-OPEN))
     (2620 988 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
     (2620 988 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
     (2620 988
           (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
     (2620 988
           (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
     (2472 1236
           (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
     (2100 420 (:REWRITE |(* y x)|))
     (1920 1236 (:REWRITE DEFAULT-TIMES-2))
     (1848 132 (:REWRITE DEFAULT-MOD-RATIO))
     (1788 1236 (:REWRITE DEFAULT-TIMES-1))
     (1656 18
           (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-RFLAGSBITS-P))
     (1656 18
           (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
     (1656 18
           (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
     (1584 264 (:REWRITE DEFAULT-MINUS))
     (1452 264 (:REWRITE |(- (* c x))|))
     (1236 1236
           (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
     (1236 1236
           (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
     (1236 1236
           (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
     (1224 696
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
     (1224 696
           (:REWRITE PREFER-POSITIVE-ADDENDS-<))
     (1092 696 (:REWRITE DEFAULT-LESS-THAN-1))
     (1061 798
           (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
     (1056 264 (:REWRITE IFIX-NEGATIVE-TO-NEGP))
     (1043 798
           (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
     (988 988 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
     (988 988
          (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
     (988 988
          (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
     (988 988
          (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
     (988 988 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
     (942 942 (:REWRITE REDUCE-INTEGERP-+))
     (942 942 (:META META-INTEGERP-CORRECT))
     (924 132 (:REWRITE MOD-X-Y-=-X . 2))
     (924 132
          (:REWRITE |(mod (+ x (mod a b)) y)|))
     (924 132
          (:REWRITE |(mod (+ x (- (mod a b))) y)|))
     (828 696 (:REWRITE DEFAULT-LESS-THAN-2))
     (798 798 (:REWRITE SIMPLIFY-SUMS-EQUAL))
     (798 798
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
     (798 798
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
     (798 798
          (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
     (798 798 (:REWRITE |(equal c (/ x))|))
     (798 798 (:REWRITE |(equal c (- x))|))
     (798 798 (:REWRITE |(equal (/ x) c)|))
     (798 798 (:REWRITE |(equal (/ x) (/ y))|))
     (798 798 (:REWRITE |(equal (- x) c)|))
     (798 798 (:REWRITE |(equal (- x) (- y))|))
     (792 132 (:REWRITE MOD-X-Y-=-X-Y . 3))
     (792 132 (:REWRITE MOD-X-Y-=-X+Y . 3))
     (696 696 (:REWRITE THE-FLOOR-BELOW))
     (696 696 (:REWRITE THE-FLOOR-ABOVE))
     (696 696 (:REWRITE SIMPLIFY-SUMS-<))
     (696 696
          (:REWRITE REMOVE-STRICT-INEQUALITIES))
     (696 696
          (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
     (696 696
          (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
     (696 696
          (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
     (696 696 (:REWRITE INTEGERP-<-CONSTANT))
     (696 696 (:REWRITE CONSTANT-<-INTEGERP))
     (696 696
          (:REWRITE |(< c (/ x)) positive c --- present in goal|))
     (696 696
          (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
     (696 696
          (:REWRITE |(< c (/ x)) negative c --- present in goal|))
     (696 696
          (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
     (696 696 (:REWRITE |(< c (- x))|))
     (696 696
          (:REWRITE |(< (/ x) c) positive c --- present in goal|))
     (696 696
          (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
     (696 696
          (:REWRITE |(< (/ x) c) negative c --- present in goal|))
     (696 696
          (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
     (696 696 (:REWRITE |(< (/ x) (/ y))|))
     (696 696 (:REWRITE |(< (- x) c)|))
     (696 696 (:REWRITE |(< (- x) (- y))|))
     (684 684
          (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
     (672 132
          (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
     (672 132
          (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
     (648 24 (:LINEAR MOD-BOUNDS-3))
     (642 132 (:REWRITE MOD-CANCEL-*-CONST))
     (564 564 (:REWRITE REMOVE-WEAK-INEQUALITIES))
     (552 6
          (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-22BITS-P))
     (480 120 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
     (480 120 (:REWRITE IFIX-WHEN-INTEGERP))
     (325 325
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
     (288 48 (:LINEAR MOD-BOUNDS-2))
     (282 282
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
     (282 282
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
     (282 282 (:REWRITE |(< (/ x) 0)|))
     (282 282 (:REWRITE |(< (* x y) 0)|))
     (264 264 (:TYPE-PRESCRIPTION NEGP))
     (264 264
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
     (264 264
          (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
     (264 264 (:REWRITE NEGP-WHEN-LESS-THAN-0))
     (264 264 (:REWRITE NEGP-WHEN-INTEGERP))
     (264 264 (:REWRITE |(< 0 (/ x))|))
     (264 264 (:REWRITE |(< 0 (* x y))|))
     (264 132 (:REWRITE DEFAULT-MOD-1))
     (252 132
          (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
     (252 132
          (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
     (132 132 (:REWRITE ZP-WHEN-INTEGERP))
     (132 132 (:REWRITE ZP-WHEN-GT-0))
     (132 132
          (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
     (132 132
          (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
     (132 132 (:REWRITE IFIX-EQUAL-TO-NONZERO))
     (132 132 (:REWRITE DEFAULT-MOD-2))
     (132 132 (:REWRITE |(mod x (- y))| . 3))
     (132 132 (:REWRITE |(mod x (- y))| . 2))
     (132 132 (:REWRITE |(mod x (- y))| . 1))
     (132 132
          (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
     (132 132
          (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
     (132 132 (:REWRITE |(mod (- x) y)| . 3))
     (132 132 (:REWRITE |(mod (- x) y)| . 2))
     (132 132 (:REWRITE |(mod (- x) y)| . 1))
     (70 14
         (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-PREFIXES-P))
     (48 48
         (:REWRITE X86ISA::PREFIXES->REP-OF-WRITE-WITH-MASK))
     (39 39
         (:REWRITE X86ISA::CR0BITS->TS-OF-WRITE-WITH-MASK))
     (36 36
         (:TYPE-PRESCRIPTION X86ISA::RFLAGSBITS-P$INLINE))
     (36 36
         (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
     (36 36
         (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
     (36 18
         (:REWRITE X86ISA::RFLAGSBITS-P-WHEN-UNSIGNED-BYTE-P))
     (36 18
         (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
     (36 18
         (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
     (28 28
         (:TYPE-PRESCRIPTION X86ISA::PREFIXES-P$INLINE))
     (27 27
         (:REWRITE X86ISA::CR4BITS->OSFXSR-OF-WRITE-WITH-MASK))
     (18 18
         (:REWRITE X86ISA::PREFIXES->OPR-OF-WRITE-WITH-MASK))
     (18 18
         (:REWRITE X86ISA::CR0BITS->EM-OF-WRITE-WITH-MASK))
     (12 12
         (:TYPE-PRESCRIPTION X86ISA::22BITS-P))
     (12 6
         (:REWRITE X86ISA::22BITS-P-WHEN-UNSIGNED-BYTE-P))
     (9 3 (:DEFINITION SYMBOL-LISTP))
     (6 6
        (:REWRITE X86ISA::PREFIXES->LCK-OF-WRITE-WITH-MASK))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR)))
