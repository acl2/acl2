; Rule Lists used by the Formal Unit Tester
;
; Copyright (C) 2021-2022 Kestrel Technology, LLC
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/axe/rule-lists" :dir :system)
(include-book "kestrel/x86/rule-lists" :dir :system)

;; these are used both for lifting and proving
(defun extra-rules ()
  (declare (xargs :guard t))
  (append '(acl2::bvchop-of-*
            acl2::integerp-of-expt
            acl2::integerp-of-*                 ; for array index calcs
            ACL2::<-OF-+-AND-+-CANCEL-CONSTANTS ; for array index calcs
            ACL2::MY-INTEGERP-<-NON-INTEGERP    ; for array index calcs
            acl2::bvsx-when-bvlt
            x86isa::canonical-address-p-between-special5
            x86isa::canonical-address-p-between-special5-alt
            x86isa::canonical-address-p-between-special6
            bitops::ash-is-expt-*-x acl2::natp-of-*
            acl2::<-of-constant-and-+-of-constant ; for address calcs
            <-of-15-and-*-of-4
            unsigned-byte-p-2-of-bvchop-when-bvlt-of-4
            acl2::bvlt-of-max-arg2
            <-of-*-when-constant-integers
            separate-when-separate
            acl2::<-of-+-cancel-second-of-more-and-only ; more?
            acl2::<-of-+-cancel-1+-1+ ;; acl2::<-of-+-cancel-first-and-first
            acl2::collect-constants-over-<-2
            acl2::commutativity-of-*-when-constant
            <-of-*-of-constant-and-constant
            rationalp-when-integerp
            acl2::<-of-+-cancel-1+-1 ; todo: same as acl2::<-of-+-cancel.  kill that one
            acl2::+-of-+-of---same
            acl2::<-of-minus-and-constant ; ensure needed
            acl2::fix-when-acl2-numberp
            acl2-numberp-of--
            acl2::acl2-numberp-of-*
            bitops::ash-of-0-c ; at least for now
            ;;RFLAGSBITS->AF-of-myif
            ACL2::BVASHR-of-0-arg2
            ACL2::BVSHR-of-0-arg2
            acl2::eql ; drop soon?
            ACL2::EQUAL-OF-CONSTANT-AND-BVUMINUS
            ACL2::BVOR-OF-MYIF-ARG2 ; introduces bvif (myif can arise from expanding a shift into cases)
            ACL2::BVOR-OF-MYIF-ARG3 ; introduces bvif (myif can arise from expanding a shift into cases)
            ACL2::BVIF-OF-MYIF-ARG3 ; introduces bvif
            ACL2::BVIF-OF-MYIF-ARG4 ; introduces bvif
            ;; help to show that divisions don't overflow or underflow:
            not-sbvlt-of-constant-and-sbvdiv-32-64
            not-sbvlt-of-sbvdiv-and-minus-constant-32-64
            not-bvlt-of-constant-and-bvdiv-64-128
            not-bvlt-of-constant-and-bvdiv-32-64
            ACL2::BVDIV-SAME
            ACL2::SBVDIV-SAME
            ACL2::SBVDIV-OF-1-ARG3
            ACL2::BVSX-OF-BVSX
            ACL2::SLICE-OF-BVSX-HIGH
            bvcat-of-repeatbit-of-getbit-of-bvsx-same
            not-sbvlt-of-bvsx-of-constant-arg2-64-8
            not-sbvlt-of-bvsx-of-constant-arg2-64-16
            not-sbvlt-of-bvsx-of-constant-arg2-64-32
            not-sbvlt-of-bvsx-of-constant-arg2-128-64
            not-sbvlt-of-bvsx-of-constant-arg3-64-8
            not-sbvlt-of-bvsx-of-constant-arg3-64-16
            not-sbvlt-of-bvsx-of-constant-arg3-64-32
            not-sbvlt-of-bvsx-of-constant-arg3-128-64
            acl2::floor-of-1-when-integerp ; simplified something that showed up in an error case?
            unicity-of-1 ; simplified something that showed up in an error case
            bvcat-of-repeatbit-of-getbit-becomes-bvsx
            bvcat-of-repeatit-tighten-64-32 ;gen!
            ACL2::BVLT-OF-BVSX-ARG2
            sbvlt-of-bvsx-32-16-constant
            RFLAGSBITS->AF-OF-IF
            ACL2::SBVLT-FALSE-WHEN-SBVLT-GEN ; did nothing?
            if-of-sbvlt-and-not-sbvlt-helper
            if-of-set-flag-and-set-flag
            XR-OF-!RFLAGS-IRREL ; todo: better normal form?
            64-bit-modep-OF-!RFLAGS
            app-view-OF-!RFLAGS
            x86p-OF-!RFLAGS
            read-OF-!RFLAGS
            boolif-same-arg1-arg2
            logext-of-+-of-bvplus-same-size
            logext-of-+-of-+-of-mult-same-size
            ACL2::MINUS-CANCELLATION-ON-RIGHT ; todo: use an arithmetic-light rule
            ACL2::BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ2 ; needed for STP to see the array op
            BV-ARRAY-READ-of-*-arg3 ; introduces bvmult for the index
            BV-ARRAY-READ-of-+-arg3 ; introduces bvplus for the index
            ACL2::NTH-BECOMES-BV-ARRAY-READ-STRONG2
            ACL2::BVPLUS-OF-*-ARG2 ; introduces bvmult -- todo: alt version?
            not-equal-of-+-and-+-when-separate
            not-equal-of-+-of-+-and-+-when-separate
            not-equal-of-+-of-+-and-+-when-separate-gen
            acl2::<-of-negative-constant-and-bv
            READ-OF-WRITE-BOTH-SIZE-1
            ACL2::BVLT-OF-CONSTANT-WHEN-USB-DAG ; rename
            separate-of-1-and-1
            <-of-+-and-+-arg3-and-arg1
            equal-of-bvshl-and-constant
            bvchop-of-bvshl-same
            acl2::equal-of-myif-arg1-safe
            acl2::equal-of-myif-arg2-safe
            write-of-write-same
            write-of-write-of-write-same
            write-of-write-of-write-of-write-same
            bvminus-of-+-arg2
            bvminus-of-+-arg3
            acl2::bvminus-of-bvplus-and-bvplus-same-2-2
            acl2::right-cancellation-for-+ ; todo: switch to an arithmetic-light rule
            acl2::bvplus-of-unary-minus
            acl2::bvplus-of-unary-minus-arg2
            acl2::if-becomes-bvif-1-axe
            ;; acl2::boolif-of-t-and-nil-when-booleanp
            slice-of-bvand-of-constant
            acl2::myif-becomes-boolif-axe ; since STP translation supports disjuncts that are calls to boolif but not if.
            acl2::equal-of-bvplus-constant-and-constant
            acl2::equal-of-bvplus-constant-and-constant-alt
            acl2::bvchop-of-bvshr-same
            ;bvand-of-lognot-arg2
            ;bvand-of-lognot-arg3
            ;bvxor-of-lognot-arg2
            ;bvxor-of-lognot-arg3
            acl2::bvchop-of-lognot
            acl2::getbit-of-lognot ; todo: handle all cases of logops inside bvops
            bvif-of-if-constants-nil-nonnil
            bvif-of-if-constants-nonnil-nil
            acl2::bvminus-of-0-arg3
            acl2::bvif-same-branches
            acl2::equal-of-1-and-bitand
            ACL2::BOOLIF-OF-NIL-AND-T
            ACL2::BVIF-OF-BOOL-FIX
            acl2::boolif-same-branches
            ACL2::BOOLEANP-OF-MYIF ; or convert myif to boolif when needed
            ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
            ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG2
            ;; these next few did seem needed after lifting (todo: either add the rest like this or drop these):
            booleanp-of-jp-condition
            booleanp-of-jnp-condition
            booleanp-of-jz-condition
            booleanp-of-jnz-condition
            ACL2::GETBIT-0-OF-BOOL-TO-BIT
            ACL2::EQUAL-OF-BOOL-TO-BIT-AND-0 ; alt version needed, or do equals get turned around?
            ACL2::EQUAL-OF-BOOL-TO-BIT-AND-1 ; alt version needed, or do equals get turned around?
            ACL2::EQUAL-OF-1-AND-BITNOT ; todo: add 0 version
            ;;ACL2::BVIF-OF-1-AND-0-BECOMES-BOOL-TO-BIT ; introduced bool-to-bit?  maybe bad.
            ;; todo: just include boolean-rules?:
            acl2::bool-fix-when-booleanp
            acl2::booland-of-constant-arg1
            acl2::booland-of-constant-arg2
            acl2::boolor-of-constant-arg1
            acl2::boolor-of-constant-arg2
            ;; acl2::bvmult-tighten-when-power-of-2p-axe ; todo: uncomment
            ;; acl2::bvplus-of-bvmult-when-power-of-2p-tighten ; todo: uncomment
            bvchop-of-bool-to-bit ;todo: drop
            logext-of-bool-to-bit
            acl2::bool-fix-when-booleanp
            acl2::<-of-if-arg1-safe
            ;; acl2::<-of-if-arg2-safe
            acl2::bvif-of-logext-1
            acl2::bvif-of-logext-2
            equal-of-bvif-safe2
            )
          (acl2::convert-to-bv-rules) ; turns things like logxor into things like bvxor
          (acl2::booleanp-rules)
          (acl2::boolean-rules-safe)
          (acl2::type-rules)))

(defun extra-lifting-rules ()
  (declare (xargs :guard t))
  (append (lifter-rules64-new)
          (extra-rules)
          '(X86ISA::WX32$inline ; more?
            X86ISA::WZ32$inline ; more?
            <-of-fp-to-rat ; do we want this?
            X86ISA::!EVEX-PREFIXES->BYTE0$INLINE-CONSTANT-OPENER
            !RFLAGS-of-if-arg1
            !RFLAGS-of-if-arg2
            ;;xr-of-!rflags-irrel
            X86ISA::IF-X-X-Y
            ;; ACL2::IF-OF-T-AND-NIL-WHEN-BOOLEANP
            ACL2::EQUAL-OF-IF-ARG1-WHEN-QUOTEP
            ACL2::EQUAL-OF-IF-ARG2-WHEN-QUOTEP
            eq
            X86ISA::SSE-CMP-SPECIAL ; scary
            X86ISA::FP-DECODE-CONSTANT-OPENER
            X86ISA::FP-to-rat-CONSTANT-OPENER
            RTL::BIAS-CONSTANT-OPENER
            RTL::expw-CONSTANT-OPENER
            unsigned-byte-p-32-of-!MXCSRBITS->IE
            unsigned-byte-p-32-of-!MXCSRBITS->DE
            ACL2::BVCHOP-OF-IF
            integerp-of-!MXCSRBITS->DE
            integerp-of-!MXCSRBITS->IE
            integerp-of-xr-mxcsr
            ifix-of-if
            MXCSRBITS->IM-of-!MXCSRBITS->IE
            MXCSRBITS->IM-of-!MXCSRBITS->DE
            MXCSRBITS->DM-of-!MXCSRBITS->DE
            MXCSRBITS->DM-of-!MXCSRBITS->IE
            MXCSRBITS->DAZ-of-!MXCSRBITS->DE
            MXCSRBITS->DAZ-of-!MXCSRBITS->IE
            X86ISA::MXCSRBITS->IM-of-if
            X86ISA::MXCSRBITS->DM-of-if
            X86ISA::MXCSRBITS->Daz-of-if
            sse-daz-of-nil
            X86ISA::N32P-XR-MXCSR
            X86ISA::SSE-CMP ; scary
            x86isa::dp-sse-cmp
            app-view-of-if
            program-at-of-if
            x86p-of-if
            ALIGNMENT-CHECKING-ENABLED-P-of-if
            get-flag-of-if
            ctri-of-if
            ;; feature-flag-of-if
            read-of-if
            bvle
            ACL2::INTEGERP-OF-BVPLUS ;todo: more
            ACL2::INTEGERP-OF-BVCHOP

            ;zf-spec$inline     ; needed for unsigned_add_associates -- but does this ruin rules about jle-condition? zf-spec seems to be used in more things that just the conditional branches?

            ;x86isa::sub-zf-spec32-same ; this can mess up the condition rules...
            ;x86isa::if-of-sub-zf-spec32-arg2
            ACL2::BFIX-WHEN-BITP
            ;;stuff related to flags changes:
            x86isa::GPR-SUB-SPEC-1-alt-def
            x86isa::GPR-SUB-SPEC-2-alt-def
            x86isa::GPR-SUB-SPEC-4-alt-def
            x86isa::GPR-SUB-SPEC-8-alt-def

            bvchop-of-sub-zf-spec32
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32

            logand-of-1-arg2
            acl2::integerp-of-if
            acl2::ifix-does-nothing
            of-spec-of-logext-32
            ACL2::LOGXOR-BVCHOP-BVCHOP        ; introduce bvxor
            ACL2::LOGXOR-of-BVCHOP-becomes-bvxor-arg1 ; introduce bvxor
;            bvplus-of-logxor-arg1                     ; introduce bvxor
;            bvxor-of-logxor-arg2                      ; introduce bvxor
            integerp-of-logxor                        ;todo: more
            acl2::unsigned-byte-p-of-if
            acl2::unsigned-byte-p-of-bvplus ;todo: more
            ACL2::BVCHOP-OF-MYIF
            XR-OF-IF ;restrict?
            ACL2::SLICE-OUT-OF-ORDER
            X86ISA::DIV-SPEC$inline ; just a dispatch on the size
            ACL2::BVCAT-OF-0-arg2
            bvmod-tighten-64-32
            bvdiv-tighten-64-32
            not-bvlt-of-max-when-unsiged-byte-p
            ;X86ISA::SF-SPEC32-REWRITE ; trying without...
            jle-condition-rewrite-1-with-bvif ; this one works on bvif
            jle-condition-rewrite-1-with-bvif-and-bvchop
            jle-condition-rewrite-1-with-bvchop
            jnl-condition-of-getbit-31-and-0
            jnl-condition-rewrite-16
            jnl-condition-rewrite-16b
            bvchop-of-logext-becomes-bvsx ; needed for jnl-condition-rewrite-16
            ACL2::BVSX-WHEN-SIZES-MATCH
            ACL2::BVCHOP-OF-BVSX
            ACL2::BVCHOP-OF-BVCHOP
            ACL2::BVPLUS-OF-BVCHOP-ARG2
            bvchop-of-zf-spec
            logext-of-zf-spec
            integerp-of-zf-spec
            sbvle ; expand to sbvlt
            ACL2::SBVLT-OF-BVCHOP-ARG2
            ACL2::BVUMINUS-OF-BVUMINUS
            ACL2::BVPLUS-OF-BVUMINUS-SAME
            ACL2::BVCHOP-NUMERIC-BOUND
            ACL2::BVCHOP-OF-LOGXOR-BECOMES-BVXOR
            ;acl2::bvuminus-of-bvsx-low ; todo: other cases? todo: push back
            SF-SPEC64-of-bvchop-64
            jnl-condition-of-sf-spec32-and-of-spec32-same
            jnl-condition-of-sf-spec64-and-of-spec64-same
            jnl-condition-of-sf-spec64-and-0
            of-spec64-of-logext-64
            ACL2::SBVLT-OF-BVSX-ARG2
            ACL2::BVSX-OF-BVCHOP
            X86ISA::!PREFIXES->REP$INLINE-CONSTANT-OPENER ; for floating point?
            X86ISA::PREFIXES->REP$INLINE-CONSTANT-OPENER ; for floating point?
            X86ISA::CHK-EXC-FN ; for floating point?
            ctri-of-xw-irrel
            ctri-of-write
            ctri-of-set-flag
            X86ISA::FEATURE-FLAGS-opener
            X86ISA::FEATURE-FLAGS-base
            eql
            integerp-of-ctri
            X86ISA::XMMI-SIZE$inline ;trying
            X86ISA::!XMMI-SIZE$inline
            X86ISA::X86-OPERAND-TO-XMM/MEM
            cr0bits->ts-of-bvchop
            cr0bits->em-of-bvchop
            cr4bits->OSFXSR-of-bvchop
            X86ISA::WX128$inline
            X86ISA::WZ128$inline
            X86ISA::RX32$inline
            X86ISA::RX64$inline
            X86ISA::RZ32$inline
            X86ISA::RZ64$inline
            X86ISA::RX128$INLINE
            X86ISA::RZ128$INLINE
            X86ISA::ZMMI
            X86ISA::ZMMI$A
            X86ISA::!ZMMI
            X86ISA::!ZMMI$A
            X86ISA::N128$inline
            integerp-of-PART-INSTALL-WIDTH-LOW$INLINE
            X86ISA::SP-SSE-CMP
            ;;X86ISA::SSE-CMP ;todo: limit?
            X86ISA::MXCSR
            X86ISA::MXCSR$A
            X86ISA::!MXCSR
            X86ISA::!MXCSR$A
            64-BIT-MODEP-of-if
            ;; FEATURE-FLAG-sse-of-xw
            ;; FEATURE-FLAG-sse-of-write
            ;; FEATURE-FLAG-sse-of-set-flag
            ;; FEATURE-FLAG-sse2-of-xw
            ;; FEATURE-FLAG-sse2-of-write
            ;; FEATURE-FLAG-sse2-of-set-flag
            ACL2::EQUAL-OF-IF-CONSTANTS
            ACL2::BVLT-OF-BVPLUS-1-CANCEL-ALT ; optional
            ;X86ISA::IDIV-SPEC-32 ; trying
            ACL2::BVCHOP-WHEN-SIZE-IS-NOT-POSP
            mv-nth-0-of-idiv-spec-32
            mv-nth-1-of-idiv-spec-32
            mv-nth-0-of-idiv-spec-64
            mv-nth-1-of-idiv-spec-64
            acl2::bvcat-of-if-arg2
            acl2::bvcat-of-if-arg4
            ACL2::BVIF-OF-0-ARG1
            ACL2::BVPLUS-WHEN-SIZE-IS-NOT-POSITIVE ; todo: more like this, make a rule-list
            x86isa::X86-CWD/CDQ/CQO-alt-def
            acl2::bvcat-of-slice-of-bvsx-same
            not-sbvlt-64-of-sbvdiv-64-of-bvsx-64-32-and--2147483648
            not-sbvlt-64-of-2147483647-and-sbvdiv-64-of-bvsx-64-32
            IF-OF-IF-OF-CONS-AND-NIL ; why not already included
            ACL2::BVPLUS-COMMUTATIVE-INCREASING-AXE
            ACL2::BVPLUS-COMMUTATIVE-2-INCREASING-AXE
            ;;acl2::equal-same
            ;; bvcat-of-minus-becomes-bvshl ; except STP doesn't support the shift operators
            acl2::<-lemma-for-known-operators
            acl2::bvlt-of-bvchop-arg2
            acl2::bvlt-of-bvchop-arg3
            acl2::sbvlt-of-bvchop-arg2
            acl2::sbvlt-of-bvchop-arg3
            ;; todo: more like this?:
            X86ISA::RFLAGSBITS->CF-of-if
            X86ISA::RFLAGSBITS->PF-of-if
            X86ISA::RFLAGSBITS->OF-of-if
            X86ISA::RFLAGSBITS->SF-of-if
            X86ISA::RFLAGSBITS->ZF-of-if
            acl2::bvand-of-bvchop-1 ;rename
            acl2::bvand-of-bvchop-2 ;rename
            ACL2::BVCHOP-OF-MINUS-BECOMES-BVUMINUS ; todo: or re-characterize the subl instruction
            ACL2::BVPLUS-OF-PLUS-ARG3 ; todo: drop once we characterize long negation?
            ACL2::BVUMINUS-OF-+
            X86ISA::INTEGERP-OF-XR-RGF
            ACL2::NATP-OF-+-OF-- ; trying, or simplify (NATP (BINARY-+ '32 (UNARY-- (BVCHOP '5 x))))
            min ; why is min arising?  or add min-same
            ACL2::<-BECOMES-BVLT-DAG-ALT-GEN-BETTER2
            ACL2::<-BECOMES-BVLT-DAG-GEN-BETTER2
            ;; after adding core-rules-bv:
            acl2::bvplus-of-logext-gen-arg1
            acl2::bvplus-of-logext-gen-arg2
            ACL2::BVPLUS-OF-LOGEXT ; rename
            ACL2::BVPLUS-OF-LOGEXT-arg1 ; rename
            ACL2::BVUMINUS-OF-LOGEXT
            acl2::bvlt-tighten-bind-and-bind-dag
            ACL2::UNSIGNED-BYTE-P-OF-0-ARG1 ; move to a more fundamental rule list
            ;; ACL2::BOOLIF-X-X-Y ; introduces boolor
            boolor-becomes-boolif
            ;bvlt-hack-1-gen
            ACL2::BVCHOP-SUBST-CONSTANT
            ACL2::BVCHOP-SUBST-CONSTANT-alt
            ACL2::BOOL-FIX$INLINE-CONSTANT-OPENER
            boolif-of-bvlt-strengthen-to-equal
            bvlt-reduce-when-not-equal-one-less
            acl2::bvchop-of-logand-becomes-bvand
            read-of-write-1-4
            read-of-write-1-both
            not-equal-of-+-when-separate
            not-equal-of-+-when-separate-alt
            x86isa::canonical-address-p-of-sum-when-unsigned-byte-p-32
            x86isa::!prefixes->seg$inline-constant-opener
            read-of-2 ; splits into 2 reads
            )
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))

(defun proof-rules ()
  (declare (xargs :guard t))
  (append '(myif-of-sub-zf-spec32-arg2
            myif-of-sub-zf-spec32-arg3
            ACL2::INTEGERP-OF-BVPLUS ;todo: more
            ACL2::INTEGERP-OF-BVCHOP
            equal-of-sub-zf-spec32-and-1
            equal-of-1-and-sub-zf-spec32
            acl2::if-of-t-and-nil-when-booleanp
            acl2::equal-of-if-constants
            acl2::if-becomes-myif ; todo: do we want this when lifting?
            ACL2::MYIF-BECOMES-BVIF-1-axe
            ACL2::BVCHOP-OF-MYIF
            ACL2::BVIF-OF-+-ARG4
            ACL2::BVIF-OF-+-ARG3
            ACL2::BVIF-OF---ARG3
            ACL2::BVIF-OF---ARG4
            ACL2::INTEGERP-OF-BVIF
            ACL2::INTEGERP-OF---when-integerp
            ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-BETTER
            ACL2::EQUAL-OF-BVPLUS-MOVE-BVMINUS-ALT-BETTER
            ACL2::BVPLUS-COMMUTATIVE-INCREASING-AXE
            ACL2::BVCHOP-OF-BVMOD
            ACL2::BVPLUS-OF-0-ARG2
            ACL2::BVMOD-OF-BVCHOP-ARG2
            ACL2::BVMOD-OF-BVCHOP-ARG3
            bvuminus-of-bvif-constants
            ACL2::BVPLUS-OF-BVIF-ARG2-SAFE
            ACL2::BVPLUS-OF-BVIF-ARG3-SAFE
            ACL2::EQUAL-OF-BVIF ;restrict to constant x?
            ACL2::EQUAL-OF-BVIF-alt ;restrict to constant x?
            ACL2::BVCHOP-OF-BVIF
            ;; just include boolean-rules?
            acl2::boolif-when-quotep-arg2
            acl2::boolif-when-quotep-arg3
            acl2::bvchop-1-becomes-getbit
            ACL2::BVCHOP-OF-BVSX
            ACL2::BVCHOP-OF-BVUMINUS-SAME
            ACL2::BVUMINUS-OF-BVUMINUS
            ACL2::BVSX-OF-BVCHOP
            ACL2::BVCHOP-OF-BVCHOP
            ACL2::BVPLUS-OF-BVCHOP-ARG2
            ACL2::EQUAL-OF-BVSX-AND-BVSX
            acl2::equal-same
            ACL2::BVPLUS-OF-LOGEXT ; rename
            ACL2::BVPLUS-OF-LOGEXT-arg1 ; rename
            ACL2::BVUMINUS-OF-LOGEXT
            ACL2::SIGNED-BYTE-P-OF-BVIF
            ACL2::LOGEXT-IDENTITY
            ACL2::SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-ONE-LESS
            ;ACL2::BOOLIF-X-X-Y ; introduces boolor
            ACL2::BVLT-OF-CONSTANT-WHEN-USB-DAG
            boolor-becomes-boolif
            ;bvlt-hack-1-gen
            ACL2::BVCHOP-SUBST-CONSTANT
            ACL2::BVCHOP-SUBST-CONSTANT-alt
            ;; acl2::boolif-of-t-and-nil-when-booleanp
            ACL2::BOOL-FIX$INLINE-CONSTANT-OPENER
            boolif-of-bvlt-strengthen-to-equal
            bvlt-reduce-when-not-equal-one-less
            ;; trying opening these up if they surive to the proof stage (TODO: Add the rest, or drop these?):
            jp-condition
            jnp-condition
            jz-condition
            jnz-condition)
          (extra-rules)
          (lifter-rules64-new) ; overkill?
          (acl2::base-rules)
          (acl2::core-rules-bv) ; trying
          (acl2::unsigned-byte-p-rules)
          (acl2::unsigned-byte-p-forced-rules)))
