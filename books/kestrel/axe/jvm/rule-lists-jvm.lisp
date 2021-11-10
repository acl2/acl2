; Lists of rule names (JVM-related)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that, as of March 2021, many of these rules are not yet open sourced.
;; This file just gives their names.

(include-book "kestrel/jvm/portcullis" :dir :system)
(include-book "../rule-lists")
(include-book "../rule-alists")

;; These are for concrete execution, which is not used much:
(defun jvm-execution-rules ()
  (declare (xargs :guard t))
  '(jvm::move-past-invoke-instruction
    jvm::update-nth-local ;bozo
    jvm::heapref-table ;bozo
    jvm::monitor-table ;bozo
    jvm::cur-class-name ;bozo
    jvm::stack ;bozo
    jvm::locals ;bozo
    jvm::class-table ;bozo
    jvm::top-operand ;bozo
    jvm::pop-operand ;bozo
    jvm::pc ;bozo
    jvm::thread-top-frame ;bozo
    jvm::thread-table ;bozo
    jvm::call-stack ;bozo
    jvm::heap ;bozo
    jvm::static-field-map ;bozo
    jvm::make-state ;bozo
    jvm::push-operand ;bozo
    jvm::make-frame ;bozo
    dom ;yuck?
    jvm::push-long
    jvm::pop-long
    jvm::top-long
    jvm::pop-items-off-stack
    jvm::pop-items-off-stack-aux
    ))

;; Rules about new addresses
(defun new-ad-rules ()
  (declare (xargs :guard t))
  '( ;;rules to simplidy sets of new addresses (could instead unroll n-new-ads?)
    insert-of-new-ad-of-insert-of-nth-new-ad ;new
    insert-of-nth-new-ad-of-insert-of-nth-new-ad
    insert-of-next-ad-onto-union-of-dom-and-n-new-adsalt-better
    insert-of-next-ad-onto-union-of-dom-and-n-new-adsalt-better-rev
    insert-of-next-ad-onto-union-of-dom-and-n-new-adsalt
    insert-new-ad-insert-2nd-new-adalt
    insert-new-ad-insert-2nd-new-ad
    insert-nth-new-ad-2-union-new-ads-slice-3
    insert-of-next-ad-onto-union-of-dom-and-n-new-ads
    insert-new-ad-union-new-ads-slice-2
    union-of-new-ads-slice-and-2set-of-n-new-ads-better
    union-2set-n-new-ads-2set-new-ads-slice
    union-2set-new-ads-slice-2set-n-new-ads
    union-commutative-2-2set-of-new-ads-slice
    nth-new-ad-collect

    insert-of-nth-new-ad-when-already-there-lemma ;;tue jul 28 21:21:47 2015
    insert-of-nth-new-ad-when-already-there-lemma-alt ;;tue jul 28 21:21:47 2015

    insert-of-new-ad-when-already-there-lemma      ;wed jul 29 01:08:20 2015
    insert-of-new-ad-when-already-there-lemma-alt  ;wed jul 29 01:08:20 2015

    ;; rules about new addresses in a heap in which some new addresses are already bound:
    nth-new-ad-of-insert-new-ad ;wed jun 23 21:01:49 2010
    new-ad-union-2set-n-new-ads-better
    nth-new-ad-of-union-dom-n-new-ads-better
;    address-hack-bbbozo ;since we have n-new-ads-becomes-n-new-ads-better
    address-hack-bbbozo-better
    nth-new-ad-of-union-dom-n-new-ads
    nth-new-ad-of-union-dom-n-new-ads-alt ;todo: adapt the better version above?
    new-ad-of-union-dom-and-n-new-ads
    new-ad-of-union-dom-and-n-new-adsalt
    new-ad-of-union-dom-and-n-new-adsalt-better

    memberp-of-nth-new-ad-and-n-new-ads-better
    new-ad-not-memberp-of-new-ads-slice2
    not-memberp-nth-new-ad-new-ads-slice
    not-memberp-of-new-ads-slice2
    memberp-of-nth-new-ad-and-new-ads-slice2
    not-memberp-n-new-ads2
    not-memberp-n-new-ads2-better
    memberp-nth-new-ad-n-new-ads

    in-of-new-ad-and-n-new-ads
    in-of-new-ad-and-n-new-ads2-better

    len-of-new-ads-slice
    len-of-n-new-ads2
    len-of-n-new-ads

    nth-of-new-ads-slice
    nth-of-n-new-ads2
    nth-of-n-new-ads

    ;; this causes problems (due to a rule ordering different when i changed some things?):
    ;;    n-new-ads-becomes-n-new-ads2 ;bozo put this in a list of heap rules? ;;tue jul 28 21:01:06 2015

    nth-new-ad-not-in-ads ;bozo why did this help (see dag2 below for a small example)? maybe something about not being able to resolve if tests?
    new-ad-not-memberp-ads

    not-equal-nth-new-ad-when-bound
    not-equal-nth-new-ad-when-bound-alt
    not-equal-new-ad-when-bound

;try to disable since null-refp is now kept closed, but we still need these:
;     equal-of-null-ref-turn-around ;loops with turn-equal-around-axe4
    equal-of-null-ref-and-new-ad
    equal-of-new-ad-and-null-ref
    equal-of-null-ref-and-nth-new-ad
    equal-of-nth-new-ad-and-null-ref

    not-null-refp-of-new-ad
    not-null-refp-of-nth-new-ad

    equal-new-ad-nil
    equal-new-ad-nil2
    equal-nth-new-ad-nil
    equal-nth-new-ad-nil2

    new-ad-not-equal-nth-new-ad2alt
    new-ad-not-equal-nth-new-ad2

    equal-nth-new-ad-nth-new-ad

    new-ads-slice-out-of-order-indices
    consp-of-new-ads-slice
    ;; do we need these?:
    car-of-new-ads-slice
    cdr-of-new-ads-slice
    ))

(defun address-rules ()
  (declare (xargs :guard t))
  '(addressfix-when-address-or-nullp-and-not-null-refp
    ;;addressp-when-address-or-nullp-and-not-null-refp ;looped!
    addressfix-of-new-ad
    addressfix-of-nth-new-ad
    addressfix-when-addressp
    addressp-when-array-refp
    addressp-of-new-ad
    addressp-of-nth-new-ad
    not-null-refp-when-array-refp
    null-refp-of-null-ref
    booleanp-of-null-refp
    booleanp-of-addressp))

;; Used for smart if handling
(defun step-state-with-pc-and-call-stack-height-rules ()
  (declare (xargs :guard t))
  '(step-state-with-pc-and-call-stack-height-of-myif ;pushes STEP-STATE-WITH-PC-AND-CALL-STACK-HEIGHT to the leaves
    step-state-with-pc-and-call-stack-height-does-nothing-1-axe ;drops it when the pc is wrong
    step-state-with-pc-and-call-stack-height-does-nothing-2-axe ;drops it when the call-stack-height is wrong (bozo should we match the whole stack not just its height?)
    step-state-with-pc-and-call-stack-height-becomes-step-axe ; go straight to do-inst? -- not if we want to manage the invokes...?
    ))

(defun run-until-return-from-stack-height-rules-common ()
  (declare (xargs :guard t))
  '(run-until-return ;opens to run-until-return-from-stack-height
    ;;these are used when we have a single make-state, not a myif-nest of states:
    run-until-return-from-stack-height-opener-fast-axe ;this goes straight to do-inst
    run-until-return-from-stack-height-base-axe))

;; These really split the execution when a branch is encountered. ;; Always
;; push run-until-return-from-stack-height into myif branches.
(defun run-until-return-from-stack-height-rules-split ()
  (declare (xargs :guard t))
  (append (run-until-return-from-stack-height-rules-common)
          '(run-until-return-from-stack-height-of-myif-split)))

;;these are for when we have a myif-nest of states and want to handle MYIFs
;;smartly (attempt to merge the executions at join points).
(defun run-until-return-from-stack-height-rules-smart ()
  (declare (xargs :guard t))
  (append (run-until-return-from-stack-height-rules-common)
          (step-state-with-pc-and-call-stack-height-rules)
          '(run-until-return-from-stack-height-of-myif-axe ;chooses a state to step and introduces STEP-STATE-WITH-PC-AND-CALL-STACK-HEIGHT
            ;; run-until-return-from-stack-height-of-myif-axe-alt ;fixme which of these do we prefer?
            run-until-return-from-stack-height-of-myif-axe-split-1 ;in case there are exeception states
            run-until-return-from-stack-height-of-myif-axe-split-2 ;in case there are exeception states
            )))

;; Since Axe cannot natively evaluate these functions
(defun jvm-constant-opener-rules ()
  (declare (xargs :guard t))
  '(jvm::typep-constant-opener
;    jvm::reference-typep-constant-opener
    jvm::array-typep-constant-opener
    jvm::class-or-interface-namep-constant-opener
    jvm::primitive-typep-constant-opener
    jvm::class-namep-constant-opener
    jvm::field-namep-constant-opener
    jvm::field-idp-constant-opener
    gen-init-bindings-for-class-constant-opener
    jvm::set-static-field-constant-opener
    jvm::get-static-field-constant-opener
    set-field-constant-opener
    get-field-constant-opener
    jvm::extract-package-name-from-class-name-constant-opener
    string-contains-charp-constant-opener
    position-equal-constant-opener
    position-equal-ac-constant-opener
    substring-before-last-occurrence-constant-opener
    common-lisp::reverse-constant-opener
    common-lisp::revappend-constant-opener
    substring-after-terminator-constant-opener
    readthroughterminator-aux-constant-opener
    jvm::bound-in-class-tablep-constant-opener
    jvm::binding-constant-opener
    jvm::bind-constant-opener
    jvm::lookup-method-in-classes-constant-opener
    jvm::initialize-one-dim-array-constant-opener
    jvm::make-frame-constant-opener
    jvm::count-slots-in-types-constant-opener
    jvm::type-slot-count-constant-opener
    jvm::get-array-component-type-constant-opener
    alistp-constant-opener
    jvm::field-publicp-constant-opener
    jvm::field-privatep-constant-opener
    jvm::field-protectedp-constant-opener
    jvm::field-staticp-constant-opener
    jvm::field-access-flags-constant-opener

    jvm::method-access-flags-constant-opener
    jvm::method-publicp-constant-opener
    jvm::method-privatep-constant-opener
    jvm::method-protectedp-constant-opener
    jvm::method-staticp-constant-opener
    jvm::method-nativep-constant-opener
    jvm::method-abstractp-constant-opener
    jvm::method-synchronizedp-constant-opener

    jvm::any-less-than-zero-constant-opener

    jvm::pc-constant-opener
    jvm::locals-constant-opener
    jvm::stack-constant-opener
    jvm::method-info-constant-opener
    jvm::method-designator-constant-opener))

;; Rules for executing JVM instructions and model methods (but not for
;; simplifying JVM expressions/states -- those are separate).
(defun jvm-semantics-rules ()
  (declare (xargs :guard t))
  '(jvm::execute-tableswitch
    jvm::execute-aaload
    jvm::execute-aastore
    jvm::execute-aconst_null
    jvm::execute-aload
    jvm::execute-aload_x
    jvm::execute-anewarray
    jvm::execute-areturn
    jvm::execute-arraylength
    jvm::execute-astore
    jvm::execute-astore_x
    jvm::execute-baload
    jvm::execute-bastore
    jvm::execute-bipush
    jvm::execute-caload
    jvm::execute-castore
    jvm::execute-dup
    jvm::execute-dup_x1
    jvm::execute-dup_x2
    jvm::execute-dup2
    jvm::execute-dup2_x1
    jvm::execute-dup2_x2
    jvm::execute-getfield
    jvm::execute-getstatic
    jvm::execute-goto
    jvm::execute-goto_w
    jvm::execute-i2b
    jvm::execute-i2c
    jvm::execute-i2l
    jvm::execute-i2s
    jvm::execute-iadd
    jvm::execute-iaload
;    jvm::execute-iaload-rewrite
    jvm::execute-iand
    jvm::execute-iastore
    jvm::execute-iconst_x
    jvm::execute-dconst_x
    jvm::execute-fconst_x
    jvm::execute-idiv
    jvm::execute-if_acmpeq
    jvm::execute-if_acmpne
    jvm::execute-if_icmpeq
    jvm::execute-if_icmpge
    jvm::execute-if_icmpgt
    jvm::execute-if_icmple
    jvm::execute-if_icmplt
    jvm::execute-if_icmpne
    jvm::execute-ifeq
    jvm::execute-ifge
    jvm::execute-ifgt
    jvm::execute-ifle
    jvm::execute-iflt
    jvm::execute-ifne
    jvm::execute-ifnonnull
    jvm::execute-ifnull
    jvm::execute-iinc
    jvm::execute-iload
    jvm::execute-iload_x
    jvm::execute-imul
    jvm::execute-ineg
    jvm::execute-instanceof
    jvm::execute-checkcast
    jvm::type-implementsp-base-1
    jvm::type-implementsp-base-2
    jvm::type-implementsp-base-3
    jvm::type-implementsp-base-4
    jvm::type-implementsp-base-5
    jvm::type-implementsp-unroll
    jvm::type-implementsp-of-same ;saves having to unroll for arrays of non-primitives

    jvm::execute-invokeinterface

    jvm::execute-invokespecial                  ;exposes the helper
    jvm::execute-invokespecial-helper-base ;opens the helper if we can resolve things

    jvm::execute-invokestatic                  ;exposes the helper
    jvm::execute-invokestatic-helper-base ;opens the helper if we can resolve things

    jvm::execute-invokevirtual                  ;exposes the helper
    jvm::execute-invokevirtual-helper-base ;opens the helper if we can resolve things

    jvm::invoke-static-initializer-for-next-class-base
    jvm::invoke-static-initializer-for-next-class-helper-base
    jvm::invoke-static-initializer-for-class-base

    jvm::execute-ior
    jvm::execute-irem
    jvm::execute-ireturn
    jvm::execute-dreturn
    jvm::execute-freturn
    jvm::void-return-core
    jvm::return-core-long
    jvm::return-core
    jvm::execute-ishl
    jvm::ishr32
    jvm::ishr64
    jvm::execute-ishr
    jvm::execute-istore
    jvm::execute-istore_x
    jvm::execute-isub
    jvm::execute-iushr
    jvm::execute-ixor
    jvm::execute-lookupswitch
    jvm::execute-jsr
    jvm::execute-jsr_w
    jvm::execute-l2i
    jvm::execute-ladd
    jvm::execute-laload
    jvm::execute-land
    jvm::execute-lastore
    jvm::execute-lcmp
    jvm::execute-lconst_x
    jvm::execute-ldc
    jvm::execute-ldc2_w
    jvm::execute-ldiv
    jvm::execute-lload
    jvm::execute-lload_x
    jvm::execute-lmul
    jvm::execute-lneg
    jvm::execute-lor
    jvm::execute-lrem
    jvm::execute-lreturn
    jvm::execute-lshl
    jvm::execute-lshr
    jvm::execute-lstore
    jvm::execute-lstore_x
    jvm::execute-lsub
    jvm::execute-lushr
    jvm::execute-lxor
    jvm::execute-monitorenter
    jvm::execute-monitorexit
    jvm::execute-multianewarray
    jvm::execute-new-base-opener-safe ;;jvm::execute-new
    jvm::execute-newarray
    jvm::execute-nop
    jvm::execute-pop
    jvm::execute-pop2
    jvm::execute-putfield
    jvm::execute-putstatic
    jvm::execute-ret
    jvm::execute-return
    jvm::execute-saload
    jvm::execute-sastore
    jvm::execute-sipush
    jvm::execute-swap

    jvm::execute-d2f
    jvm::execute-d2i
    jvm::execute-d2l
    jvm::execute-fadd
    jvm::execute-fmul
    jvm::execute-fdiv
    jvm::execute-frem
    jvm::execute-fsub
    jvm::execute-dadd
    jvm::execute-dmul
    jvm::execute-ddiv
    jvm::execute-drem
    jvm::execute-dsub
    jvm::execute-fneg
    jvm::execute-dneg
    jvm::execute-faload
    jvm::execute-daload
    jvm::execute-fastore
    jvm::execute-dastore
    jvm::execute-f2i
    jvm::execute-f2d
    jvm::execute-f2l
    jvm::execute-i2f
    jvm::execute-i2d
    jvm::execute-l2d
    jvm::execute-l2f
    jvm::execute-fcmpg
    jvm::execute-fcmpl
    jvm::execute-dcmpg
    jvm::execute-dcmpl

    jvm::execute-fload
    jvm::execute-dload
    jvm::execute-fstore
    jvm::execute-dstore

    jvm::execute-fload_x
    jvm::execute-dload_x
    jvm::execute-fstore_x
    jvm::execute-dstore_x

    ;;TODO: these should be tried in order based on how often each type of instruction is executed
    jvm::do-inst-of-tableswitch
    jvm::do-inst-of-aaload
    jvm::do-inst-of-aastore
    jvm::do-inst-of-aconst_null
    jvm::do-inst-of-aload
    jvm::do-inst-of-aload_0
    jvm::do-inst-of-aload_1
    jvm::do-inst-of-aload_2
    jvm::do-inst-of-aload_3
    jvm::do-inst-of-anewarray
    jvm::do-inst-of-areturn
    jvm::do-inst-of-arraylength
    jvm::do-inst-of-astore
    jvm::do-inst-of-astore_0
    jvm::do-inst-of-astore_1
    jvm::do-inst-of-astore_2
    jvm::do-inst-of-astore_3
    jvm::do-inst-of-baload
    jvm::do-inst-of-bastore
    jvm::do-inst-of-bipush
    jvm::do-inst-of-caload
    jvm::do-inst-of-castore
    jvm::do-inst-of-dup
    jvm::do-inst-of-dup_x1
    jvm::do-inst-of-dup_x2
    jvm::do-inst-of-dup2
    jvm::do-inst-of-dup2_x1
    jvm::do-inst-of-dup2_x2
    jvm::do-inst-of-getfield
    jvm::do-inst-of-getstatic
    jvm::do-inst-of-goto
    jvm::do-inst-of-goto_w
    jvm::do-inst-of-i2b
    jvm::do-inst-of-i2c
    jvm::do-inst-of-i2l
    jvm::do-inst-of-i2s
    jvm::do-inst-of-iadd
    jvm::do-inst-of-iaload
    jvm::do-inst-of-iand
    jvm::do-inst-of-iastore
    jvm::do-inst-of-iconst_m1
    jvm::do-inst-of-iconst_0
    jvm::do-inst-of-iconst_1
    jvm::do-inst-of-iconst_2
    jvm::do-inst-of-iconst_3
    jvm::do-inst-of-iconst_4
    jvm::do-inst-of-iconst_5
    jvm::do-inst-of-idiv
    jvm::do-inst-of-if_acmpeq
    jvm::do-inst-of-if_acmpne
    jvm::do-inst-of-if_icmpeq
    jvm::do-inst-of-if_icmpge
    jvm::do-inst-of-if_icmpgt
    jvm::do-inst-of-if_icmple
    jvm::do-inst-of-if_icmplt
    jvm::do-inst-of-if_icmpne
    jvm::do-inst-of-ifeq
    jvm::do-inst-of-ifge
    jvm::do-inst-of-ifgt
    jvm::do-inst-of-ifle
    jvm::do-inst-of-iflt
    jvm::do-inst-of-ifne
    jvm::do-inst-of-ifnonnull
    jvm::do-inst-of-ifnull
    jvm::do-inst-of-iinc
    jvm::do-inst-of-iload
    jvm::do-inst-of-iload_0
    jvm::do-inst-of-iload_1
    jvm::do-inst-of-iload_2
    jvm::do-inst-of-iload_3
    jvm::do-inst-of-imul
    jvm::do-inst-of-ineg
    jvm::do-inst-of-instanceof
    jvm::do-inst-of-checkcast
    jvm::do-inst-of-invokeinterface
    jvm::do-inst-of-invokespecial
    jvm::do-inst-of-invokestatic
    jvm::do-inst-of-invokevirtual
    jvm::do-inst-of-ior
    jvm::do-inst-of-irem
    jvm::do-inst-of-ireturn
    jvm::do-inst-of-ishl
    jvm::do-inst-of-ishr
    jvm::do-inst-of-istore
    jvm::do-inst-of-istore_0
    jvm::do-inst-of-istore_1
    jvm::do-inst-of-istore_2
    jvm::do-inst-of-istore_3
    jvm::do-inst-of-isub
    jvm::do-inst-of-iushr
    jvm::do-inst-of-ixor
    jvm::do-inst-of-lookupswitch
    jvm::do-inst-of-jsr
    jvm::do-inst-of-jsr_w
    jvm::do-inst-of-l2i
    jvm::do-inst-of-ladd
    jvm::do-inst-of-laload
    jvm::do-inst-of-land
    jvm::do-inst-of-lastore
    jvm::do-inst-of-lcmp
    jvm::do-inst-of-lconst_0
    jvm::do-inst-of-lconst_1
    jvm::do-inst-of-ldc
    jvm::do-inst-of-ldc_w
    jvm::do-inst-of-ldc2_w
    jvm::do-inst-of-ldiv
    jvm::do-inst-of-lload
    jvm::do-inst-of-lload_0
    jvm::do-inst-of-lload_1
    jvm::do-inst-of-lload_2
    jvm::do-inst-of-lload_3
    jvm::do-inst-of-lmul
    jvm::do-inst-of-lneg
    jvm::do-inst-of-lor
    jvm::do-inst-of-lrem
    jvm::do-inst-of-lreturn
    jvm::do-inst-of-lshl
    jvm::do-inst-of-lshr
    jvm::do-inst-of-lstore
    jvm::do-inst-of-lstore_0
    jvm::do-inst-of-lstore_1
    jvm::do-inst-of-lstore_2
    jvm::do-inst-of-lstore_3
    jvm::do-inst-of-lsub
    jvm::do-inst-of-lushr
    jvm::do-inst-of-lxor
    jvm::do-inst-of-monitorenter
    jvm::do-inst-of-monitorexit
    jvm::do-inst-of-multianewarray
    jvm::do-inst-of-new
    jvm::do-inst-of-newarray
    jvm::do-inst-of-nop
    jvm::do-inst-of-pop
    jvm::do-inst-of-pop2
    jvm::do-inst-of-putfield
    jvm::do-inst-of-putstatic
    jvm::do-inst-of-ret
    jvm::do-inst-of-return
    jvm::do-inst-of-saload
    jvm::do-inst-of-sastore
    jvm::do-inst-of-sipush
    jvm::do-inst-of-swap

    jvm::do-inst-of-dreturn
    jvm::do-inst-of-freturn

    jvm::do-inst-of-dconst_0
    jvm::do-inst-of-dconst_1

    jvm::do-inst-of-fconst_0
    jvm::do-inst-of-fconst_1
    jvm::do-inst-of-fconst_2

    jvm::do-inst-of-d2f
    jvm::do-inst-of-d2i
    jvm::do-inst-of-d2l
    jvm::do-inst-of-fadd
    jvm::do-inst-of-fmul
    jvm::do-inst-of-fdiv
    jvm::do-inst-of-frem
    jvm::do-inst-of-fsub
    jvm::do-inst-of-dadd
    jvm::do-inst-of-dmul
    jvm::do-inst-of-ddiv
    jvm::do-inst-of-drem
    jvm::do-inst-of-dsub
    jvm::do-inst-of-fneg
    jvm::do-inst-of-dneg
    jvm::do-inst-of-faload
    jvm::do-inst-of-daload
    jvm::do-inst-of-fastore
    jvm::do-inst-of-dastore
    jvm::do-inst-of-f2i
    jvm::do-inst-of-f2d
    jvm::do-inst-of-f2l
    jvm::do-inst-of-i2f
    jvm::do-inst-of-i2d
    jvm::do-inst-of-l2d
    jvm::do-inst-of-l2f
    jvm::do-inst-of-fcmpg
    jvm::do-inst-of-fcmpl
    jvm::do-inst-of-dcmpg
    jvm::do-inst-of-dcmpl

    jvm::do-inst-of-fload
    jvm::do-inst-of-dload
    jvm::do-inst-of-fstore
    jvm::do-inst-of-dstore

    jvm::do-inst-of-fload_0
    jvm::do-inst-of-fload_1
    jvm::do-inst-of-fload_2
    jvm::do-inst-of-fload_3

    jvm::do-inst-of-dload_0
    jvm::do-inst-of-dload_1
    jvm::do-inst-of-dload_2
    jvm::do-inst-of-dload_3

    jvm::do-inst-of-fstore_0
    jvm::do-inst-of-fstore_1
    jvm::do-inst-of-fstore_2
    jvm::do-inst-of-fstore_3

    jvm::do-inst-of-dstore_0
    jvm::do-inst-of-dstore_1
    jvm::do-inst-of-dstore_2
    jvm::do-inst-of-dstore_3

    jvm::execute-java.lang.system.arraycopy
    jvm::execute-java.lang.object.getclass
    jvm::execute-java.lang.class.getprimitiveclass

    jvm::is-java.lang.system.arraycopy
    jvm::is-java.lang.object.getclass
    jvm::is-java.lang.float.floattorawintbits
    jvm::is-java.lang.float.intbitstofloat))

;; jvm-specific rules used to simplify expressions (but not to actually do symbolic execution)
;; todo: factor out some map rules, etc
(defun jvm-simplification-rules-jvm ()
  (declare (xargs :guard t))
  (append (jvm-constant-opener-rules)
          (new-ad-rules)
          (address-rules)
          '(set::delete-constant-opener ;needed for address calcs
            set::tail-constant-opener   ;needed for address calcs
            set::head-constant-opener   ;needed for address calcs
            set::empty-constant-opener  ;needed for address calcs
            set::sfix-constant-opener   ;needed for address calcs
            set::setp-constant-opener   ;needed for address calcs
            fast-<<-constant-opener     ;needed for address calcs
            ;; do-inst-of-myif
            jvm::intern-tablep-of-intern-table
            jvm::intern-tablep-of-empty-intern-table
            jvm::string-has-been-internedp-of-empty-intern-table

            ;; arrays:
            array-object-fields
            ;; jvm::size-of-array-element
            unsigned-byte-p-when-array-refp
            address-or-nullp-when-array-refp
            equal-of-get-field-contents-and-nil-when-array-refp
            equal-of-nil-and-get-field-contents-when-array-refp
            array-refp-of-set-field-of-set-field-initialize
            array-refp-of-set-field-irrel-one-dim-primitive
            array-refp-of-set-field-irrel-one-dim-non-primitive
            array-refp-of-set-field-contents-same
            ;; get-class-when-array-refp ; enable this if we disable get-class
            get-field-class-when-array-refp
            get-field-class-when-array-ref-listp-one-dim
            jvm::make-array-type      ;dangerous?
            acl2::array-contents ;; we enable this to expost get-field

            ;; rules about initialize-one-dim-array:
            jvm::get-field-class-of-initialize-one-dim-array
            jvm::get-field-contents-of-initialize-one-dim-array
            jvm::get-length-field-of-initialize-one-dim-array
            jvm::get-field-of-initialize-one-dim-array-irrel-ad
            jvm::get-field-of-initialize-one-dim-array-irrel-field
            jvm::rkeys-of-initialize-one-dim-array

            rkeys-of-myif ;move to a maps-rules list?
            jvm::decode-signed-non-neg
            ;; todo: add some float and double stuff here!

            jvm::make-method-designator
            jvm::sub-classp
            jvm::sub-class-or-same-classp
            jvm::in-same-packagep
;jvm::extract-package-name-from-class-name
;acl2::string-contains-charp
            jvm::field-accessiblep
            jvm::field-is-staticp
            jvm::resolve-class
            jvm::resolve-non-array-class
            jvm::get-class-object
            equal-of-minus-1-and-null-ref
            jvm::is-array-typep
            ;;very new:
            jvm::lookup-offset-for-match

            ;; all this stuff is new:
            jvm::get-array-element-type-base
            jvm::get-array-element-type-unroll
            get-array-dimensions-of-ref
            get-array-dimensions-of-ref-aux-base-1
            get-array-dimensions-of-ref-aux-base-2
            get-array-dimensions-of-ref-aux-unroll
            get-field-class-of-inner-array-2d
            addressp-of-nth-of-array-contents
            <-when-sbvlt-constants ;needed to show array refs are in bounds
            jvm::in-of-rkeys-when-g
            jvm::in-of-rkeys-when-g-rev
            not-null-refp-of-nth-of-array-contents
            equal-of-ad-and-nth-of-get-field-same
            len-of-contents-of-nth-of-array-contents
            refs-differ-when-array-dimensions-differ
            refs-differ-when-array-dimensions-differ-alt
            sbvlt-of-bvplus-of-constant-and-constant
            sbvlt-of-bvmult-4-and-0
            sbvlt-of-bvmult-4-and-16
            get-array-dimensions-of-ref-aux-of-set-field-irrel
            jvm::number-of-array-dimensions-constant-opener
            get-array-dimensions-of-ref-aux-of-set-field-same-1d

            jvm::field-id-type-constant-opener

            ;; acl2::return-last-rewrite

            ;; call stacks:
            jvm::empty-call-stackp ;; open to expose a claim about call-stack-size
            jvm::top-frame-of-push-frame
            jvm::pop-frame-of-push-frame
            ;; jvm::empty-call-stackp-of-pop-frame
            ;; jvm::empty-call-stackp-of-push-frame
            jvm::call-stack-size-of-pop-frame
            jvm::call-stack-size-of-push-frame
            jvm::call-stack-size-of-push-frame-of-push-frame
            jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame
            jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame-of-push-frame ;make a version of this for operand-stack-size?
            jvm::call-stack-size-lemma         ;needed?
            jvm::one-plus-call-stack-size-hack ;needed?
            jvm::<-of-call-stack-size-and-plus-of-call-stack-size-of-pop-frame ;needed?
            jvm::equal-of-+-of-call-stack-size-combine-constants
            jvm::not-equal-of-call-stack-size-and-constant-when-negative

            ;; helps with symbolic execution:
            extract-control-information-from-stack-of-push-frame

            ;; operand stacks:
            jvm::top-operand-of-push-operand
            jvm::pop-operand-of-push-operand
            jvm::top-long-of-push-long
            jvm::pop-long-of-push-long
            jvm::pop-operand-of-pop-operand-of-push-long ;does this break the operand stack abstraction?

            ;; rules about operand-stack-size:
            jvm::operand-stack-size-of-empty-operand-stack
            jvm::operand-stack-size-of-push-operand
            jvm::operand-stack-size-of-pop-operand
            jvm::operand-stack-size-of-push-long
            jvm::operand-stack-size-of-pop-long
            jvm::operand-stack-size-of-nil
            jvm::operand-stack-size-bound ;renme

            ;; rules about popn-operands:
            jvm::popn-operands-base
            jvm::popn-operands-opener

            ;; rules about topn-operands:
            jvm::topn-operands-of-push-operand
            jvm::topn-operands-of-0

            ;; rules about pop-items-off-stack:
            jvm::pop-items-off-stack
            jvm::pop-items-off-stack-aux-base
            jvm::pop-items-off-stack-aux-unroll

;jvm::string-has-been-internedp-of-myif ;fri jun 13 21:44:00 2014

            jvm::make-field-id
            jvm::get-field-ids

            ;; array building:
            jvm::build-new-array
            jvm::build-new-array-default
            jvm::build-multi-dim-array-base
            jvm::build-multi-dim-array-unroll
            jvm::build-multi-dim-arrays-base
            jvm::build-multi-dim-arrays-unroll
            jvm::initial-array-contents
            ;; len-of-initial-array-contents ;; not needed if we enable initial-array-contents
            ;; consp-of-initial-array-contents ;; not needed if we enable initial-array-contents

            get-field-reassemble-class ;maybe needed because of when we break the abstraction?

            set-class ;; open to expose set-field ;todo: try disabled?
            get-class ;; open to expose get-field ;todo: try disabled?

            ;; rules about any-less-than-zero (there is also a constant-opener above):
            jvm::any-less-than-zero-of-reverse-list
            jvm::any-less-than-zero-of-true-list-fix ;needed?
            jvm::any-less-than-zero-of-cons
            jvm::any-less-than-zero-of-nil

            null-refp-of-myif

            ;; jvm::obtain-and-throw-exception ;; leave this closed to stop the execution

            jvm::no-explicit-invokep
            jvm::len-of-invoke-instruction-constant-opener ;jvm::len-of-invoke-instruction ;could build in to the evaluator
            jvm::move-past-invoke-instruction
            eql-becomes-equal
            not-addressp-of-null-ref
            ;; address-or-nullp ;;trying...

            address-or-nullp-of-new-ad
            address-or-nullp-of-nth-new-ad
            address-or-nullp-of-null-ref
            address-or-nullp-when-addressp-free
            addressp-when-address-or-nullp-free
            jvm::addressp-of-myif
            in-of-rkeys-of-s-one
            in-of-rkeys-of-s-two
            ;; todo: keep these disabled?
            jvm::class-decl-access-flags
            jvm::class-decl-non-static-fields
            jvm::class-decl-static-fields
            jvm::class-decl-methods
            jvm::class-decl-interfaces
            jvm::class-decl-superclass ;or just run it?
            jvm::class-decl-interfacep

            jvm::get-superclass
            jvm::lookup-method-for-invokespecial
            jvm::lookup-method-for-invokespecial-aux-unroll
            jvm::lookup-method-for-invokespecial-aux-base-1
            jvm::lookup-method-for-invokespecial-aux-base-2
            jvm::lookup-method-for-invokespecial-aux-base-3
            jvm::lookup-method-for-invokespecial-aux-base-4
            jvm::superclassp
;jvm::classp
            jvm::bound-to-a-classp
            jvm::bound-to-an-interfacep
            jvm::make-one-dim-array-type
            ;; jvm::array-classp
;jvm::non-array-classp
            jvm::class-implements-interfacep
            jvm::get-superinterfaces-aux-base
            jvm::get-superinterfaces-aux-opener
            acl2::get-superinterfaces
;     get-class-of-initialize-2d-array
;     get-class-field-of-initialize-2d-array
            jvm::intern-table-of-make-state
            equal-of-nil-and-len
            jvm::get-interned-string-of-set-interned-string-same
            jvm::string-has-been-internedp-of-set-interned-string-same
;jvm::string-has-been-internedp-of-nil
            ;;jvm::get-interned-string-of-nil
            jvm::get-interned-string-of-empty-intern-table
            equal-nil-s
            jvm::equal-nil-string-to-char-list

            logext-when-usb-cheap ;new, since logext is still used a little bit (for arraycopy?)
            logext-identity-when-usb-smaller-dag

            jvm::op-code

            jvm::call-stack

            ;; call-stack-of-make-state-of-thread-table

            first-non-member-when-member ;new
            first-non-member-when-memberp
            first-non-member-when-not-memberp

            alistp-of-bind

;    jvm::encode-unsigned ;;is a macro!
            cancel-<-+

            s-same-s
            s-diff-s-axe
;    null-ref
            equal-of-nil-and-null-ref
            equal-of-null-ref-and-nil

            eq
;    atom ;fri dec 24 16:38:27 2010
            jvm::initialize-static-fields-unroll ;todo: what if we don't do this?  can we handle this with rules?
            jvm::initialize-static-fields-base
            default-value
;    strip-cars-opener
            strip-cars-of-non-consp
            bvand-of-logext
            bvand-of-logext-alt

            ;; rules about get-field:
            get-field-of-set-field-both ;todo: try this one first
            ;; don't need these 3 if we have get-field-of-set-field-both:
            ;; get-field-of-set-field-diff-1
            ;; get-field-of-set-field-diff-2
            ;; get-field-of-set-field-same
            get-field-of-set-fields
            get-field-of-init-ref-in-heap-diff-ref

            ;; rules about set-field:
            set-field-of-set-field-same
            set-field-of-set-field-reorder-pairs ;; requires the ref to be the same
            set-field-of-set-field-diff-1-constant-ads ;trying

            jvm::binding-bind
            jvm::bind-bind
            jvm::lookup-method-in-class-info-constant-opener
            lookup-method-in-classes-peel-off-one-axe
            lookup-method-in-classes-base
            lookup-method-in-classes-of-cons-1 ; in case the list of classes is not constant
            lookup-method-in-classes-of-cons-2 ; in case the list of classes is not constant

            ;;     jvm::in-list-1
            ;;     jvm::in-list-2
            ;;     jvm::in-list-base
;     jvm::method-native

            ;;maps (why needed?):
            g-same-s
            g-diff-s

            jvm::lookup-field-unroll
;    jvm::lookup-field-base-1 ;should never happen (counter hitting zero)
            jvm::lookup-field-base-2
            jvm::lookup-field-base-3
            jvm::resolve-field
            jvm::lookup-field-lst-opener
            jvm::lookup-field-lst-base
            jvm::get-field-info ;todo: or just execute it

            ;; Method resolution:
            jvm::resolve-method-step-2
            jvm::resolve-method
            jvm::resolve-class-method
            jvm::resolve-interface-method
            jvm::resolve-method-step-2-aux-base-1
            jvm::resolve-method-step-2-aux-base-2
            jvm::resolve-method-step-2-aux-unroll

            ;; jvm::long-fix
            jvm::pc-if-when-test-is-constant
            make-state-when-pc-if-is-around-pc
            make-state-when-myif-is-around-method-designator ;mon jul  5 22:24:05 2010
            make-state-when-myif-is-around-method-info ;mon jul  5 22:24:05 2010

            jvm::thread-top-frame-of-make-state-of-bind
            jvm::thread-top-frame-of-make-state-of-thread-table ;newer

;     th-rewrite
;     jvm::make-method-info
;    jvm::base-class-def

;     jvm::primitive-typep ;mon jun  7 16:28:20 2010
            jvm::primitive-typep-base
            jvm::array-typep-base
;    jvm::default-value1
;     jvm::lock-object
;    jvm::unlock-object
;     jvm::objectlockable?
            jvm::attempt-to-enter-monitor
            jvm::thread-owns-monitorp
            jvm::decrement-mcount

            jvm::intern-string ;try with this disabled?

            jvm::current-inst

            ;; frames:
            jvm::locked-object-of-make-frame
            jvm::pc-of-make-frame
            jvm::locals-of-make-frame
            jvm::stack-of-make-frame
            jvm::method-designator-of-make-frame
            jvm::method-info-of-make-frame
            ;; todo: rename to frame-method-descriptor, etc.:
            jvm::cur-method-descriptor
            jvm::cur-method-name
            jvm::cur-class-name

            jvm::thread-table-of-make-state
            jvm::heap-of-make-state
            jvm::class-table-of-make-state
            jvm::heapref-table-of-make-state
            jvm::monitor-table-of-make-state
            jvm::static-field-map-of-make-state
            jvm::initialized-classes-of-make-state

            jvm::get-superclasses-aux-opener
            jvm::get-superclasses-aux-base
            get-superclasses ;class-decl-superclasses ;should we add this to eval-fn?
;     jvm::method-sync
            jvm::method-program-constant-opener ; we keep method-program itself closed because it is used in 'poised' assumptions
            jvm::method-program-of-acons
            jvm::lookup-method
;     rkeys-of-initialize-2d-array-same
            get-static-field-of-set-static-field-same
            get-static-field-of-set-static-field-diff
;     get-field-contents-of-initialize-2d-array-same

            jvm::step-opener ;open step to expose do-inst (todo: drop this, but we must change step-state-with-pc-and-call-stack-height to call step-always-open...)

;degenerate case?
            get-field-of-nth-new-ad-same-heap
            initialize-one-dim-array-of-myif
            get-field-of-myif2
            get-field-of-myif
            new-ad-of-myif
            rkeys-of-set-field
            rkeys-of-set-field-both
            rkeys-of-set-fields

;logext-list (where should this go?)
;     not-logext-list-rewrite ;bozo why this phrasing needed exactly
;     consp-of-logext-list
;     logext-list-of-myif-drop-logext-lists-arg1
;     logext-list-of-myif-drop-logext-lists-arg2
;     logext-list-of-myif-of-logext-list-arg1
;     logext-list-of-myif-of-logext-list-arg2
;     bv-array-write-of-myif-of-logext-list

            ;;sets:
            insert-of-myif
            insert-of-myif2

            ;;maps:
            g-of-myif
            g-of-myif2

            ;; rules to push a myif down into the state components when merging states
            jvm::myif-of-make-state-and-make-state
            jvm::myif-of-make-frame
            jvm::myif-of-push-frame-and-push-frame
            jvm::myif-of-push-operand-and-push-operand
            jvm::myif-of-bind-and-bind
            jvm::myif-of-set-field-and-set-field
            jvm::myif-of-update-nth-local-same ;faster special case
            jvm::myif-of-update-nth-local-arg1
            jvm::myif-of-update-nth-local-arg2
            ;; jvm::myif-of-set-field-1-strong
            ;; jvm::myif-of-set-field-2-strong
            jvm::myif-of-set-field-1
            jvm::myif-of-set-field-2

            ;; since new ads are not nil:
            jvm::myif-of-nth-new-ad ;added when myif-when-not-nil disabled.
            jvm::myif-of-new-ad

            jvm::thread-classp
            stack-height

            init-ref-in-heap ;trying...

;     get-field-contents-of-initialize-2d-array-sub-array

            fastg-becomes-g

            ;; local variables:
            jvm::nth-local-constant-opener
            jvm::nth-local-of-update-nth-local-same
            jvm::nth-local-of-update-nth-local-diff
            jvm::nth-local-of-myif
            jvm::len-of-update-nth-local
            ;; jvm::update-nth-local-constant-opener
            jvm::update-nth-local-of-update-nth-local-same
            jvm::update-nth-local-of-update-nth-local-diff
            jvm::update-nth-local-of-nth-local-same
            jvm::uninitialized-locals ;; would like to keep disabled to prevent the locals from being a constant, but that causes problem with the lifter tries to evaluate a call
            jvm::initialize-locals
            jvm::initialize-locals-aux-unroll
            jvm::initialize-locals-aux-base

            ;;set stuff (probably used for sets of addresses):
            in-of-insert-irrel

;pretty basic (needed to compare stack heights to decide whether to step?):
            fold-consts-in-+
            hack-arith-cancel

            nth-append-1
            nth-append-2

            nfix ;okay?

;     len-of-logext-list

;     jvm::byte-or-bit-fix-val ;yuck?

            integerp-nth-of-get-field-contents-when-array-refp2

            set::insert-identity
            in-of-2set
            set::union-in
            setp-of-rkeys

            set::repeated-insert

            array-contents-okp

            len-of-contents-when-array-refp
            ;;array-length-when-array-refp

            in-of-rkeys-when-array-refp

            ;; initializing objects:
            gen-init-bindings-base
            gen-init-bindings-unroll
            gen-init-bindings-for-class-unroll
            gen-init-bindings-for-class-base

;     true-listp-of-get-field-contents-of-initialize-2d-array-same-2
            true-listp-of-get-field-contents
;    jvm::int-fix
;     get-field-length-of-initialize-2d-array-same-2
            array-length-when-a-row-of-a-2d-array

;    get-field-of-initialize-2d-array-irrel
;     get-class-of-initialize-2d-array-sub-array
            get-field-reassemble-array-contents
;get-field-reassemble-array-type ;gross!

            if-thm ;bozo

            ;;    if-of-non-nil ;slow? wed jan 13 21:22:18 2010

            ;;    natp-means-non-neg ;loops with defn natp - limit somehow? ;thu may 17 00:02:17 2012

;     bvchop-list-of-logext-list

;     get-field-type-from-array-refp-better ;fixme do we need this?
;    s-shl-becomes-bvcat-gen-eric
;     |2d-array-type-lemma| ;fixme do we need this?

            logtail-of-logext
;     bv-array-read-of-logext-list
;     bv-array-write-of-logext-list
            bv-array-write-of-logext-around-value-gen

            dom

            jvm::class-or-interface-namep
            jvm::reference-typep
            null

            jvm::intern-table-okp-of-set-field-irrel-pair
            jvm::intern-table-okp-of-set-field-irrel-ad
            jvm::intern-table-okp-of-set-field-2
            jvm::intern-table-okp-of-intern-table-and-heap
            jvm::not-member-equal-of-new-ad-of-rkeys-and-strip-cdrs-when-intern-table-okp ;gen
            jvm::not-null-refp-of-get-interned-string
            not-equal-nil-when-syntactically-a-bv-axe

            n-new-ads2-constant-opener
            new-ad-constant-opener
            new-ad-aux-constant-opener
            nth-new-ad-constant-opener
            memberp-constant-opener

            ;; class-tables:
            ;; also some rules about g and s ...
            jvm::bound-in-class-tablep-of-set-class-info
            jvm::get-class-info-of-set-class-info
            jvm::get-class-info-of-set-classes
            jvm::bound-in-class-tablep-of-set-classes
; jvm::bound-in-class-tablep-of-s
            jvm::bound-in-class-tablep-when-equal-of-get-class-info ;drop?

            primitive-array-contents-okp-of-int
            primitive-array-contents-okp-of-byte
            primitive-array-contents-okp-of-boolean
            primitive-array-contents-okp-of-short
            primitive-array-contents-okp-of-char
            primitive-array-contents-okp-of-long
            primitive-array-contents-okp-of-float
            primitive-array-contents-okp-of-double

            jvm::skip-invokestatic-instruction
            )))

;; all rules needed to simplify JVM expressions (but not to actually do symbolic execution)
(defun jvm-simplification-rules ()
  (declare (xargs :guard t))
  (append (list-rules) ;; for array dimensions (e.g., consp-of-cons)
          (jvm-simplification-rules-jvm)))

;; ;; Core JVM rules, for symbolic execution, etc.
;; (defun jvm-rules-jvm ()
;;   (declare (xargs :guard t))
;;   (append (jvm-semantics-rules)
;;           (jvm-simplification-rules)))

;; todo: get rid of this?
;; many of these are list rules
(defun jvm-rules-unfiled-misc ()
  (declare (xargs :guard t))
  (append (update-nth2-rules) ;since below we have rules to introduce update-nth2
          '(equal-nil-of-myif
            logext-of-0 ;move to logext-rules?
;basic rules:
            if-of-if-t-nil
;    possible-exception-of-nil
;    len-of-update-nth-rewrite-2

            update-nth-becomes-update-nth2
            ;; update-nth-becomes-update-nth2-extend
            ;; update-nth-becomes-update-nth2-extend-gen
            update-nth-becomes-update-nth2-extend-new

            true-listp-of-cons

            true-listp-of-take
            nth-of-take-2
            ;; nth-of-bvchop-becomes-nth2 ;yuck?
            ;; nth-of-bvxor-becomes-nth2 ;yuck?
            ;; nth-of-slice-becomes-nth2 ;yuck?
;    true-listp-of-logext-list
;    logext-list-equal-nil-rewrite2
;    logext-list-equal-nil-rewrite

;    iushr-constant-opener
            usbp8-implies-sbp32-2 ;fixme do we still need this?
            integerp-of-nth-when-all-integerp
;    logext-identity;;this caused problems.  trying without.
            sbp-32-when-non-neg ;do we need still this?
            nth-of-subrange
            one-plus-len-hack
            <-of-+-of-1-same
            <-of-+-of-1-same-alt)))

;move?
;; TODO: Add more
(defun map-rules ()
  (declare (xargs :guard t))
  '(not-equal-of-nil-and-s))

;deprecate
(defun jvm-rules ()
  (declare (xargs :guard t))
  (append (map-rules)
          (jvm-semantics-rules)
          (jvm-simplification-rules)
          (jvm-rules-list)
          (jvm-rules-alist)
          (list-rules) ;drop?
          (bv-array-rules)
          (jvm-rules-unfiled-misc)))

;; ;drop
;; (defun yet-more-rules-jvm ()
;;   (declare (xargs :guard t))
;;   '(not-equal-of-nil-and-s
;;     ;;s-not-equal-nil-when-v-not-nil
;;     ;; len-of-g-of-g-contents-when-array-refp
;;     ;; g-of-set-fields-irrel
;;     ;; g-of-g-of-set-field-when-pairs-different
;; ;    g-of-initialize-2d-array
;; ;    g-of-g-contents-of-initialize-2d-array-sub-array
;;     ;; jvm::g-of-initialize-one-dim-array-irrel ;drop?
;;     ;; jvm::g-of-initialize-one-dim-array            ;drop?
;;     ;; g-of-g-of-set-field-same
;; ; g-of-g-contents-of-initialize-2d-array-same
;;     ;; g-of-set-field-irrel
;;     ;;trying without these guys - does this leave the heap as a myif nest?
;;     ))

;; todo: rename
(defun amazing-rules-spec-and-dag ()
  (declare (xargs :guard t))
  (append (amazing-rules-bv)
          (bvchop-list-rules)
          (lookup-rules) ;Sat Dec 25 23:52:09 2010
          (list-rules)
          (logext-rules) ;move to parent?
          (jvm-rules-list)
          (jvm-rules-alist)
          (jvm-rules-unfiled-misc)
          (more-rules-yuck)
          '(getbit-list-of-bv-array-write-too-high
            map-packbv-constant-opener)))

;todo: separate out jvm?
;this includes the jvm rules:
;used by many axe examples
(defun amazing-rules ()
  (declare (xargs :guard t))
  (append (amazing-rules-spec-and-dag)
          (map-rules)
          (jvm-semantics-rules)
          (jvm-simplification-rules)
          (run-until-return-from-stack-height-rules-smart) ;drop? but this is needed for some things in examples/axe
          ))

;more generally, these are for extracting (or setting?) any state component?
;should include nth of myif?
(defund get-local-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append (base-rules)
           (boolean-rules) ;needed? Sun May  3 16:25:13 2020
           (type-rules)
           (core-rules-bv)
           (core-rules-non-bv)
           (list-rules) ;drop?
           (bvchop-list-rules)
           (bvif-rules)
           (unsigned-byte-p-rules)
           (logext-rules)
           (jvm-simplification-rules)
           (jvm-rules-list)
           (jvm-rules-alist)
           (bv-array-rules)
           (jvm-rules-unfiled-misc)
;           (bitxor-rules)
;           (bit-blast-rules3) ;bozo
           (more-rules-yuck)
           (trim-rules)
           (trim-helper-rules)
           (list-to-bv-array-rules)
           (map-rules)
           (yet-more-rules-non-jvm)
           (more-rules-bv-misc)
           ;;(amazing-rules) ;this seemed slow - BBOZO why?? lots of bvchop 7 of larger values?
           '(nth-of-myif ;Sun Feb 27 01:58:14 2011
             update-local-in-state    ;new only for the lifter?
             set-field-in-state       ;new
;             set-pc                ;new
             append-associative ;new
             getbit-list-of-bv-array-write-too-high
             getbit-list-of-bv-array-write-too-high
             thread-top-frame-of-myif
             heap-of-myif

             update-nth-of-cons
             myif-of-cons-and-cons ;drop?

             set-field-of-set-field-reorder
             ;; bv-array-read-of-logext-list-better

             getbit-of-bvand-eric

             ;; bv-array-write-of-logext-list-better
             ;; bound-hack-yuck
             ;; myif-intervening-and-negated-hack
             ;; myif-comparison-hack
             ))
   '(slice-trim-dag-all                      ;new
     ;;array-reduction-when-all-same-improved2 ;looped?
     update-nth-becomes-update-nth2
     )))

;i guess we don't want the trim rules here...
;deprecate! only used in this file.  just inline this
(defun arbit-loop-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append (base-rules)
           (boolean-rules) ;trying
           (type-rules)
           (core-rules-bv)
           (core-rules-non-bv)
           (list-rules) ;drop?
           (bvchop-list-rules)
           (bvif-rules)
           (unsigned-byte-p-rules)
           (logext-rules)
           (jvm-semantics-rules)
           (jvm-simplification-rules)
           (jvm-rules-list)
           (jvm-rules-alist)
           (bv-array-rules)
           (jvm-rules-unfiled-misc)
;           (bitxor-rules)
;           (bit-blast-rules3) ;bozo
           (more-rules-yuck)
           (trim-rules)
           (trim-helper-rules)
           (list-to-bv-array-rules) ;needed?
           (map-rules)
           (yet-more-rules-non-jvm)
           (more-rules-bv-misc)
           ;;(amazing-rules) ;this seemed slow - BBOZO why?? lots of bvchop 7 of larger values?
           '(;fixme what other of the amazing rules do we need?
             <-of-+-cancel-1-2 ;just added -where else is this needed?  what else do we need here?
             getbit-list-of-bv-array-write-too-high
             update-nth-of-cons
             myif-of-cons-and-cons ;drop?
             set-field-of-set-field-reorder
             ;; bv-array-read-of-logext-list-better
             getbit-of-bvand-eric
             ;; bv-array-write-of-logext-list-better
             ;; bound-hack-yuck
             ;; myif-intervening-and-negated-hack
             ;; myif-comparison-hack
             unicity-of-0
             fix-of-len
             integerp-when-signed-byte-p))
   '(slice-trim-dag-all                      ;new
     ;;array-reduction-when-all-same-improved2 ;looped?
     update-nth-becomes-update-nth2)))

;; ;separate out
;; (defun more-type-rules ()
;;   (declare (xargs :guard t))
;;   '(acl2-numberp-of-len
;;     jvm::acl2-numberp-of-call-stack-size
;;     len-equal-impossible
;;     ))

(defun first-loop-top-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append (amazing-rules-spec-and-dag)
           (map-rules)
           (jvm-semantics-rules)
           (jvm-simplification-rules)
           ;;(run-until-return-from-stack-height-rules-smart) ;drop?
           ;;(dag-val-rules) ;where else should we use this?
           '(nth-of-myif ;sun feb 27 02:08:36 2011 (to simplify expressions for locals - the if goes away)
             equal-of-nil-of-s-and-s
;             jvm::initialize-2d-array ;sun jun  6 21:04:46 2010
             equal-when-bound-dag
             acl2-numberp-of-len
             jvm::acl2-numberp-of-call-stack-size
             equal-constant-+-alt
             booleanp-of-memberp ;add
;             get-pc-designator-from-state
;             get-pc-designator-from-frame
             set::insert-delete-cancel
             update-nth-of-cons
             update-nth-of-0 ;not sure i want this...
             unicity-of-0
             fix-of-len
;             call-stack-of-make-state-of-thread-table
;                           update-nth ;fixme might loop
             getbit-of-bvand
             set-field-of-set-field-reorder
             set-fields-opener
             set-fields-base-case
             jvm::initialize-one-dim-array ;todo: should we open this or not?
             binary-append-opener          ;restrict to constants?
             not-null-refp-when-addressp-free
             ))
   '(update-nth-becomes-update-nth2-extend-new
     ;;array-reduction-when-all-same-improved2               ;looped?
     update-nth-becomes-update-nth2
     )))

;try using this instead of first-loop-top-rules (and kill that one)
(defun first-loop-top-rules-invariant-rules ()
  (declare (xargs :guard t))
  (append (first-loop-top-rules)
          '(;; booland-commute-constant
            jvm::equal-of-push-frame-and-push-frame ;why?
            jvm::equal-of-make-frame-and-make-frame ;why?
            equal-cons-cases2 ;drop?  was for locals?
            equal-of-cons-alt
            len-equal-impossible
            integerp-implies-acl2-numberp
            )))

;; ;add to arbit-loop-rules and just use that?
;; (defun invariant-rules ()
;;   (declare (xargs :guard t))
;;   (append (arbit-loop-rules)
;;           '(;set-pc ;can we drop some rules?
;;             heap
;;             jvm::jvm-statep-of-make-state
;;             jvm::make-state-equal-rewrite-2
;;             bind-equal-same-rewrite2
;; ;            alist-of-thread-table-of-one-loop-iteration
;;             IDENTITY
;;             )))

;fixme get rid of this?
;todo: this contains some duplicates (other rule lists in this file may too)
(defun rule-list-1001 ()
  (declare (xargs :guard t))
  (append (lookup-rules) ;new!
          (arbit-loop-rules)
          ;(run-until-return-from-stack-height-rules-smart) ;drop?
          (first-loop-top-rules-invariant-rules)                   ;fixme
          (address-rules)
          '(sbvlt-of-bvplus-of-1-when-sbvlt-rev
            acl2-numberp-of-logext ;new
            turn-equal-around-axe4 ;new wed jun 23 22:14:18 2010
;            len-when-pop-known ;hack
 ;           consp-when-pop-known ;hack
;            consp-of-push        ;hack
;            get-pc
            signed-byte-p-of-logext
;            set-pc ;can we drop some rules?
            jvm::jvm-statep-of-make-state
            jvm::make-state-equal-rewrite-2
            bind-equal-same-rewrite2
;            alist-of-thread-table-of-one-loop-iteration
            )))

;fixme build this from smaller lists of rules?
;GETBIT-OF-BVXOR-ERIC ;seemed to be bad for dag prover Tue Jan 12 06:24:08 2010
(defun axe-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append '(mod-of-0-arg1

             equal-of-map-reverse-list-and-map-reverse-list ;Tue Feb  8 15:08:06 2011

             ;; logext can still appear (if arraycopy is called):
             logext-when-usb-cheap
             logext-identity-when-usb-smaller-dag

             all-unsigned-byte-p-of-take-of-subrange ;Fri Dec 17 03:22:09 2010
             all-true-listp-of-map-unpackbv
             items-have-len-of-map-unpackbv
             map-packbv-of-map-unpackbv
             group-of-ungroup-same
             all-true-listp-of-map-reverse-list
             items-have-len-of-map-reverse-list
             all-unsigned-byte-p-of-reverse-list
             all-all-unsigned-byte-p-of-map-reverse-list

             equal-of-map-packbv-and-map-packbv

             bvlt-transitive-3-a
             bvlt-transitive-3-b
             bvlt-transitive-4-a
             bvlt-transitive-4-b
             bvlt-transitive-5-a
             bvlt-transitive-5-b

             equal-of-bvchop-extend-when-bvlt     ;new
             bvplus-of-bvuminus-of-bvcat-of-slice32 ;new
             bvplus-of-bvuminus-of-bvcat-of-slice   ;new
             bvlt-of-floor-arg3
             bvlt-of-floor-arg2
             bvchop-numeric-bound ;applied for even non-constant widths Fri Sep  3 10:19:33 2010
             equal-of-nth2-and-bv-array-read ;Tue Aug 31 03:44:49 2010 drop?
             equal-of-nth2-and-bv-array-read-alt ;Tue Aug 31 03:44:49 2010 drop?
             unsigned-byte-p-of-nth2 ;Tue Aug 31 03:44:58 2010 drop?
             sbvrem-when-positive-work-hard ;added work-hard Sat Dec 18 23:31:50 2010 ;was just in axe-prover-rules ;Fri Aug 13 00:51:36 2010
             equal-of-0-and-sbvrem-when-small
             unsigned-byte-p-of-*-of-constant ;Mon Jul 19 16:25:03 2010
             equal-of-0-and-+-of-minus-2 ;gen the 0?!
             boolor-of-bvlt-of-constant-and-bvlt-of-constant-3-disjuncts ;fffixme add the rest of these
             boolor-of-bvlt-of-constant-and-bvlt-of-constant
             boolor-lemma-sha-1
             unsigned-byte-p-of-minus
             bv-array-read-when-index-is-len

             leftrotate-32-of-myif-arg2
             bvnot-of-myif

             bvlt-of-myif-arg3
             bvlt-of-myif-arg2
             bvcat-of-myif-arg2
             bvcat-of-myif-arg4

             bvcat-of-constant-when-equal-of-constant-and-bvchop
             equal-of-bvchop-and-bvplus-of-same
             equal-of-bvchop-and-bvplus-of-same-alt
             <-of-+-of-minus-and-constant
             <-of-+-of-minus-and-constant-alt
             append-of-nil-arg2 ;move?
             bvlt-unique
;equal-of-constant-and-getbit-extend ;loops with BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE?
             unsigned-byte-p-of-1-when-not-nil
             nth-when-all-same-cheap
             equal-of-nil-and-map-packbv
             bv-array-read-of-append
             bv-array-read-of-map-packbv
             bvcat-of-slice-when-slice-known
             nth-becomes-bv-array-read-strong2
             nth-of-bv-when-all-same
             unsigned-byte-p-of-+-of-minus-better
             bv-array-write-shorten-constant-data
             EQUAL-OF-CONSTANT-AND-BVXOR-OF-CONSTANT
             bvlt-6-4
             equal-of-0-and-bvxor
             bvlt-of-bvuminus-same
             bvplus-of-same
             bvlt-of-bvmult-of-constant-and-constant
             ASSOCIATIVITY-OF-+
             bvcat-of-slice-extend-constant-region
             ;len-of-FINALCDR
             ;group-of-FINALCDR
             bvcat-when-unsigned-byte-p
             unsigned-byte-p-of-2-when-bvlt
             nth-of-myif-limited ;Mon May 10 02:08:59 2010 trying this since i needed nth of myif to make two nodes in the miter agree? - maybe we should always blast a multiple-value expression?
             equal-0-getbit-when-bvlt
             equal-of-0-and-slice-extend
             nthcdr-of-firstn-same
             bvlt-6-1
             equal-of-0-and-getbit-when-bvlt-hack
;             slice-when-not-bvlt-hack ;kill
             drop->-hyps
             <-of-+-of-minus
             <-of-+-of-minus-alt
             equal-of-+-of-minus-alt
             equal-of-+-of-minus
             <-of-+-of-minus-32
             <-of-+-of-minus-alt-32
             equal-of-+-of-minus-alt-32
             equal-of-+-of-minus-32

             bvcat-when-top-bit-0-2
             bvcat-when-top-bit-0
             unsigned-byte-p-of-0-arg1
             nth-of-nil
             equal-of-nil-when-equal-of-len
             move-minus-hack
             move-minus-hack2
             firstn-of-+-of-minus
             firstn-of-+-of-minus-2
             unsigned-byte-p-tighten-when-slice-is-0
             unsigned-byte-p-false-when-not-longer
             equal-of-0-and-bvchop-6
             bvlt-of-64
             unsigned-byte-p-of-+-of-minus2
             sbvlt-of-+-arg1
             sbvlt-of-+-arg2
             bvplus-of-unary-minus-arg2
             all-all-unsigned-byte-p-of-append
             all-all-unsigned-byte-p-of-cons
             items-have-len-of-cons
             items-have-len-of-append
             firstn-of-nil
             all-all-unsigned-byte-p-of-nil
;             equal-of-0-and-len-when-true-listp ;loops with equal-of-nil-when-true-listp ;fri may 21 01:25:02 2010
             bvlt-of-33554432 ;todo: gross
             unsigned-byte-p-shrink
             times-of-64-becomes-bvmult
             subrange-of-cons-constant-version
             bv-arrayp ;think about this...
             bv-array-clear-of-bv-array-write-both
             <-of-constant-when-natp-2
             unsigned-byte-p-when-bvlt
             bvcat-when-highsize-is-not-posp
             bvcat-when-lowsize-is-not-posp
             fold-consts-in-*
             booland-of-bvlt-of-constant-and-bvle-of-constant
             sbvlt-of-bvplus-of-bvuminus-tighten-31-32
             sbvlt-of-negative-constant-when-unsigned-byte-p-2
             <-of-constant-when-usb
             my-integerp-<-non-integerp
             my-non-integerp-<-integerp
             booland-combine-adjacent-bvles
             booland-combine-adjacent-bvles-alt
             boolif-of-not-same-arg2 ;moved from axe-prover-rules
             boolif-of-not-same-arg3 ;moved from axe-prover-rules

             sbvlt-of-bvplus-of-constant-and-constant
             nth-when-equal-of-take-hack
             prefixp-same
             prefixp-of-cdr-rule
             bvchop-when-must-be-1
             bvplus-subst-value
             bvplus-subst-value-alt
             subrange-of-bv-array-write-irrel ;drop?
;subrange-of-bv-array-write-in-range
             subrange-of-bv-array-write

             cdr-of-subrange
             bv-array-clear-range-of-bv-array-write-both
             cdr-of-bv-array-clear
             nth-of-bv-array-clear-both
             sbvlt-of-constant-when-<-of-constant
             bvlt-of-constant-when-<-of-constant
             sbvlt-of-bvplus-32 ;yuck?
             bvchop-identity-when-<
             bv-array-clear-range-of-1-and-cons-of-0
             bv-array-read-of-append-of-cons
             bv-array-clear-range-of-append-one-more
             append-of-constant-and-cons-of-constant
             bv-array-clear-range-of-cons
             bv-array-clear-range-of-append-of-cons
             bv-array-clear-range-of-cons-of-cons
             bv-array-clear-range-of-bv-array-write-too-high

             bv-array-clear-length-1-of-list-zero ;Wed Apr 14 00:23:10 2010
             bvchop-identity-cheap ;moved from prover rules
             bvplus-of-bvcat-and-bvuminus-of-bvcat ;Tue Apr 13 16:17:40 2010
             bvminus-of-constant-and-bvplus-of-constant ;Sun Apr 11 17:17:35 2010
             true-listp-of-add-to-end
             len-of-add-to-end ;fixme just expand add-to-end ?
             ;append-of-final-cdr-arg1
             prefixp-of-true-list-fix-arg2
             prefixp-of-true-list-fix-arg1
             prefixp-of-add-to-end
             prefixp-of-nil-arg2
             prefixp-of-nil-arg1
             equal-of-+-of-minus-same
             equal-of-fix-same ;reorder?
             <-of-256

             <-becomes-bvlt-dag-alt-gen-better ;these are from md5
             equal-of-bvplus-cancel-2-of-more-and-1-of-more
             equal-of-bvplus-cancel-3-of-more-and-1-of-more
;              bound-when-usb2
;              myif-of-bvif-becomes-bvif-arg2
;             myif-of-bvif-becomes-bvif-arg1
;            myif-of-bvcat-becomes-bvif-arg1
;           myif-of-bvcat-becomes-bvif-arg2
;             getbit-of-bvplus-split ;bad? introduces ifs sat dec 25 23:51:03 2010

             sbvlt-becomes-bvlt-cheap
             sbvlt-becomes-bvlt-cheap-1
             sbvlt-becomes-bvlt-cheap-2
             equal-of-bvplus-cancel-arg1 ;was just in prover-rules
             firstn-of-0
             bv-array-clear-of-cons
             bv-array-read-of-cons-both
             equal-of-myif-and-bvif-same
             equal-of-myif-and-bvif-same-alt
             bvplus-of-bvplus-of-bvuminus-of-bvcat ;new without this there was a problem
             boolor-of-equal-and-not-of-equal-constants
             boolor-of-equal-and-not-of-equal-constants-alt
             booland-of-booland-of-boolif
             not-equal-constant-when-unsigned-byte-p-bind-free-dag ;was just in prover-rules ;Wed Mar 17 04:03:01 2010
             sha1-context-hack ;Wed Mar 17 03:54:02 2010 (how much does this help?)
             boolor-of-booland-same-2 ;Wed Mar 17 03:06:45 2010
             bvlt-of-constant-when-unsigned-byte-p-tighter
             equal-of-repeat-and-bv-array-write-hack-alt
             equal-of-repeat-and-bv-array-write-hack

             all-unsigned-byte-p-of-append ;fri mar 12 03:05:08 2010

             booleanp-of-prefixp
             equal-of-constant-and-bv-array-write
             equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus-alt
             equal-of-bv-array-write-of-bvplus-and-repeat-of-bvplus
             all-unsigned-byte-p-of-repeat ;are these needed?

             ;;these are for the rolled proof:
             <-of-len-and-constant
             <-becomes-bvlt-dag-alt-gen-better2
             <-becomes-bvlt-dag-gen-better2

             bvplus-of-bvuminus-of-bvcat-and-bvcat

             unsigned-byte-p-of-smaller
             bvxor-cancel-2-of-more-and-1-of-more
             bitxor-when-equal-of-constant-and-bvchop-arg1
             bitxor-when-equal-of-constant-and-bvchop-arg2
             <-cancel-only-and-2-of-more ;fixme also add comm of plus?
             getbit-when-equal-of-constant-and-bvchop
             equal-of-constant-when-not-bvlt-constant-1
             equal-of-constant-when-not-bvlt-constant-2
             equal-of-constant-when-bvlt-constant-1
             equal-of-constant-when-bvlt-constant-2

             bv-array-read-of-unary-minus-32-2 ;new
             bvuminus-of-myif-arg2
             equal-of-firstn-and-firstn-same
             true-listp-of-firstn ;wasn't already included?!
             bvchop-0-hack
             slice-of-bvif-safe
             equal-of-constant-and-slice-when-bvlt
             equal-of-constant-and-slice-when-equal-of-constant-and-slice
             equal-of-constant-and-slice-when-equal-of-constant-and-bvchop ;may help a lot?  more like this?

             bvlt-of-constant-and-slice
             bvif-of-equal-of-bvchop-same
             equal-of-0-and-slice-when-bvlt
             equal-of-0-and-slice-when-bvlt2
;             unsigned-byte-p-of-+-of-minus ;thu apr 29 05:44:14 2010
;            unsigned-byte-p-of-+-of-minus-alt ;thu apr 29 05:44:17 2010
             bvxor-subst-arg2
             bvxor-subst-arg3

             bvlt-of-bvchop-arg3
             bvlt-of-bvchop-arg2

             bvcat-subst-constant-arg2
             bvcat-subst-constant-arg4

             firstn-of-firstn ;make a safe non-splitting version?
             bvlt-of-2147483583
             nthcdr-of-bv-array-write-is-nil
             slice-of-floor-of-expt-constant-version
             consp-becomes-<-of-len
             getbit-when-slice-is-known-constant
             bitxor-of-minus
             floor-of-*-of-8-and-32
             consp-of-ungroup

             equal-of-constant-and-+-of-minus-and-bv
             group-of-cons
             <-of-non-integerp-and-integerp
             bvlt-of-bitxor-of-1-same
             bvlt-of-bitxor-of-1-same-two

             <-of-constant-and-+-of-bv-and-minus-and-bv
             <-of-+-of-minus-becomes-bvlt
             unsigned-byte-p-of-slice-one-more
             equal-of-plus-minus-move
             equal-of-0-and-+-of-minus ;these should have similar names
             myfirst-of-myif-arg2
             map-packbv-of-myif-arg3
             group-of-myif-arg2
             booland-of-not-of-equal-and-equal-constants
             booland-of-not-of-equal-and-equal-constants-alt


             equal-of-bitxor-and-bitxor-same-6
             bvplus-of-bvcat-constants
             slice-when-bvchop-known-2

             consp-of-group
             ;;BV-ARRAY-READ-OF-BV-ARRAY-WRITE-DIFF-SAFE-fixme ;make it not true?! huh?
             bv-array-clear-range-of-bv-array-write-contained
             sbvlt-of-constant-and-bvplus-of-constant ;yuck?
             equal-of-bvplus-of-bvchop-and-bvplus-same
             boolor-of-not-and-booland-same-1
             unsigned-byte-p-of-bvuminus-bigger
             <-of-len-and-expt-of-2-constant-version
             collect-constants-<-/     ;can introduce fractions...
             collect-constants-<-/-two ;can introduce fractions...
             <-of-floor-constant-when-not-integerp
             move-minus-to-constant
             <-of-minus1-and-floor

             equal-of-*-of-1/4-and-slice-of-2
             <-of-0-and-*
             bvchop-of-1/4
             equal-of-0-and-*-of-constant
             *-of-1/4-and-bvcat-of-0
             *-of-1/16-and-bvcat-of-0
             integerp-of-*-of-1/4 ;gen!

             ;;sha1-spec-case-rules:
             equal-of-0-and-bvmult-of-expt-constant-version
             bvmult-tighten-6-8-2
             bvuminus-of-*
             equal-of-bvmult-of-expt-constant-version
             acl2-numberp-of-mod
             integerp-of-mod
             bvchop-shift-gen-constant-version

             bvlt-of-*-arg3

             bvlt-add-to-both-sides-constant-lemma ;expensive?

             ;rationalp-when-integerp ;drop
             rational-of-floor
             rationalp-*2
             integerp-of-floor
;             bvuminus-of-bvuminus
             consp-of-repeat ;move

             boolor-hack-sha1
             booland-of-not-of-boolor
             bvlt-add-to-both-sides-constant-lemma-alt-dag
             bvlt-of-bvuminus-and-constant
             boolor-of-booland-of-not-same-2

             booland-of-boolor-and-not-same-5
             booland-of-boolor-and-not-same-5-alt
             booland-of-boolor-and-not-same-3
             booland-of-boolor-and-not-same-4
             bvlt-of-bvuminus-5-4
             rationalp-of-ceiling
             integerp-of-ceiling
             bvlt-of-bvuminus-arg2-constant
;    <-becomes-bvlt-dag-both
             <-0-+-negative-2
;    +-of-myif-arg1 ;new5
;   +-of-myif-arg2 ;new5
             repeat-of-myif-arg1
             take-of-nil
             integerp-of-+-when-integerp-1
;    unary---of-bvif ;new5
             nfix
             *-of-1/32-and-bvcat-of-0
;    bvlt-of-bvif-arg3 ;bad?
;    bvlt-of-bvif-arg2 ;bad?

             booland-of-not-same2
;    equal-of-bvif ;trying without..
             plus-of-minus-one-and-bv-dag
             <-of-+-arg1-when-negative-constant
             ; <-of-+-arg2-when-negative-constant ;uncomment?
;bvuminus-when-smaller-bind-free
;    bvuminus-when-smaller-bind-free-dag
             commutativity-2-of-+-when-constant
             rationalp-of--
             rationalp-of-+
             bvlt-of-1
             max
             len-of-nthcdr ;move
             bvchop-of-times-of-/-32
             equal-of-bvplus-constant-and-constant
             integerp-of-1-times-1/32
             commutativity-of-*-when-constant
             bvmult-32
             <-of-bvcat-alt
             +-of-bvplus
             take-of-repeat
             rationalp-of-myif
             rationalp-of-len
             booleanp-of-rationalp
             len-of-group
             floor-of-16-when-usb-31
             *-becomes-bvmult-axe
;ceiling-in-terms-of-floor

             floor-of-32-when-usb
             list-fix-of-append
             bvlt-of-constant-when-usb-dag
             minus-becomes-bv-2
;commutativity-2-of-+

             nthcdr-of-repeat
             functional-self-inversion-of-minus
             distributivity-of-minus-over-+

;    <-becomes-bvlt-dag-alt-gen ;Wed Feb 24 15:00:10 2010
             +-combine-constants
             <-of-negative-constant-and-unary-minus
             move-negative-addend-1
             unicity-of-0
             collect-constants-over-<
             natp

             rationalp-when-bv-operator
             acl2-numberp-when-bv-operator

             +-becomes-bvplus-hack-gen
;group-of-append-new ;too aggressive? ;Fri May 21 07:20:55 2010
             append-associative ;move

;(bit-blast-rules-basic) ;new! we only want these when mitering?
             unsigned-byte-p-of-+-of-constant-strong
             nth-of-repeat
             +-of-minus-1-and-bv2-alt-bind-free
             <-of-constant-and-+-of-bv-and-minus
             <-of-constant-and-+-of-minus-and-bv

             nth-of-plus-of-bv-and-minus
             nth-of-plus-of-bv-and-minus-alt
             repeat-of-plus-of-bv-and-minus
             repeat-of-plus-of-bv-and-minus-alt

;;;FLOOR-OF-MINUS-ARG1 ;scary
;;;FLOOR-OF-sum ;scary

             equal-of-booleans-axe ;EQUAL-OF-BOOLEANS-SPLIT
             getbit-of-myif

             true-listp-of-ungroup
             bvplus-of-bvuminus-of-slice-and-bvcat-of-slice

             equal-of-+-and-bv
             equal-of-0-and-floor
             equal-of-getbit-and-bitxor-same
             equal-of-getbit-and-bitxor-same-alt
             equal-of-floor-of-expt-and-bv-constant-version-dag
             <-of-diff-of-bv-and-constant
             <-of-constant-when-<=-of-free
             bvxor-cancel-lemma1-bvchop-version-alt3
             bvxor-cancel-lemma1-bvchop-version-alt2
             floor-bound-lemma3
             equal-of-bvplus-cancel-arg2-alt ;more?
             equal-of-constant-and-bvif-of-constant-and-constant

             ;;                                      <-of-constant-and-+-of-minus
             ;;                                      <-of-*-of-floor-and-same
             ;;                                      +-of-bvplus-of-1-and-unary-minus-same
             ;;                                      +-of-bvplus-of-2-and-unary-minus-same

             +-of-minus-bind-free-constant-version ;more like this?!
             unsigned-byte-p-of-floor-of-expt-constant-version
             bvplus-of-floor-4-32
             bvplus-of-floor-4-32-alt
             bvmult-of-expt2-constant-version
             equal-constant-+-alt

             ;;new (try with the back?!):
             ;;                                      bvand-of-bvxor-of-ones-same
             ;;                                      bvand-of-bvxor-of-ones-same-alt
             ;;                                      bvand-of-bvand-of-bvxor-of-ones-same
             ;;                                      bvand-of-bvand-of-bvxor-of-ones-same-alt
             ;;                                      BITXOR-COMMUTATIVE-2-INCREASING-DAG
             ;;                                      BITXOR-COMMUTATIVE-INCREASING-DAG

             ;;                                      EQUAL-OF-CONSTANT-AND-BVXOR-OF-CONSTANT
             ;;                                      bvnot-becomes-bvxor
             ;;                                      BVCAT-EQUAL-REWRITE ;wait, why didn't this fire when the slow dag is rewritten?
             ;;                                      BVCAT-EQUAL-REWRITE-ALT


             ;;                                      BVXOR-COMMUTATIVE-DAG
             ;;                                      BVXOR-COMMUTATIVE-2-DAG
             ;;                                      ;BVXOR-ASSOCIATIVE
             ;;                                      SLICE-OF-BVXOR
             ;;                                      EQUAL-OF-BITXOR-SAME
             ;;                                      EQUAL-OF-BITXOR-SAME-alt
             ;;                                      TURN-EQUAL-AROUND-AXE4
             ;;                                      equal-of-getbit-and-bitxor-same
             ;;                                      equal-of-getbit-and-bitxor-same-alt
             ;;                                      equal-of-getbit-and-bitxor-same-alt2
             ;;                                      equal-of-getbit-and-bitxor-same-alt3
             ;; ;                         BOOLAND-ASSOCIATIVE
             ;;                                      equal-of-bitxor-and-bitxor-same
             ;;                                      equal-of-bitxor-and-bitxor-same-2
             ;;                                      equal-of-bitxor-and-bitxor-same-3
             ;;                                      equal-of-bitxor-and-bitxor-same-4
             ;;                                      equal-of-bitxor-and-bitxor-same-5
             ;;                                      equal-of-bitxor-and-bitxor-same-6
             ;;                                      equal-of-bvxor-and-bvxor-same-7
             ;;                                      equal-of-bvxor-and-bvxor-same-8
             ;;                                      BVCAT-EQUAL-REWRITE
             ;;                                      GETBIT-OF-LEFTROTATE32-HIGH
             ;;                                      BVMULT-OF-EXPT2-constant-version
             ;;end of new stuff

             equal-of-nth-and-bv-array-read-better
             equal-of-nth-and-bv-array-read-alt-better

             boolor-adjacent-ranges-sha1-hack ;fragile! ;maybe not needed?

             equal-of-bitxor-and-bitxor-same
             getbit-of-bvmult-of-expt-constant-version
             equal-of-myif-same-1
             equal-of-myif-same-2
             bvif-of-myif-1
             bvif-of-myif-2
             bvplus-of-plus-arg3
             bvplus-of-plus-arg2
             slice-of-+ ;ffixme complete set..
             bv-array-read-of-+
             <-of-+-of-minus-and-bv
             equal-of-+-of-minus-and-bv
             nth-of-bv-array-write-becomes-bv-array-read-strong
             sha1-hack-four-million-six
             equal-of-0-and-bvplus-of-bvuminus-alt
             equal-of-0-and-bvplus-of-bvuminus
             sha1-hack-four-million-four
;                                bvplus-of-bvplus-constants-size-differs-better-no-split-case2 ;wed feb 24 14:58:25 2010
             acl2-numberp-of-myif
             boolif-of-booland-same
             boolif-of-boolor-same
             sha1-hack-four-million-five-alt
             sha1-hack-four-million-five


             sha1-hack-four-million-one
             sha1-hack-four-million-three
             boolif-of-not
             sha1-hack-four-million
             ;;bvchop-of-nth-becomes-bv-array-read2
             nth-becomes-bv-array-read-strong ;why doesn't this fire?
;bvif-of-nth-arg3
;bvif-of-nth-arg4
             bvplus-of-myif-arg3
             bvplus-of-myif-arg2
;BOOLOR-ASSOCIATIVE ;new - do we have dag versions of the comm rules? - was this slow?!
;bvcat-of-nth-arg2
;bvcat-of-nth-arg4
;bvxor-of-nth-arg2
;bvxor-of-nth-arg3
;bitxor-of-nth-arg1
;bitxor-of-nth-arg2
;slice-of-nth-becomes-bv-array-read ;i have high hopes for this. yeeg.
             boolif-of-booland-of-boolor
             boolif-of-boolor-of-boolor
             bvif-of-+-arg3
             bvif-of-+-arg4
             bvif-of-minus-arg3
             bvif-of-minus-arg4
             slice-of-myif
             bvlt-of-huge-when-slice-not-max
             bvchop-of-minus-becomes-bvuminus
             items-have-len-of-nil
             items-have-len-of-myif
             bvlt-when-slice-known-hack
             equal-of-slice-and-slice-when
             equal-of-slice-and-slice-when-alt
             slice-monotone-strong-30-6-bv
             equal-of-subrange-and-subrange-same-lsts-and-ends
             sha1-hack-three-million
             sha1-hack-two-million
             sha1-hack-two-million-alt
             bvchop-subst-constant

             equal-of-packbv-and-packbv
             bvlt-of-bvplus-of-bvcat-of-slice
             unsigned-byte-p-of-myif-strong ;expensive..
             bvlt-of-bvmult-of-expt-arg2-constant-version2

             acl2-numberp-of-floor
             integerp-of-myif-strong
             bvchop-of-minus-trim
             sha1-hack-a-million
             subrange-of-take
             nthcdr-of-subrange
             subrange-of-group
             equal-of-group-and-group
             subrange-when-end-is-negative

             consp-of-subrange
             getbit-of-leftrotate32-high
;fffixme do these contradict what simplifying bitxors does?
             ;;BITXOR-COMMUTATIVE-dag
             ;; BITXOR-COMMUTATIVE-2-dag

             bvxor-of-bvcat     ;dangerous?
             bvxor-of-bvcat-alt ;dangerous?

             slice-of-leftrotate32-high
             bvxor-cancel-lemma1-bvchop-version
             bvxor-cancel-lemma1-bvchop-version-alt


;             bvcat-of-slice-and-bvcat-of-getbit
             bvcat-of-slice-of-bv-array-read-and-bvcat-of-getbit-of-bv-array-read
             equal-of-bvxor-and-bvxor-arg1-arg2
             slice-of-bvxor ;needed due to an issue with bv-array-reads being trimmed
             bvxor-cancel-lemma1-alt
             bvxor-cancel-lemma1

             equal-of-0-when-bvlt
             trim-of-0-arg1
             bvmult-of-power-of-2-subst-9-8
             equal-of-slice-and-constant-when-equal-of-bvchop-and-constant2
             all-unsigned-byte-p-of-subrange
             bvmult-subst2-alt-constant-version
             bvmult-subst2-constant-version

             nth-of-unpackbv ;or should we unroll unpackbv?
             nth-of-ungroup-gen
             map-packbv-of-group-of-ungroup-of-map-unpackbv ;Sat Feb  5 13:02:18 2011
            ;drop?:
             map-packbv-of-map-ungroup-of-map-map-unpackbv ;Thu Feb  3 14:20:47 2011
             ;group-of-map-unpackbv ;Tue Feb  8 15:05:59 2011 yuck?!
             packbv-base ;drop?
             packbv-opener ;drop? would need trim of packbv and getbit of packbv ;add syntaxp hyp..
             bvchop-of-packbv
             all-unsigned-byte-p-of-map-packbv
             unsigned-byte-p-of-packbv-gen

;                                    bitlist-to-bv2-rewrite
             bv-array-read-when-equal-of-firstn-and-constant
             bv-array-read-when-equal-of-take-and-constant

;                                    UNSIGNED-BYTE-P-OF-BITLIST-TO-BV2
             nthcdr-of-ungroup
             bvplus-of-bvuminus-of-bvcat-of-0
;bool-to-bit ;was expensive
             bvcat-of-slice-onto-constant
             getbit-when-not-bvlt-constant

             bvxor-cancel-cross-1
             bvxor-cancel-cross-2
             bvxor-cancel
             bvxor-cancel-alt

             bvplus-cancel-cross
             bvplus-cancel-cross2
             unsigned-byte-p-of-nth

             <-of-constant-and-unary-minus
             bvplus-and-bvcat-hack ;caused problems?
             <-of-minus-and-constant
             <-of-negative-constant-and-bv
;bvchop-of-nth-becomes-bv-array-read
             bvlt-of-one-less-than-max-25
             all-true-listp-of-nthcdr
             all-all-unsigned-byte-p-of-nthcdr
             all-unsigned-byte-p-of-nthcdr
             equal-of-0-and-getbit-of-bvplus
;                                GETBIT-OF-BVPLUS-SPLIT ;trying this - bad!
             items-have-len-of-nthcdr
             bvplus-of-bvcat-constants-hack
             bvlt-of-bvcat-arg2
             bvmult-of-4-gen

             nth-of-group
             bvmult-of-bvcat-hack100


             bvplus-of-bvuminus-of-bvcat-same
             items-have-len-of-group-strong
             bvdiv-of-64
;             sbvlt-becomes-bvlt-better

             group2-in-terms-of-group
             equal-of-group-and-group2-alt
             equal-of-group-and-group2
;                                    ceiling-in-terms-of-floor2 ;introduces /
;                                    group-of-map-byte-to-bit-list
             one-fourth-hack

             bound-when-low-bits-0
             bound-when-low-bits-0-alt
             bvcat-equal-rewrite-alt
             bvlt-of-bvplus-constant-and-constant-other
             len-of-ungroup ;what else is missing?
;                                    len-of-map-map-byte-to-bit-list
;                                    true-lisp-of-map-ungroup
;                                    len-of-map-ungroup
             equal-of-group2-and-group2
             ;group2-of-ungroup ;thu feb  3 17:20:24 2011
             ;group-of-ungroup ;Thu Feb  3 17:20:58 2011
;                                    TAKE-OF-MAP-BYTE-TO-BIT-LIST
;                                    LEN-OF-MAP-BYTE-TO-BIT-LIST
             bvmult-becomes-bvcat-31-64
;                                    group2-of-MAP-BYTE-TO-BIT-LIST
             bytes-to-bits-rewrite
             ;LEN-OF-BYTES-TO-BITS

             take-of-ungroup
             firstn-of-ungroup
             ceiling-of-bvcat-hack

             bvlt-when-bvchop-known-subst
             bvlt-when-bvchop-known-subst-alt
             bvlt-of-bvmult-9-8-400
;                                     slice-of-bvplus-cases-no-split-no-carry2 ;seems expensive...
             bvcat-of-bvmult-hack-another
             bvchop-of-floor-of-expt-of-2-constant-version
             unsigned-byte-p-of-bvmult-29-30-16
             equal-constant-when-bvchop-equal-constant-false

             sha1-hack-123434
             equal-of-bvplus-and-bvplus-cancel-arg1-arg1 ;more like this?!

             equal-of-bvnot-and-bvnot
             bvmult-of-bvcat-hack4
             bvmult-of-bvcat-hack3
             bvmult-of-bvcat-hack2
             take-of-group2
             floor-when-usb-bind-free-dag-constant-version
             take-of-bytes-to-bits
;GROUP-BECOMES-GROUP2 ;put this back?
             bvmult-of-bvcat-hack
             take-of-group
             firstn-of-group

             bvplus-of-slice-and-bvuminus-of-bvmult
             all-all-unsigned-byte-p-of-group
             true-listp-of-group
             all-true-listp-of-group
             booleanp-of-all-all-unsigned-byte-p

             majority-idiom1
             majority-idiom2
             majority-idiom3
             majority-idiom4
             majority-idiom5
             majority-idiom6
             majority-idiom7
             majority-idiom8

             bvand-of-bvnot-same
             bvand-of-bvnot-same-alt
             bvand-of-bvand-of-bvnot-same
             bvand-of-bvand-of-bvnot-same-alt

             bvand-associative
             bvand-commutative-2-dag

             bvor-associative
             bvor-commutative-2-dag
             bvor-commutative-dag

             equal-of-bvor-and-bvxor
             equal-of-bvor-and-bvxor-alt
             equal-of-bvxor-and-bvor
             equal-of-bvxor-and-bvor-alt

             plus-of-minus-becomes-bv-dag
             plus-of-minus-becomes-bv-dag-alt

             bvlt-of-slice-29-30-2
             slice-when-not-bvlt-gen
             bvlt-of-slice
             all-all-unsigned-byte-p-of-group2-rewrite
             bvplus-tighten-free-1
             bvplus-tighten-free-2
             bvlt-of-bvplus-when-bvlt-of-slices
             ;;             BVPLUS-OF-BVPLUS-COMBINE-CONSTANTS-WHEN-NOT-OVERFLOW ;Fri Mar 26 17:45:00 2010
             bvlt-of-slice-and-slice2-back

             bvlt-of-bvplus-constant-when-not-bvlt-of-bvplus-constant
;BOOLAND-COMMUTATIVE-2 ;looped? should never be used in the dag world?
;booland-commutative ;looped? should never be used in the dag world?
             booland-associative
             equal-of-0-when-bvlt-of-slice
             floor-becomes-slice-when-unsigned-byte-p
;             bvlt-tighten-free-alt ;problems? ;tue aug 31 19:45:37 2010
;             bvlt-tighten-free ;problems? ;tue aug 31 19:45:37 2010
             minus-becomes-bv
             true-listp-of-bv-array-clear-range
             all-unsigned-byte-p-of-bv-array-clear-range
             len-of-bv-array-clear-range
             bv-array-read-of-bv-array-clear-range-contained
             bv-array-read-of-bv-array-clear-range-high
             bv-array-read-of-bv-array-clear-range-low
             bv-array-clear-of-bv-array-clear-range-contained
             bv-array-clear-whole-range
             bv-array-clear-of-bv-array-clear-adjacent1
             bv-array-clear-of-bv-array-clear-adjacent2
             bv-array-clear-of-bv-array-clear-range-adjacent1
             bv-array-clear-of-bv-array-clear-range-adjacent2
             bv-array-clear-range-of-bv-array-clear-adjacent1
             bv-array-clear-range-of-bv-array-clear-adjacent2
             bv-array-clear-range-of-bv-array-clear-range-adjacent1
             bv-array-clear-range-of-bv-array-clear-range-adjacent2
             bv-array-clear-of-bv-array-write-better
;bv-array-clear-of-bv-array-write
             bvlt-of-bvplus-of-bvuminus-other-alt ;new
             all-true-listp-of-group2
             items-have-len-of-group2
             bvplus-of-bvuminus-trim
             <-becomes-bvlt-free ;ffixme put in the complete theory of this stuff?
             <-becomes-bvlt-free-alt
             <-of-constant-and-floor
             bvmult-of-slice-when-bvchop-0
             bvcat-equal-bvcat
             true-listp-of-nthcdr-2
             bvlt-of-slice-and-slice2
             bv-array-read-of-bv-array-clear
             all-unsigned-byte-p-of-bv-array-clear-gen
             len-of-bv-array-clear
             true-listp-of-bv-array-clear
             bv-array-read-of-take-better ;added -better fri dec 24 17:14:32 2010

             bvmult-of-bvcat
             bv-array-write-equal-rewrite
             bv-array-write-equal-rewrite-alt
             bv-array-write-of-bv-array-write-tighten-len
             min
             unsigned-byte-p-from-bound-constant-version-axe
             acl2-numberp-of-len
             ;; jvm::acl2-numberp-of-call-stack-size ;trying
             equal-of-append
             bvmult-tighten-dag-power-of-2
             bvplus-tighten-better
             bvmult-tighten-dag ;can we do better for a power of 2?? ffixme
             true-listp-of-group2
             bvmult-of-bvplus-hack-gen-constant-version
             equal-of-bvmult-of-slice
;                                <-becomes-bvlt-dag-alt-gen ;wed feb 24 15:00:22 2010
             <-of-floor-of-constant-and-constant-gen

             all-unsigned-byte-p-of-myif-strong
             all-unsigned-byte-p-of-take
             all-unsigned-byte-p-of-firstn   ;just in case

             floor-of-floor
             <-of-0-and-floor

             plus-becomes-bvplus-arg2-free-dag ;other ones?
             plus-becomes-bvplus-arg1-free-dag ;other ones?
;bvmult-of-slice-when-bvchop-0 ;where did this rule go? ffixme
             bvlt-of-bvmult-hack200
             nth-of-group2-gen
             nth-of-group2 ;drop?
             <-+-negative-0-2

             len-of-group2
             slice-subst-constant
             slice-subst-constant-alt
             bvplus-tighten-hack100
             bvmult-tighten-hack
             bvmult-of-bvplus-hack4
             bvmult-of-bvplus-hack3

;;dup             *-BECOMES-BVMULT-axe
             slice-tighten-top-free
             bvmult-of-bvplus-hack2
             bvmult-of-slice-tighten
             plus-becomes-bvplus-dag
             bvmult-of-bvplus-hack
             bvmult-of-bvmult-hack
             <-lemma-for-known-operators2
             <-lemma-for-known-operators3
             nthcdr-of-nthcdr

             cdr-of-group2
             cdr-of-group
             +-becomes-bvplus-when-bv-dag
             natp-of-*
             *-of-1/64-when-multiple
             integerp-of-*-of-1/64

             <-of-slice-and-constant-when-not-positive
             floor-of-64-when-usb-64
             floor-of-64-when-usb-31
             natp-of-floor
             nthcdr-of-group2
             nthcdr-of-group

             <-of-0-and-len-when-consp ;hope this is okay..
             all-true-listp-of-cdr
             all-all-unsigned-byte-p-of-cdr
             all-unsigned-byte-p-when-all-all-unsigned-byte-p
             true-listp-of-nth-when-all-true-listp
             len-nth-from-items-have-len
             equal-of-bvplus-and-bvplus-cancel-gen-alt
             equal-of-bvplus-and-bvplus-cancel-gen
             unsigned-byte-p-of-bvplus-tighten
             bvlt-tighten-arg1
;bvlt-tighten-arg2 ;wed feb 24 01:14:46 2010
             acl2-numberp-when-unsigned-byte-p
             bvlt-of-plus-arg1
             bvlt-of-plus-arg2

             <-of-negative-when-usbp
             nth-of-nthcdr
             bvlt-of-bvplus-1-cancel-alt
             consp-of-nthcdr
             posp
;             natp ;loops with natp-means-non-neg
;natp-when-integerp

             cdr-of-nthcdr
             collect-constants-over-<-2

             equal-of-cons
;             bv-array-write-with-index-and-len-same ;mon jul 19 21:06:14 2010
;             bvxor-associative ;i can't believe this was missing!
;             bvxor-commutative-dag
;           bvxor-commutative-2-dag
             bv-array-read-trim-index
             bvlt-transitive-free2-back-constants
             bvlt-of-bvplus-constant-and-constant
             bvlt-of-bvplus-same-alt
;                                <-of-bvplus-becomes-bvlt-arg1 ;wed feb 24 14:59:16 2010
;                                <-of-bvplus-becomes-bvlt-arg2 ;wed feb 24 14:59:16 2010
             nth-becomes-bv-array-read2
;             bvlt-transitive-free-back ;other rules like this?
             nth-of-take-gen
             nth-of-firstn ;move to list-rules?
             bvlt-when-not-bvlt
             bvlt-when-unsigned-byte-p
;                        <-of-bvplus-same-gen
;nth-of-take ;seemed expensive (why suddenly?)

             <-becomes-bvlt
             <-becomes-bvlt-alt
             equal-of-cons-and-cons-same-arg2
             subrange-same
             cons-equal-no-split
             +-of-minus1-and-bvplus-of-1
             take-of-bv-array-write-irrel
             equal-of-bvplus-constant-and-constant-alt
             nthcdr-of-take-becomes-subrange
             <-of-bvplus-same-32-1
             integerp-when-unsigned-byte-p-free
             equal-of-append-arg1
             +-of-minus-constant-version
             bvlt-when-not-bvlt-one-more
             ;;bvchop-identity ;fri jan 15 22:52:27 2010

             slice-of-bvplus-cases-no-split-case-no-carry-constant-version
             plus-of-minus-of-slice-and-bvmult-of-slice
             plus-of-slice-and-minus-of-bvmult-of-slice
             bvmult-of-16-becomes-bvcat
             bvlt-of-bvmult-of-slice-and-slice

             items-have-len-of-group

             ;;                              ;i think maybe we don't want to open all this stuff until we have to?:
             ;;                              sha1-loop-11-unrollsha1-loop-11-base-case
             ;;                              sha1-loop-12-unrollsha1-loop-12-base-case
             ;;                              sha1-loop-13-unrollsha1-loop-13-base-case
             ;;                              sha1-loop-14-unrollsha1-loop-14-base-case
             ;;                              sha1-loop-15-unrollsha1-loop-15-base-case
             ;;                              sha1-inner-loop-base
             ;;                              sha1-inner-loop-unroll
             ;;                              prepare-message-schedule
             ;;                              prepare-message-schedule-aux-base
             ;;                              prepare-message-schedule-aux-unroll
             )
           (amazing-rules-spec-and-dag)
           (map-rules)
           (miter-rules) ;todo
           (introduce-bv-array-rules) ;do we still want these?

           ;;new, since these will be pulled out:
           (strip-cadrs (map-runes 'map-packbv))
           (strip-cadrs (map-runes 'map-unpackbv))
           (strip-cadrs (map-runes 'map-map-unpackbv))
           (strip-cadrs (map-runes 'map-ungroup)))
   '(sbvlt-becomes-bvlt-better ;fri mar 26 08:12:17 2010 ;delete this from above
     myif-of-bvif-becomes-bvif-arg2 ;thu mar 25 12:59:18 2010 (4)
     myif-of-bvif-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg1
     myif-of-bvcat-becomes-bvif-arg2
     bound-when-usb2 ;thu mar 25 05:33:45 2010

     myif-of-bv-array-write-arg1-safe ;may have caused big problems
     myif-of-bv-array-write-arg2-safe ;may have caused big problems

     bvplus-when-<=-15-hack-for-sha1
     <-of-myif-arg2 ;wed feb  3 23:56:47 2010
;bv-array-read-shorten-data ;sat jan 16 02:37:49 2010
     firstn-becomes-take-gen  ;take caused problems ;revisit this?
     unsigned-byte-p-of-myif      ;thu jan 14 21:26:14 2010
     getbit-of-bvxor              ;tue jan 12 05:56:17 2010
     ;; nth-of-bvchop-becomes-nth2  ;yuck?
     ;; nth-of-bvxor-becomes-nth2
     ;; nth-of-slice-becomes-nth2

     bvlt-of-bvif-arg2
     bvlt-of-bvif-arg3
     bvplus-commutative-2-sizes-differ ;after including dag prover rules
     bvplus-commutative-dag    ;after including dag prover rules
     bvplus-commutative-2-dag  ;after including dag prover rules
;     bvxor-all-ones            ;why? ;trying without
     )))

;These should only be tried if the usual rules don't apply (constants are rare):
(table axe-rule-priorities-table 'jvm::pc-opener 1)
(table axe-rule-priorities-table 'jvm::locals-opener 1)
(table axe-rule-priorities-table 'jvm::stack-opener 1)
(table axe-rule-priorities-table 'jvm::method-designator-opener 1)

;; (defun program-equivalence-rules ()
;;   (declare (xargs :guard t))
;;   (append '(jvm::reduce-make-state-equality-when-all-but-thread-tables-match
;;             jvm::equal-of-push-frame-and-push-frame
;;             jvm::equal-of-make-frame-and-make-frame
;;             jvm::push-operand-equal-rewrite
;;             jvm::bind-equal-rewrite)
;;           (map-rules)
;;           (amazing-rules-bv)
;;           (bvchop-list-rules)))

;these wrap up rotates first..
(defun phase-1-rules ()
  (declare (xargs :guard t))
  (set-difference-equal (append '( ;bvshl ;this makes things much bigger
                                  )
                                (amazing-rules-spec-and-dag)
                                (map-rules)
                                (jvm-semantics-rules)
                                (jvm-simplification-rules)
                                (run-until-return-from-stack-height-rules-smart))
                        '(                ;;BVOR-WITH-SMALL-ARG2
                          getbit-of-bvxor ;new
                          bvplus-commutative-dag
                          bvplus-commutative-2-dag
                          bvplus-associative
                          bvuminus-of-bvplus ;can mess up the concat as shift and plus pattern
                          bvshr-rewrite-for-constant-shift-amount ;important for rotates?  could keep this but add rotate intro rules with slice instead of bvshr
                          bvshl-rewrite-with-bvchop-for-constant-shift-amount
                          bvashr-rewrite-for-constant-shift-amount
                          )))

;; ;wrap up rotates first..
;; ;todo: compare to phased-bv-axe-rule-sets
;; (defun phased-axe-rule-sets-for-symbolic-execution (state)
;;   (declare (xargs :stobjs state
;;                   :verify-guards nil))
;;   (list (make-axe-rules (phase-1-rules)
;;                      state)
;;         (make-axe-rules (set-difference-equal (append '( ;bvshl ;this makes things much bigger
;;                                                      )
;;                                                    (amazing-rules))
;;                                            '( ;BVOR-WITH-SMALL-ARG2
;;                                              ;;GETBIT-OF-BVXOR
;;                                              ;;BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
;;                                              ;;BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT
;;                                              ))
;;                         state)))

(defun phased-rule-alists-for-symbolic-execution (state)
  (declare (xargs :stobjs state
                  :guard (ilks-plist-worldp (w state))))
  (list (make-rule-alist! (phase-1-rules)
                         (w state))
        (make-rule-alist! (set-difference-equal (append '( ;bvshl ;this makes things much bigger
                                                         )
                                                       (amazing-rules-spec-and-dag)
                                                       (map-rules)
                                                       (jvm-semantics-rules)
                                                       (jvm-simplification-rules)
                                                       (run-until-return-from-stack-height-rules-smart))
                                               '( ;BVOR-WITH-SMALL-ARG2
                                                 ;;GETBIT-OF-BVXOR
                                                 ;;BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
                                                 ;;BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT
                                                 ))
                         (w state))))

;;
;; priorities
;;

;this one is going to fire a lot when we walk down a big heap with get-field-of-set-field
(table axe-rule-priorities-table 'equal-nth-new-ad-rewrite -10)
(table axe-rule-priorities-table 'get-field-of-set-field-diff-1 -10)

;try the opener(s) before the base rule:
;try the myif rules first...
(table axe-rule-priorities-table 'run-until-return-from-stack-height-of-myif-axe-split-1 -13)
(table axe-rule-priorities-table 'run-until-return-from-stack-height-of-myif-axe-split-2 -13)
(table axe-rule-priorities-table 'run-until-return-from-stack-height-of-myif-axe -12)
;(table axe-rule-priorities-table 'run-until-return-from-stack-height-of-myif-axe-alt -12)
;(table axe-rule-priorities-table 'run-until-return-from-stack-height-opener-fast-print -11)
(table axe-rule-priorities-table 'run-until-return-from-stack-height-opener-fast-axe -10)
(table axe-rule-priorities-table 'run-until-return-from-stack-height-opener-axe -10)
(table axe-rule-priorities-table 'run-until-return-from-stack-height-base-axe -9)

(table axe-rule-priorities-table 'jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame -13)
(table axe-rule-priorities-table 'jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame -12)
(table axe-rule-priorities-table 'jvm::call-stack-size-of-push-frame-of-push-frame -11)
(table axe-rule-priorities-table 'jvm::call-stack-size-of-push-frame -10)
