; Lists of rule names (JVM-related)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

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

    equal-of-nth-new-ad-and-myif-of-nth-new-ad-arg3
    equal-of-nth-new-ad-and-myif-of-nth-new-ad-arg3-alt
    equal-of-nth-new-ad-and-myif-of-nth-new-ad-arg2
    equal-of-nth-new-ad-and-myif-of-nth-new-ad-arg2-alt))

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

;; mostly for debugging?
;; todo: add a smart version of this
(defun symbolic-execution-rules-for-run-n-steps ()
  (declare (xargs :guard t))
  '(run-n-steps-opener-axe
    run-n-steps-zp
    run-n-steps-of-myif-split ;todo: do something smarter? (more like what the non-step-limited execution does?)
    ))

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
    run-until-return-from-stack-height-base-axe
    ;; Stuff to get rid of step around exception states:
    step-state-with-pc-and-call-stack-height-of-obtain-and-throw-exception
    <-of-constant-and-call-stack-size-when-negative
    posp-of-+-of-constant
    integerp-of-call-stack-size
    inverse-of-+
    distributivity-of-minus-over-+
    associativity-of-+
    +-commutative-2-axe
    +-commutative-axe
    +-combine-constants))

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
    jvm::method-designator-constant-opener
    jvm::exception-handler-targets-constant-opener))

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
            set::emptyp-constant-opener ;needed for address calcs
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
            jvm::make-array-type-base jvm::make-array-type-unroll      ;dangerous??
            acl2::array-contents ;; we enable this to expose get-field

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
            jvm::resolve-class-base-1 jvm::resolve-class-base-2 jvm::resolve-class-unroll
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
            popn-frames-opener
            popn-frames-of-0

            ;; rules about operand-stack-size:
            jvm::operand-stack-size-of-empty-operand-stack
            jvm::operand-stack-size-of-push-operand
            jvm::operand-stack-size-of-pop-operand
            jvm::operand-stack-size-of-push-long
            jvm::operand-stack-size-of-pop-long
            jvm::operand-stack-size-of-nil
            jvm::operand-stack-size-bound ;rename

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

            eql ; replaces eql with equal
            eq ; replaces eq with equal

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
            ;;jvm::classp
            jvm::is-a-classp
            jvm::is-an-interfacep
            jvm::make-one-dim-array-type
            ;; jvm::array-classp
;jvm::non-array-classp
            jvm::class-implements-interfacep
            jvm::get-superinterfaces-aux-base
            jvm::get-superinterfaces-aux-opener
            jvm::get-superinterfaces
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
            logext-identity-when-usb-smaller-axe

            jvm::op-code

            jvm::call-stack

            ;; call-stack-of-make-state-of-thread-table

            first-non-member-when-member ;new
            first-non-member-when-memberp
            first-non-member-when-not-memberp

            alistp-of-bind

;    jvm::encode-unsigned ;;is a macro!
            <-of-+-cancel-2-1

            s-same-s
            s-diff-s-axe
;    null-ref
            equal-of-nil-and-null-ref
            equal-of-null-ref-and-nil

;    atom ;fri dec 24 16:38:27 2010
            jvm::initialize-static-fields-unroll ;todo: what if we don't do this?  can we handle this with rules?
            jvm::initialize-static-fields-base
            default-value
;    strip-cars-opener
            strip-cars-of-non-consp
            ;bvand-of-logext
            ;bvand-of-logext-alt

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
            jvm::get-superclasses ;class-decl-superclasses ;should we add this to eval-fn?
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
            <-of-+-cancel-2-2

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

            ;;    not-<-of-0-when-natp ;loops with defn natp - limit somehow? ;thu may 17 00:02:17 2012

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
            jvm::reference-typep-base jvm::reference-typep-unroll
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
            not-equal-nil-when-equal-of-len-arg1
            not-equal-nil-when-equal-of-len-arg2
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

;; ;deprecate
;; (defun jvm-rules ()
;;   (declare (xargs :guard t))
;;   (append (map-rules)
;;           (jvm-semantics-rules)
;;           (jvm-simplification-rules)
;;           (list-rules3)
;;           (alist-rules)
;;           (list-rules) ;drop?
;;           (bv-array-rules)
;;           (jvm-rules-unfiled-misc)))

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

;todo: separate out jvm?
;this includes the jvm rules:
;used by many axe examples.  try using amazing-rules-spec-and-dag instead, for miter proofs.
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
           (list-rules3)
           (alist-rules)
           (bv-array-rules)
           (update-nth2-rules) ;since below we have rules to introduce update-nth2
           (update-nth2-intro-rules)
           (update-nth-rules)
           (jvm-rules-unfiled-misc)
;           (bitxor-rules)
;           (bit-blast-rules) ;bozo
           (more-rules-yuck)
           (trim-rules)
           (trim-helper-rules)
           (list-to-bv-array-rules)
           (map-rules)
           (yet-more-rules-non-jvm)
           (array-reduction-rules)
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
   '(slice-trim-axe-all                      ;new
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
           (list-rules3)
           (alist-rules)
           (bv-array-rules)
           (update-nth2-rules) ;since below we have rules to introduce update-nth2
           (update-nth2-intro-rules)
           (update-nth-rules)
           (jvm-rules-unfiled-misc)
;           (bitxor-rules)
;           (bit-blast-rules) ;bozo
           (more-rules-yuck)
           (trim-rules)
           (trim-helper-rules)
           (list-to-bv-array-rules) ;needed?
           (map-rules)
           (yet-more-rules-non-jvm)
           (array-reduction-rules)
           (more-rules-bv-misc)
           ;;(amazing-rules) ;this seemed slow - BBOZO why?? lots of bvchop 7 of larger values?
           '(;fixme what other of the amazing rules do we need?
             ;<-of-+-cancel-1-2 ;just added -where else is this needed?  what else do we need here?
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
             fix-when-acl2-numberp
             acl2-numberp-of-len
             ;fix-of-len
             integerp-when-signed-byte-p))
   '(slice-trim-axe-all                      ;new
     update-nth-becomes-update-nth2)))

(defun first-loop-top-rules ()
  (declare (xargs :guard t))
  (set-difference-equal
   (append (amazing-rules-spec-and-dag) ; this may have list rules we don't need
           (map-rules)
           (jvm-semantics-rules)
           (jvm-simplification-rules)
           ;;(run-until-return-from-stack-height-rules-smart) ;drop?
           ;;(dag-val-rules) ;where else should we use this?
           '(nth-of-myif ;sun feb 27 02:08:36 2011 (to simplify expressions for locals - the if goes away)
             equal-of-nil-of-s-and-s
;             jvm::initialize-2d-array ;sun jun  6 21:04:46 2010
             not-equal-when-bound
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
             fix-when-acl2-numberp
             acl2-numberp-of-len
             ;fix-of-len
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
   '(update-nth-becomes-append ; drop?
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
            acl2-numberp-when-integerp
            )))

;; todo: get rid of this? used in lifter.
;todo: this contains some duplicates (other rule lists in this file may too)
;; todo: better name
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

(defun sbvlt-of-bvif-rules ()
  (declare (xargs :guard t))
  '(sbvlt-of-bvif-when-sbvlt-arg3
    sbvlt-of-bvif-when-sbvlt-arg4
    sbvlt-of-bvif-when-not-sbvlt-arg3
    sbvlt-of-bvif-when-not-sbvlt-arg4
    sbvlt-of-bvif-when-sbvlt-arg3-alt
    sbvlt-of-bvif-when-sbvlt-arg4-alt
    sbvlt-of-bvif-when-not-sbvlt-arg3-alt
    sbvlt-of-bvif-when-not-sbvlt-arg4-alt))

;; Used during lifting and after
(defun formal-unit-testing-extra-simplification-rules ()
  (declare (xargs :guard t))
  (append (sbvlt-of-bvif-rules)
          '(bv-array-read-of-bv-array-write
            ;;todo: when prove-with-tactics sees a not applied to a boolor, it should try to prove both cases
            ;;boolor  ;might have a loop
            equal-of-bvif
            equal-of-bvif-alt
            bvplus-of-bvif-arg2 ;perhaps restrict to the case when the duplicated term is a constant
            bvplus-of-bvif-arg3 ;perhaps restrict to the case when the duplicated term is a constant
            sbvlt-of-myif-arg2-safe
            sbvlt-of-myif-arg3-safe
            integerp-when-unsigned-byte-p-free ;needed for update-nth reasoning for object arrays (but we may change that)
            <-of-constant-when-usb ;needed for update-nth reasoning for object arrays (but we may change that)
            max                    ;used in object array reasoning
            SBVLT-OF-+-ARG2        ;used in object array reasoning
            ;;SBVLT-OF-+-ARG3
            <-OF-+-COMBINE-CONSTANTS-1 ;used in object array reasoning
            not-<-when-sbvlt-alt       ;used in object array reasoning
            <-OF-BVCHOP-ARG1 ; since BV-ARRAY-READ-OF-BV-ARRAY-WRITE introduces <
            bvlt-of-bvif-arg2
            bvlt-of-bvif-arg3
            equal-of-myif-arg1-safe
            equal-of-myif-arg2-safe
            bv-array-read-of-bvif-arg2
            bvmult-of-bvif-arg3
            bvshl-of-bvif-arg3
            bv-array-read-of-bv-array-write-diff ;can help when the indices are not constant but are provably unequal (might be ITEs)

            ;;todo: move these next few to core-rules-bv:
            equal-of-bvchop-and-bvplus-of-same
            equal-of-bvchop-and-bvplus-of-same-alt
            sbvlt-of-bvplus-of-constant-and-constant-2
            signed-addition-overflowsp
            signed-addition-underflowsp
            <-of-bvplus-becomes-bvlt-arg1 ;the < may come from array rules (todo: avoid even introducing it?)

            ;; move these?:
            sbvlt-when-sbvlt-of-bvplus-of-constant
            sbvlt-when-sbvlt-of-bvminus-of-constant
            sbvlt-of-bvplus-of-constant-and-constant-2
            sbvlt-of-bvplus-of-constant-and-constant-2b
            bvlt-of-bvdiv-constants
            sbvlt-of-0-and-sbvdiv
            sbvlt-false-when-sbvlt-gen ; move to more basic rule set (but this is in a big expensive file that we may not want to depend on)
            )
          (amazing-rules-spec-and-dag)))

;;only used just below?
(defun formal-unit-testing-extra-simplification-rules-no-boolif ()
  (declare (xargs :guard t))
  (set-difference-eq
   (formal-unit-testing-extra-simplification-rules)
   ;; since pruning doesn't know about booland/boolor/etc:
   '(MYIF-BECOMES-BOOLIF-T-ARG1 ;rename
     ;;MYIF-BECOMES-BOOLIF-T-ARG2
     ;;MYIF-BECOMES-BOOLIF-NIL-ARG1
     MYIF-BECOMES-BOOLIF-NIL-ARG2 ;rename
     ;;MYIF-BECOMES-BOOLIF-AXE
     )))

(defun formal-unit-tester-extra-lifting-rules ()
  (declare (xargs :guard t))
  (append '(;addressp-when-address-or-nullp-and-not-null-refp ;loops with address-or-nullp
            equal-of-addressfix-same
            jvm::execute-model-static-boolean-method
            boolif booland ; why?
            )
          (formal-unit-testing-extra-simplification-rules-no-boolif)))

;These should only be tried if the usual rules don't apply (constants are rare):
(set-axe-rule-priority jvm::pc-opener 1)
(set-axe-rule-priority jvm::locals-opener 1)
(set-axe-rule-priority jvm::stack-opener 1)
(set-axe-rule-priority jvm::method-designator-opener 1)

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
;todo: add jvm to the name
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
                          bvplus-commutative-axe
                          bvplus-commutative-2-axe
                          bvplus-associative
                          bvuminus-of-bvplus ;can mess up the concat as shift and plus pattern
                          bvshr-rewrite-for-constant-shift-amount ;important for rotates?  could keep this but add rotate intro rules with slice instead of bvshr
                          bvshl-rewrite-with-bvchop-for-constant-shift-amount
                          bvashr-rewrite-for-constant-shift-amount
                          )))

;; ;todo: compare to phased-bv-axe-rule-sets
;; note that this builds in the "smart" symbolic execution rules.
(defun phased-rule-alists-for-symbolic-execution (state)
  (declare (xargs :stobjs state))
  (list (make-rule-alist! (phase-1-rules)
                          (w state))
        ;; here's what gets turned on here (BVPLUS-COMMUTATIVE-AXE BVPLUS-COMMUTATIVE-2-AXE BVPLUS-ASSOCIATIVE BVUMINUS-OF-BVPLUS GETBIT-OF-BVXOR BVSHL-REWRITE-WITH-BVCHOP-FOR-CONSTANT-SHIFT-AMOUNT BVSHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT BVASHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT):
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
(set-axe-rule-priority equal-nth-new-ad-rewrite -10)
(set-axe-rule-priority get-field-of-set-field-diff-1 -10)

;try the opener(s) before the base rule:
;try the myif rules first...
(set-axe-rule-priority run-until-return-from-stack-height-of-myif-axe-split-1 -13)
(set-axe-rule-priority run-until-return-from-stack-height-of-myif-axe-split-2 -13)
(set-axe-rule-priority run-until-return-from-stack-height-of-myif-axe -12)
;(set-axe-rule-priority run-until-return-from-stack-height-of-myif-axe-alt -12)
;(set-axe-rule-priority run-until-return-from-stack-height-opener-fast-print -11)
(set-axe-rule-priority run-until-return-from-stack-height-opener-fast-axe -10)
(set-axe-rule-priority run-until-return-from-stack-height-opener-axe -10)
(set-axe-rule-priority run-until-return-from-stack-height-base-axe -9)

(set-axe-rule-priority jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame -13)
(set-axe-rule-priority jvm::call-stack-size-of-push-frame-of-push-frame-of-push-frame -12)
(set-axe-rule-priority jvm::call-stack-size-of-push-frame-of-push-frame -11)
(set-axe-rule-priority jvm::call-stack-size-of-push-frame -10)
