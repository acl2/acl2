; Axe rules about the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These rules call the axe-syntax functions.

(include-book "kestrel/jvm/jvm-rules" :dir :system)
(include-book "kestrel/jvm/symbolic-execution" :dir :system)
(include-book "kestrel/jvm/execution" :dir :system)
(include-book "kestrel/jvm/int-subtypes" :dir :system)
(local (include-book "kestrel/jvm/jvm-facts" :dir :system))
(include-book "axe-syntax-functions-jvm") ;for get-stack-height-and-pc-to-step-from-myif-nest
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "kestrel/axe/bv-list-rules-axe" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

;; Declare some JVM-related functions to be known-booleans:
(add-known-boolean set::in)
(add-known-boolean array-refp)
(add-known-boolean array-ref-listp)
(add-known-boolean jvm::string-has-been-internedp)
(add-known-boolean jvm::intern-table-okp)
(add-known-boolean addressp)
(add-known-boolean address-or-nullp)
(add-known-boolean null-refp)
(add-known-boolean jvm::bound-in-class-tablep)
(add-known-boolean java-booleanp)
(add-known-boolean java-bytep)
(add-known-boolean java-shortp)
(add-known-boolean java-charp)
(add-known-boolean java-intp)
(add-known-boolean java-longp)
(add-known-boolean java-boolean-as-int-p)
(add-known-boolean java-byte-as-int-p)
(add-known-boolean java-short-as-int-p)
(add-known-boolean java-char-as-int-p)
(add-known-boolean jvm::java-floatp)
(add-known-boolean jvm::java-doublep)
(add-known-boolean jvm::heapp)
(add-known-boolean jvm::intern-tablep)
(add-known-boolean jvm::jvm-statep)
(add-known-boolean jvm::type-implementsp)

;TODO: Add 'axe' to the names of these rules

;breaks the abstraction. may be needed for axe, where operand-stack-size doesn't get executed
;todo: just use a constant opener?
(defthm jvm::operand-stack-size-of-nil
  (equal (jvm::operand-stack-size nil)
         0))

;Not really a JVM rule.
(defthmd s-diff-s-axe
  (implies (and (axe-syntaxp (heavier-dag-term b a))
                (not (equal a b)))
           (equal (s b y (s a x r))
                  (s a x (s b y r)))))

;perhaps oddly we move the set-fields with heavier ads to the front (they will be more likely to be referenced again soon)
(defthmd set-field-of-set-field-reorder
  (implies (and (axe-syntaxp (heavier-dag-term ref2 ref1))
                (not (equal ref1 ref2)))
           (equal (set-field ref1 pair1 value1
                             (set-field ref2 pair2 value2 heap))
                  (set-field ref2 pair2 value2
                             (set-field ref1 pair1 value1 heap)))))

(defthmd set-field-of-set-field-reorder-pairs
  (implies (and (axe-syntaxp (heavier-dag-term pair2 pair1))
                (not (equal pair1 pair2)))
           (equal (set-field ref pair1 value1 (set-field ref pair2 value2 heap))
                  (set-field ref pair2 value2 (set-field ref pair1 value1 heap)))))

;; We sort first by class name
(defthm set-static-field-of-set-static-field-diff-class-axe
  (implies (and (axe-syntaxp (heavier-dag-term class-name1 class-name2))
                (not (equal class-name1 class-name2)))
           (equal (jvm::set-static-field class-name1 field-name1 value1 (jvm::set-static-field class-name2 field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name2 field-name2 value2 (jvm::set-static-field class-name1 field-name1 value1 static-field-map))))
  :hints (("Goal" :use set-static-field-of-set-static-field-diff-class
           :in-theory (disable set-static-field-of-set-static-field-diff-class))))

;; We sort second by field name (so here the class names must be the same)
(defthm set-static-field-of-set-static-field-diff-field-axe
  (implies (and (axe-syntaxp (heavier-dag-term field-name1 field-name2))
                (not (equal field-name1 field-name2)))
           (equal (jvm::set-static-field class-name field-name1 value1 (jvm::set-static-field class-name field-name2 value2 static-field-map))
                  (jvm::set-static-field class-name field-name2 value2 (jvm::set-static-field class-name field-name1 value1 static-field-map))))
  :hints (("Goal" :use set-static-field-of-set-static-field-diff-field
           :in-theory (disable set-static-field-of-set-static-field-diff-field))))

(defthm run-n-steps-opener-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array)) ;(axe-syntaxp (is-a-make-statep s dag-array))
                (not (zp n)))
           (equal (jvm::run-n-steps n s)
                  (jvm::run-n-steps (+ -1 n) (jvm::step (th) s))))
  :rule-classes nil ;; since this calls-axe-syntaxp
  :hints (("Goal" :in-theory (enable jvm::run-n-steps next))))

(defun symbolic-execution-rules-for-run-n-steps ()
  '(run-n-steps-opener-axe
    run-n-steps-zp
    run-n-steps-of-myif-split ;todo: do something smarter? (more like what the non-step-limited execution does?)
    ))

;fixme handle this!  can we keep th closed?  could just use the definition instead of this rule...
(defthmd th-rewrite
  (equal (th)
         0))

;; This can only fire on a make-state, not a myif.
(defthm run-until-return-from-stack-height-base-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (< (stack-height s) sh))
           (equal (run-until-return-from-stack-height sh s)
                  s))
  :rule-classes nil ;; since this calls axe-syntaxp
  )

;; This can only fire on a make-state, not a myif.
;; This variant directly introduces do-inst.
(defthm run-until-return-from-stack-height-opener-fast-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (<= sh (jvm::call-stack-size (jvm::call-stack (th) s))))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height
                   sh
                   (let* ((top-frame (jvm::thread-top-frame (th) s))
                          (instr (lookup (jvm::pc top-frame)
                                         (jvm::method-program (jvm::method-info top-frame)))))
                     (jvm::do-inst (car instr) instr (th) s)))))
  :rule-classes nil ;; since this calls axe-syntaxp
  :hints (("Goal"
           :use (:instance run-until-return-from-stack-height-opener-fast)
           :in-theory (e/d (stack-height jvm::step jvm::op-code th) ()))))

;; This can only fire on a make-state, not a myif.
;; This version introduces STEP, not DO-INST.
(defthm run-until-return-from-stack-height-opener-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (<= sh (stack-height s)))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height sh (jvm::step (th) s))))
  :rule-classes nil ;; since this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable run-until-return-from-stack-height-opener))))

;; (defthmd run-until-return-from-stack-height-opener-fast-print
;;   (implies (<= sh (jvm::call-stack-size (jvm::call-stack (th) s)))
;;            (equal (run-until-return-from-stack-height sh s)
;;                   (run-until-return-from-stack-height
;;                    sh
;;                    (let* ((top-frame (jvm::thread-top-frame (th) s))
;;                           (instr (lookup (jvm::pc top-frame)
;;                                          (jvm::program top-frame))))
;;                      (jvm::do-inst (car instr) (print-constant instr) ;this is what does the printing
;;                                    (th) s)))))
;;   :hints (("Goal" :use (:instance run-until-return-from-stack-height-opener-fast))))

;; The main symbolic execution rule used for handling branches during unrolling.
;; The 2 is here because we usually take a symbolic base stack, add a dummy
;; frame to catch the result, and add the frame in which execution begins.
;; TODO: Build the myif into the structure of the rule?  But then only insert the call to step-state-with-pc-and-call-stack-height on the right branch?
(defthm run-until-return-from-stack-height-of-myif-axe
  (implies (and (axe-syntaxp (is-a-myif myif-nest dag-array)) ;todo: just use SYNTACTIC-CALL-OF? ;could incorporate this check into get-stack-height-and-pc-to-step-from-myif-nest...
                (axe-bind-free (get-stack-height-and-pc-to-step-from-myif-nest myif-nest base-stack dag-array)
                               '(sh2 pc)) ;binds sh2 and pc ;bozo pass in call-stack?
;                (syntaxp (quotep pc))
;                (syntaxp (quotep sh2))
                (<= 2 sh2)
                ;;(>= (jvm::call-stack-size (jvm::call-stack (th) myif-nest) (+ 2 (jvm::call-stack-size base-stack)))) ;this implies that it's okay to step it
                )
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) myif-nest)
                  (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack))
                                                      (step-state-with-pc-and-call-stack-height pc
                                                                                                (+ sh2 (jvm::call-stack-size base-stack))
                                                                                                myif-nest))))
  :rule-classes nil ;; because this calls axe-syntaxp and axe-bind-free
  :hints (("Goal" :in-theory (e/d (step-state-with-pc-and-call-stack-height stack-height
                                                                            run-until-return-from-stack-height-opener)
                                  (jvm::step)))))

;; this version doesn't assume the presence of a dummy frame to catch the result
;; TODO: Build the myif into the structure of the rule?  But then only insert the call to step-state-with-pc-and-call-stack-height on the right branch?
(defthm run-until-return-from-stack-height-of-myif-alt-axe
  (implies (and (axe-syntaxp (is-a-myif myif-nest dag-array)) ;todo: just use SYNTACTIC-CALL-OF?
                (axe-bind-free (get-stack-height-and-pc-to-step-from-myif-nest myif-nest base-stack dag-array)
                               '(sh2 pc)) ;binds sh2 and pc ;bozo pass in call-stack?
;                (syntaxp (quotep pc))
;                (syntaxp (quotep sh2))
                (<= 1 sh2)
                ;;(>= (jvm::call-stack-size (jvm::call-stack (th) myif-nest) (+ 2 (jvm::call-stack-size base-stack)))) ;this implies that it's okay to step it
                )
           (equal (run-until-return-from-stack-height (+ 1 (jvm::call-stack-size base-stack)) myif-nest)
                  (run-until-return-from-stack-height (+ 1 (jvm::call-stack-size base-stack))
                                                      (step-state-with-pc-and-call-stack-height pc
                                                                                                (+ sh2 (jvm::call-stack-size base-stack))
                                                                                                myif-nest))))
  :rule-classes nil ;; because this calls axe-syntaxp and axe-bind-free
  :hints (("Goal" :in-theory (e/d (step-state-with-pc-and-call-stack-height stack-height
                                                                            run-until-return-from-stack-height-opener)
                                  (jvm::step)))))

;; Lift the IF where there is no more stepping to do in the then-part
;; (exception branches may remain).  For example, consider the case where the
;; then-part is finished and the else-part is stuck.
;rename
(defthm run-until-return-from-stack-height-of-myif-axe-split-1
  (implies (axe-syntaxp (no-state-to-step-p tp base-stack dag-array))
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) (myif test tp ep))
                  (myif test
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) tp)
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) ep))))
  :rule-classes nil ;; Not for use by the ACL2 rewriter.
  :hints (("Goal" :in-theory (enable myif))))

;; Lift the IF where there is no more stepping to do in the else-part
;; (exception branches may remain). For example, consider the case where the
;; else-part is finished and the then-part is stuck.
;rename
(defthm run-until-return-from-stack-height-of-myif-axe-split-2
  (implies (axe-syntaxp (no-state-to-step-p ep base-stack dag-array))
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) (myif test tp ep))
                  (myif test
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) tp)
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) ep))))
  :rule-classes nil ;; Not for use by the ACL2 rewriter.
  :hints (("Goal" :in-theory (enable myif))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-becomes-step-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))
                (equal call-stack-height
                       (jvm::call-stack-size (jvm::call-stack (th) s))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  (jvm::step (th) s)))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-1-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-2-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal call-stack-height
                            (jvm::call-stack-size (jvm::call-stack (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;todo: could restrict to BV terms
;used by Axe
;;Often used to prove that a value stored by set-field is non-nil, which tells
;;us that the corresponding heap address becomes bound by the set-field.
(defthmd not-equal-nil-when-integerp
  (implies (integerp x)
           (not (equal nil x)))
  :hints (("Goal" :in-theory (disable (:TYPE-PRESCRIPTION BVPLUS)))))

;; TODO: Make the equal a quick syntactic check?
(defthm address-or-nullp-when-addressp-free
  (implies (and (addressp free) ;poor man's backchain limit
                (equal free x))
           (address-or-nullp x)))

;; TODO: Make the equal a quick syntactic check?
(defthm not-null-refp-when-addressp-free
  (implies (and (addressp free) ;poor man's backchain limit
                (equal free x))
           (not (null-refp x))))

;; TODO: Make the equal a quick syntactic check?
;; use null-refp as the normal form
(defthm addressp-when-address-or-nullp-free
  (implies (and (address-or-nullp free) ;poor man's backchain limit
                (equal free x))
           (equal (addressp x)
                  (not (null-refp x)))))


(def-constant-opener jvm::pc)
(def-constant-opener jvm::locals)
(def-constant-opener jvm::stack)
(def-constant-opener jvm::locked-object)
(def-constant-opener jvm::method-info)
(def-constant-opener jvm::method-designator)
(def-constant-opener jvm::cur-class-name)
(def-constant-opener jvm::cur-method-name)
(def-constant-opener jvm::cur-method-descriptor)

(def-constant-opener jvm::method-program)

(def-constant-opener jvm::java-floatp)
(def-constant-opener jvm::float-signp)
(def-constant-opener jvm::make-regular-float)
(def-constant-opener jvm::float<)
(def-constant-opener jvm::float=)
(def-constant-opener jvm::regular-float-value)
(def-constant-opener jvm::fcmpl)
(def-constant-opener jvm::regular-floatp)

(def-constant-opener jvm::field-id-type)
(def-constant-opener jvm::field-publicp)
(def-constant-opener jvm::field-privatep)
(def-constant-opener jvm::field-protectedp)
(def-constant-opener jvm::field-staticp)
(def-constant-opener jvm::field-access-flags)

(def-constant-opener jvm::method-publicp)
(def-constant-opener jvm::method-privatep)
(def-constant-opener jvm::method-protectedp)
(def-constant-opener jvm::method-staticp)
(def-constant-opener jvm::method-nativep)
(def-constant-opener jvm::method-abstractp)
(def-constant-opener jvm::method-synchronizedp)
(def-constant-opener jvm::method-access-flags)

(def-constant-opener jvm::any-less-than-zero)

(def-constant-opener jvm::nth-local)
(def-constant-opener jvm::update-nth-local)
(def-constant-opener jvm::typep)
;(def-constant-opener jvm::reference-typep)
(def-constant-opener jvm::array-typep)
(def-constant-opener jvm::class-or-interface-namep)
(def-constant-opener jvm::primitive-typep)
(def-constant-opener jvm::class-namep)
(def-constant-opener jvm::field-namep)
(def-constant-opener jvm::field-idp)

(def-constant-opener jvm::lookup-method-in-class-info)

;; todo: improve def-constant-opener to handle a function and all supporters:
(def-constant-opener jvm::extract-package-name-from-class-name)
(def-constant-opener string-contains-charp)
(def-constant-opener position-equal)
(def-constant-opener position-equal-ac)
(def-constant-opener substring-before-last-occurrence)
(def-constant-opener reverse)
(def-constant-opener revappend)
(def-constant-opener substring-after-terminator)
(def-constant-opener readthroughterminator-aux)
(def-constant-opener jvm::bound-in-class-tablep)
(def-constant-opener jvm::binding)
(def-constant-opener jvm::bind)
(def-constant-opener jvm::lookup-method-in-classes)
(def-constant-opener jvm::initialize-one-dim-array)
(def-constant-opener jvm::make-frame)
(def-constant-opener jvm::count-slots-in-types)
(def-constant-opener jvm::type-slot-count)
(def-constant-opener jvm::set-static-field)
(def-constant-opener jvm::get-static-field)
(def-constant-opener set-field)
(def-constant-opener get-field)
(def-constant-opener jvm::get-array-component-type)
(def-constant-opener gen-init-bindings-for-class)

(def-constant-opener alistp)

(def-constant-opener new-ad)
(def-constant-opener new-ad-aux)
(def-constant-opener nth-new-ad)
(def-constant-opener n-new-ads2)

(def-constant-opener set::delete)
(def-constant-opener set::tail)
(def-constant-opener set::head)
(def-constant-opener set::empty)
(def-constant-opener set::sfix)
(def-constant-opener set::setp)
(def-constant-opener FAST-<<)

;fixme add type-prescription rule-classes to lots of booleanp rules?
(defthm booleanp-of-array-refp
  (booleanp (array-refp ad dims element-type heap)))

(defthm booleanp-of-array-ref-listp
  (booleanp (array-ref-listp ads dims element-type heap)))
