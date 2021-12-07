; A lifter for x86 code, based on Axe, that can handle (some) code with loops
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: First working version

;; TODO: Add ability to pass in loop invariants

;; TODO: Test handling of subroutine calls

;; TODO: Consider using PC ranges for code segment, rather than lists of offsets.

;; TODO: Remove the subroutine-length argument.

;; TODO: Maybe add back the option for non-flattened loop function params (then
;; maybe also support mentioning param names in measures).

;; TODO: Test the lifting of loops inside conditionals.

;; TODO: Remove the need to pass in the loop-alist.

;; TODO: Does it make sense to assume each loop has a single header?

;; TODO: prove type properties of loop functions in x86 lifter (essentially postludes)

;; TODO: What if the code being lifted doesn't respect normal calling conventions?

;; TODO: add an option to enforce a rewrite step limit in the lifter, for debugging?  May require a change to the rewriter.

;; TODO: Switch to using a simpler rewriter, that doesn't depend on skip-proofs

(include-book "misc/defp" :dir :system)
(include-book "kestrel/x86/tools/support-axe" :dir :system)
(include-book "kestrel/utilities/get-vars-from-term" :dir :system)
(include-book "kestrel/x86/tools/lifter-support" :dir :system)
(include-book "kestrel/x86/tools/rule-lists" :dir :system)
(include-book "kestrel/x86/tools/assumptions" :dir :system)
(include-book "kestrel/x86/tools/assumptions32" :dir :system)
(include-book "kestrel/x86/tools/assumptions64" :dir :system)
(include-book "kestrel/x86/tools/conditions" :dir :system)
(include-book "kestrel/x86/tools/read-over-write-rules" :dir :system)
(include-book "kestrel/x86/tools/write-over-write-rules" :dir :system)
(include-book "kestrel/axe/rewriter" :dir :system)
(include-book "kestrel/utilities/ints-in-range" :dir :system)
(include-book "kestrel/axe/rules-in-rule-lists" :dir :system)
;(include-book "kestrel/axe/rules2" :dir :system) ;for BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-NON-CONST
;(include-book "axe/basic-rules" :dir :kestrel-acl2)
(include-book "kestrel/bv/arith" :dir :system) ;todo
;(include-book "kestrel/arithmetic-light/mod" :dir :system)
;(include-book "kestrel/axe/rules1" :dir :system) ;for ACL2::FORCE-OF-NON-NIL, etc.
(include-book "../dags2") ; for compose-term-and-dags
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/utilities/unify" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/x86/tools/read-and-write" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)
(include-book "kestrel/utilities/subtermp" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system) ;for logext-identity
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

(local (in-theory (enable acl2::member-equal-becomes-memberp))) ;todo

;(in-theory (disable acl2::bvplus-of-minus1-tighten-32)) ;caused problems in proofs about examples

;dup
;clash
(defun acl2::my-pack-listb (item lst)
  (if (endp lst)
      nil
    (cons (acl2::pack$ item (car lst))
          (acl2::my-pack-listb item (cdr lst)))))

(defthm integerp-of-nth
  (implies (and (integer-listp lst)
                (< n (len lst))
                (natp n))
           (integerp (nth n lst)))
  :hints (("Goal" :in-theory (e/d (integer-listp (:i nth))
                                  (;acl2::nth-of-cdr
                                   )))))

;; TODO: This must exist somewhere in the model
;; The nth element of this list is register n
(defconst *register-names*
  '(rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15))

(defconst *register-numbers*
  (list *rax* *rcx* *rdx* *rbx* *rsp* *rbp* *rsi* *rdi*
        *r8*  *r9*  *r10* *r11* *r12* *r13* *r14* *r15*))

(in-theory (disable RATIONAL-LISTP)) ;slow
(in-theory (disable x86isa::INTEGERP-WHEN-CANONICAL-ADDRESS-P-CHEAP)) ;slow

(defthm mod-of-plus-reduce-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                ;; make sure k1 is not in normal form:
                (not (and (< k1 k2)
                          (<= 0 k1)))
                (integerp k1)
                (posp k2) ;gen but think about loops
                (integerp x) ;could gen but we may not have theorems about rationalp
                )
           (equal (mod (+ k1 x) k2)
                  (mod (+ (mod k1 k2) x) k2)))
  :hints (("Goal" :in-theory (enable acl2::mod-sum-cases))))


(defun untranslate-terms (terms iff-flg wrld)
  (declare (xargs :mode :program))
  (if (endp terms)
      nil
    (cons (untranslate (first terms) iff-flg wrld)
          (untranslate-terms (rest terms) iff-flg wrld))))

(defun map-all-to-val (keys val)
  (if (endp keys)
      nil
    (acons (first keys) val (map-all-to-val (rest keys) val))))

(defun my-pack-list2 (item lst)
  (if (endp lst)
      nil
      (cons (pack-in-package-of-symbol item item (car lst))
            (my-pack-list2 item (cdr lst)))))

;; This version expects RULES to evaluate to a list of symbols (names of rules).
;; This version returns a term
;; TODO: Rename
;; Returns (mv erp term state).
;why is this a macro?
(defmacro acl2::simp-term-to-term (term rules &rest rest)
  `(mv-let (erp dag)
     (acl2::make-term-into-dag (acl2::check-arities ,term)
                               nil ;fixme interpreted-function-alist
                               )
     (if erp
         (mv erp nil state)
       (mv-let (erp dag-lst-or-quotep state)
         (simp-dag dag
                   :rules ,rules
                   ,@rest)
         (if erp
             (mv erp nil state)
           (mv (erp-nil)
               (dag-to-term dag-lst-or-quotep)
               state))))))

;; Test whether the stack height of X86 is less than it was when the stack pointer was OLD-RSP.
;; Since the stack grows from high to low, the stack height is less when the RSP is greater.
(defun stack-height-decreased-wrt (x86 old-rsp)
  (declare (xargs :stobjs x86
                  :guard (natp old-rsp))) ;tighten?
  (> (rgfi *rsp* x86) old-rsp))

(defun stack-height-increased-wrt (x86 old-rsp)
  (declare (xargs :stobjs x86
                  :guard (natp old-rsp))) ;tighten?
  (< (rgfi *rsp* x86) old-rsp))

(defun get-pc (x86)
  (declare (xargs :stobjs x86))
  (rip x86))

;;TODO: How can we determine whether we are in a subroutine call (can't just
;;look at RSP)?  I guess we could include subroutine PCs as part of the code
;;segment for now...  Or check RBP?

(defp run-until-exit-segment-or-hit-loop-header (starting-rsp
                                                 segment-pcs ;a list of addresses (will not include the header of the current loop)
                                                 loop-headers ;a list of addresses
                                                 x86)
  ;; If we've exited the subroutine call, then we've exited the segment, so stop:
  (if (stack-height-decreased-wrt x86 starting-rsp)
      x86
    ;; If we are at the loop header of a nested loop (or perhaps of the current
    ;; loop, but that usually won't happen since we exclude it from the segment
    ;; PCs), then stop:
    (if (memberp (get-pc x86) loop-headers)
        x86
      ;;otherwise, we are not at a loop header:
      (if nil ;;(stack-height-increased-wrt x86 starting-rsp) ;if we are in a subroutine call, take another step
          (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (x86-fetch-decode-execute x86))
        ;;the stack height is the same as the height of the segment:
        (if (not (member (get-pc x86) segment-pcs))
            x86 ;if we are at the right stack height and not at one of the segment pcs, we've exited the segment
          ;;otherwise, take a step:
          (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (x86-fetch-decode-execute x86)))))))

;; (defthm run-until-exit-segment-or-hit-loop-header-opener-1
;;   (implies (and (stack-height-increased-wrt x86 starting-rsp)
;;                 (not (memberp (get-pc x86) loop-headers)))
;;            (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers x86)
;;                   (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (x86-fetch-decode-execute x86)))))

(defthm run-until-exit-segment-or-hit-loop-header-opener-2
  (implies (and ;(not (stack-height-increased-wrt x86 starting-rsp))
                (not (stack-height-decreased-wrt x86 starting-rsp))
                (memberp (get-pc x86) segment-pcs)
                (not (memberp (get-pc x86) loop-headers)))
           (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers x86)
                  (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (x86-fetch-decode-execute x86)))))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-1
  (implies (stack-height-decreased-wrt x86 starting-rsp)
           (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers x86)
                  x86)))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-2
  (implies (memberp (get-pc x86) loop-headers)
           (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers x86)
                  x86)))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-3
  (implies (and ;;(not (stack-height-increased-wrt x86 starting-rsp))
                (not (stack-height-decreased-wrt x86 starting-rsp))
                (not (memberp (get-pc x86) segment-pcs)))
           (equal (run-until-exit-segment-or-hit-loop-header
                   starting-rsp
                   segment-pcs loop-headers x86)
                  x86)))

(defthm run-until-exit-segment-or-hit-loop-header-of-myif-split
  (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (myif test s1 s2))
         (myif test
                     (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers s1)
                     (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers s2)))
  :hints (("Goal" :in-theory (enable myif))))

;this puts in myif...
(defthm run-until-exit-segment-or-hit-loop-header-of-if
  (equal (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers (if test s1 s2))
         (myif test
                     (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers s1)
                     (run-until-exit-segment-or-hit-loop-header starting-rsp segment-pcs loop-headers s2))))

(defun symbolic-execution-rules ()
  '(;;run-until-exit-segment-or-hit-loop-header-opener-1
    run-until-exit-segment-or-hit-loop-header-opener-2
    run-until-exit-segment-or-hit-loop-header-base-case-1
    run-until-exit-segment-or-hit-loop-header-base-case-2
    run-until-exit-segment-or-hit-loop-header-base-case-3
    run-until-exit-segment-or-hit-loop-header-of-myif-split
    run-until-exit-segment-or-hit-loop-header-of-if))

(acl2::ensure-rules-known (symbolic-execution-rules))

;; Essay on Variables: The main variable used to represent the state is x86
;; (once we support nested loops, I guess we'll use x86_0, x86_1, etc.).  Other
;; variables may be introduced by the user or the tool to represent particular
;; state components.  (For compositional lifting, where the goal is to express
;; the transformation done on the state, we may need to replace these at the
;; end with their expressions over the initial state.)  (TODO: What about
;; aliasing? Maybe we only introduce such vars for registers?  Or maybe it's
;; okay to refer to the same input with several names.)  Assumptions can be
;; over the variable x86 and perhaps other vars.  Equality assumptions can be
;; used to introduce the pther vars.

;; ;; Repeatedly advance the state and lift loops.
;; ;; Returns (mv erp event state result-array-stobj)
;; ;; The state should already be stepped past the loop header (because we stop symbolic execution when we hit the loop header again?)
;; (defun lift-code-segment-aux (state-dag ;over the var x86 and perhaps other vars representing inputs (see the Essay on Variables)
;;                               segment-pcs ;PCs of the code segment to lift (should not include the header of the current loop)
;; ;loop-alist ; maps loop headers (PCs) to lists of PCs in the corresponding loops
;;                               assumptions ; over x86 and perhaps other vars (see the Essay on Variables)
;;                               extra-rules ; rules to enable
;;                               rules-to-monitor ; rules to monitor
;;                               starting-rsp ;tells us the stack height of the current subroutine
;;                               loop-headers
;;                               print
;;                               state
;;                               result-array-stobj)

;; ;work around a lambda in the formula of acl2::member-of-cons
;; (defthm acl2::member-equal-of-cons
;;   (equal (member-equal a (cons b x))
;;          (if (equal a b)
;;              (cons b x)
;;              (member-equal a x))))

(defun lifter-rules2 ()
  (append ;or put these in symbolic-execution-rules ?:
   '(stack-height-increased-wrt
     stack-height-decreased-wrt
     get-pc
     acl2::memberp-of-cons-irrel-strong
     x86isa::memberp-of-cons-same
     acl2::memberp-of-nil
;     acl2::member-equal-of-cons
     acl2::equal-of-same-cancel-4
     acl2::right-cancellation-for-+
     x86isa::logext-64-does-nothing-when-canonical-address-p
     x86isa::equal-of-if-constants
     x86isa::equal-of-if-constants-alt
     acl2::bool-fix-when-booleanp
     x86isa::if-t-nil
     x86isa::mv-nth-of-if
     x86isa::canonical-address-p-of-if
     x86isa::+-of-if-arg1
     x86isa::+-of-if-arg2
     acl2::bvchop-numeric-bound
     x86isa::xw-of-rip-and-if
     x86isa::if-x-x-y
     x86p-of-write ;move
     read-of-write-same ;move
     get-flag-of-write
     xr-of-write
     read-of-xw-irrel
     64-bit-modep-of-write
     program-at-of-write
     alignment-checking-enabled-p-of-write
     mod-of-plus-reduce-constants
     mv-nth-1-of-rb-becomes-read
     mv-nth-1-of-wb-becomes-write
     xr-of-write
     write-of-xw-irrel
     read-of-xw-irrel
     read-of-set-flag
     x86p-of-write
     64-bit-modep-of-write
     program-at-of-write
     set-flag-of-write
     alignment-checking-enabled-p-of-write
     read-of-write-disjoint2
     write-of-write-same
     read-in-terms-of-nth-and-pos-eric ; this is for resolving reads of the program.
     read-in-terms-of-nth-and-pos-eric-4-bytes ; this is for resolving reads of the program.
     acl2::equal-of-same-cancel-4
     acl2::equal-of-same-cancel-3
     acl2::equal-of-bvplus-constant-and-constant
     acl2::equal-of-bvplus-constant-and-constant-alt
     acl2::mod-of-+-of-constant
     )
;(x86isa::lifter-rules)
   ))

(acl2::ensure-rules-known (lifter-rules2))

(acl2::ensure-rules-known (lifter-rules32))
(acl2::ensure-rules-known (lifter-rules64))

;; Eventually we may add these rules about read to lifter-rules2.
(defun invariant-preservation-rules ()
  (append (lifter-rules2)
          '(mv-nth-1-of-rb-becomes-read
            read-of-write-disjoint
            read-of-write-same
            )))

(acl2::ensure-rules-known (invariant-preservation-rules))

;; Returns (mv erp rsp-dag state).
(defun extract-rsp-dag (;;assumptions
                          extra-rules
                          remove-rules
                          ;;rules-to-monitor
                          state-dag
                          ;; state-var
                          lifter-rules
                          state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* (((mv erp dag) (compose-term-and-dag '(xr ':rgf '4 :x86) :x86 state-dag)) ;todo make a version of compose-term-and-dag that translates and checks its arg
       ((when erp) (mv erp nil state)))
    (simp-dag dag :rules (set-difference-eq (append lifter-rules extra-rules) remove-rules)
              :check-inputs nil)))

;; Returns (mv erp rbp-dag state).
(defun extract-rbp-dag (;;assumptions
                          extra-rules
                          remove-rules
                          ;;rules-to-monitor
                          state-dag
                          ;; state-var
                          lifter-rules
                          state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* (((mv erp dag) (compose-term-and-dag '(xr ':rgf '5 :x86) :x86 state-dag)) ;todo make a version of compose-term-and-dag that translates and checks its arg
       ((when erp) (mv erp nil state)))
    (simp-dag dag :rules (set-difference-eq (append lifter-rules extra-rules) remove-rules)
              :check-inputs nil)))

;; Returns (mv erp pc-dag state).
(defun extract-pc-dag (state-dag
                       assumptions
                       extra-rules
                       remove-rules
                       ;;rules-to-monitor
                       ;; state-var
                       lifter-rules
                       state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (b* (((mv erp dag) (compose-term-and-dag '(xr ':rip 'nil :x86) :x86 state-dag))
       ((when erp) (mv erp nil state)))
    (simp-dag dag
              :rules (set-difference-eq (append lifter-rules extra-rules) remove-rules)
              :assumptions assumptions ;need to know that text offset is reasonable
              :monitor '(x86isa::logext-48-does-nothing-when-canonical-address-p)
              :check-inputs nil)))

(defun offsets-up-to (num)
  (declare (xargs :guard (or (natp num)
                             (eql -1 num))
                  :measure (if (not (natp num))
                               0
                             (+ 1 num))))
  (if (not (natp num))
      (reverse nil)
    (cons num
          (offsets-up-to (+ -1 num)))))

(defun relative-pc-term (offset base)
  (declare (xargs :guard (and (integerp offset)
                              (pseudo-termp base))))
  (if (= 0 offset)
      base ;no need to add 0
    `(binary-+ ',offset ,base)))

;; ;;TODO: What about offset 0?
;; (defun create-text-offset-terms (num)
;;   (declare (xargs :guard (natp num)))
;;   (if (zp num)
;;       (list 'text-offset)
;;     (cons (relative-pc-term num 'text-offset)
;;           (create-text-offset-terms (+ -1 num)))))

(defthm integerp-of-car-when-integer-listp
  (implies (and (integer-listp x)
                (consp x))
           (integerp (car x)))
  :hints (("Goal" :in-theory (enable integer-listp))))

(defun relative-pc-terms (offsets base)
  (declare (xargs :guard (and (integer-listp offsets)
                              (pseudo-termp base))))
  (if (endp offsets)
      nil
    (cons (relative-pc-term (first offsets) base)
          (relative-pc-terms (rest offsets) base))))

;; Replace state vars in the assumptions with the current state-var and try to
;; show that they still hold.  Returns (mv erp proved-assumptions
;; failed-assumptions state).  TODO: Don't bother to try
;; ones that are only about the RSP, since we push back the RSP of state-var
;; anyway?
(defun try-to-update-assumptions (assumptions
                                  extra-rules
                                  remove-rules
                                  rules-to-monitor
                                  state-dag
                                  state-var
                                  previous-state-vars
                                  all-assumptions
                                  proved-assumptions-acc
                                  failed-assumptions-acc
                                  lifter-rules
                                  state)
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (and (pseudo-term-listp assumptions)
                              (pseudo-term-listp all-assumptions)
                              (symbol-listp previous-state-vars)
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp rules-to-monitor))))
  (if (endp assumptions)
      (mv (erp-nil)
          (reverse proved-assumptions-acc)
          (reverse failed-assumptions-acc)
          state)
    (b* ((assumption (first assumptions))
         (updated-assumption (acl2::sublis-var-simple (map-all-to-val previous-state-vars state-var) assumption))
         (- (cw "(Attempting to prove assumption ~x0.~%" updated-assumption))
         ((mv erp dag-to-prove) (compose-term-and-dag updated-assumption state-var state-dag))
         ((when erp) (mv erp nil nil state))
         (- (cw "(DAG to prove: ~x0.)~%" dag-to-prove))
         (- (cw "(Using ~x0 assumptions.)~%" (len all-assumptions)))
         ;; prove that the original assumptions imply that the updated assumption holds over state-dag
         ((mv erp res state)
          (simp-dag dag-to-prove
                    :rules (set-difference-eq
                            (append (invariant-preservation-rules)
                                    lifter-rules
                                    extra-rules)
                            remove-rules)
                    :monitor (append '( ;xr-wb-in-app-view
                                       )
                                     rules-to-monitor)
                    :assumptions all-assumptions
                    :check-inputs nil))
         ((when erp) (mv erp nil nil state)))
      (if (equal res *t*) ;todo: allow other non-nil constants?
          (prog2$ (cw "Success.)~%")
                  (try-to-update-assumptions (rest assumptions)
                                             extra-rules
                                             remove-rules
                                             rules-to-monitor
                                             state-dag state-var previous-state-vars all-assumptions
                                             (cons updated-assumption proved-assumptions-acc)
                                             failed-assumptions-acc
                                             lifter-rules
                                             state))
        (prog2$ (cw "Failed.  Candidate assumption rewrote to ~x0.)~%" (dag-to-term res)) ;todo: think about blowup
                (try-to-update-assumptions (rest assumptions)
                                           extra-rules
                                           remove-rules
                                           rules-to-monitor
                                           state-dag state-var previous-state-vars all-assumptions
                                           proved-assumptions-acc
                                           (cons updated-assumption failed-assumptions-acc)
                                           lifter-rules
                                           state))))))

(defun get-added-offset (term base-var)
  (if (eq term base-var)
      0
    (if (and (eq 'binary-+ (ffn-symb term))
             (quotep (farg1 term))
             (eq base-var (farg2 term)))
        (unquote (farg1 term))
      (er hard 'get-added-offset "Unexpected term: ~x0." term))))


;; Returns (mv erp one-rep-term exit-term exit-test-term state) where one-rep-term
;; represents the branches that return to the loop top, exit-term represents
;; the branches that exit the loop, and exit-test-term represents the test
;; governing the branches that exit the loop.  :one-rep-term can be :none if no
;; branches return to the loop top.  Likewise, exit-term can be :none if no
;; branches exit the loop.  loop-body-term is a myif nest with x86 states at
;; the leaves.
(defun analyze-loop-body-aux (loop-body-term loop-top-pc-term loop-top-rsp-term extra-rules remove-rules lifter-rules assumptions state)
  (declare (xargs :stobjs (state)
                  :mode :program)
           (irrelevant loop-top-rsp-term) ;todo
           )
  (if (call-of 'myif loop-body-term)
      (b* ((test (farg1 loop-body-term))
           ((mv erp one-rep-term1 exit-term1 exit-test-term1 state)
            (analyze-loop-body-aux (farg2 loop-body-term) loop-top-pc-term loop-top-rsp-term extra-rules remove-rules lifter-rules assumptions state))
           ((when erp) (mv erp nil nil nil state))
           ((mv erp one-rep-term2 exit-term2 exit-test-term2 state)
            (analyze-loop-body-aux (farg3 loop-body-term) loop-top-pc-term loop-top-rsp-term extra-rules remove-rules lifter-rules assumptions state))
           ((when erp) (mv erp nil nil nil state)))
        (mv (erp-nil)
            (if (eq :none one-rep-term1)
                one-rep-term2
              (if (eq :none one-rep-term2)
                  one-rep-term1
                `(myif ,test ,one-rep-term1 ,one-rep-term2)))
            (if (eq :none exit-term1)
                exit-term2
              (if (eq :none exit-term2)
                  exit-term1
                `(myif ,test ,exit-term1 ,exit-term2)))
            `(myif ,test ,exit-test-term1 ,exit-test-term2) ;gets simplified in the wrapper
            state))
    ;; loop-body-term should be an x86 state.  Test whether it has exited the loop:
    (b* (((mv erp exitp state)
          (acl2::simp-term-to-term ;; `(if (stack-height-decreased-wrt ,loop-body-term ,loop-top-rsp-term)
           ;;     't
           ;;   (if (stack-height-increased-wrt ,loop-body-term ,loop-top-rsp-term)
           ;;       'nil
           ;;     ;; stack height is the same as when we entered the loop:
           ;;     (not (equal (get-pc ,loop-body-term) ,loop-top-pc-term))))
           ;; assuming no recursion, we don't need to check the stack height:
           `(not (equal (get-pc ,loop-body-term) ,loop-top-pc-term))
           (set-difference-eq
            (append (lifter-rules2)
                    lifter-rules
                    extra-rules
                    (myif-rules)
                    '(x86isa::xr-of-myif))
            remove-rules)
           :assumptions assumptions))
         ((when erp) (mv erp nil nil nil state)))
      (if (not (quotep exitp))
          (prog2$ (er hard 'analyze-loop-body-aux "Failed to decide whether branch has exited the loop.  Result: ~X01." exitp nil)
                  (mv (erp-t) nil nil nil state))
        (if (unquote exitp)
            (mv (erp-nil) :none loop-body-term *t* state)
          (mv (erp-nil) loop-body-term :none *nil* state))))))

;; Returns (mv erp one-rep-term exit-term exit-test-term state
;;) where one-rep-term represents the branches that
;; return to the loop top, exit-term represents the branches that exit the
;; loop, and exit-test-term represents the test governing the branches that
;; exit the loop.
(defun analyze-loop-body (loop-body-term loop-top-pc-term loop-top-rsp-term extra-rules remove-rules lifter-rules assumptions state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (mv-let (erp one-rep-term exit-term exit-test-term state)
    (analyze-loop-body-aux loop-body-term loop-top-pc-term loop-top-rsp-term extra-rules remove-rules lifter-rules assumptions state)
    (if erp
        (mv erp nil nil nil state)
      (if (eq :none one-rep-term)
          (prog2$ (er hard 'analyze-loop-body-aux "There appear to be no branches that return to the loop top.")
                  (mv (erp-t) nil nil nil state))
        (if (eq :none exit-term)
            (prog2$ (er hard 'analyze-loop-body-aux "There appear to be no branches that exit the loop.")
                    (mv (erp-t) nil nil nil state))
          (b* (((mv erp exit-test-term state)
                (acl2::simp-term-to-term exit-test-term
                                         (append lifter-rules
                                                 (myif-rules) ;simplify myif of t and t, myif of t and nil, etc.
                                                 )))
               ((when erp) (mv erp nil nil nil state)))
            (mv (erp-nil) one-rep-term exit-term exit-test-term state)))))))

(in-theory (disable ACL2::NATP-MEANS-NON-NEG)) ;todo

;todo: this is slowing stuff down: ACL2::USE-ALL-HEAPREF-TABLE-ENTRYP-FOR-CAR

;todo: speed this up
;; Returns (mv okp xw-triples core-term).  Each xw-triple is of the form (list field index value).
(defun check-and-extract-xws (term xw-triples-acc)
  (if (not (call-of 'xw term))
      (mv t (reverse xw-triples-acc) term)
    (let* ((field (farg1 term))
           (index (farg2 term))
           (value (farg3 term))
           (x86 (farg4 term)))
      (if (or ;; registers:
           (and (quotep field)
                (eq (unquote field) :rgf)
                (quotep index)
                (member (unquote index) *register-numbers*))
           ;; instruction pointer:
           (and (equal field '':rip)
                (equal index ''nil))
           ;; the source of undefined values:
           (and (equal field '':undef)
                (equal index ''nil)))
          (check-and-extract-xws x86 (cons (list (unquote field) (unquote index) value) xw-triples-acc))
        ;; Anything else is an error (TODO: Allow more things here?)
        (prog2$ (er hard 'check-and-extract-xws "Unsupported call to XW in one-rep-dag: ~x0." term)
                (mv nil nil term))))))

;; Returns (mv okp write-triples core-term). Each triple is (list numbytes base-addr val)
(defun check-and-extract-writes (term write-triples-acc)
  (if (not (call-of 'write term))
      (mv t (reverse write-triples-acc) term)
    (let* ((n (farg1 term))
           (base-addr (farg2 term))
           (val (farg3 term))
           (x86 (farg4 term)))
      (if (and (quotep n)
               (posp (unquote n))
               ;; anything about the base-addr and val?
               )
          (check-and-extract-writes x86 (cons (list n base-addr val) write-triples-acc))
        (prog2$ (er hard 'check-and-extract-writes "Unsupported call to WRITE in one-rep-dag: ~x0." term)
                (mv nil nil term))))))

;; Returns (mv okp flag-pairs core-term).  Each pair is (list flag-keyword val)
(defun check-and-extract-flags (term flag-pairs-acc)
  (if (not (call-of 'set-flag term))
      (mv t (reverse flag-pairs-acc) term)
    (let* ((flag-name (farg1 term)) ;a keyword
           (val (farg2 term))
           (x86 (farg3 term)))
      (if (and (quotep flag-name)
               (member (unquote flag-name) x::*flags*)
               ;; anything about the val?
               )
          (check-and-extract-flags x86 (cons (list (unquote flag-name) val) flag-pairs-acc))
        (prog2$ (er hard 'check-and-extract-flags "Unsupported call to SET-FLAG in one-rep-dag: ~x0." term)
                (mv nil nil term))))))

;; We expect TERM to be a nest of calls to XW, around a nest of calls to WRITE,
;; around a nest of calls to SET-FLAG, around the state-var.  Returns (mv okp
;; xw-triples write-triples flag-pairs).
(defun check-and-split-one-rep-term (term state-var)
  (b* (((mv xws-okp xw-triples term) (check-and-extract-xws term nil))
       ((mv writes-okp write-triples term) (check-and-extract-writes term nil))
       ((mv flags-okp flag-pairs term) (check-and-extract-flags term nil)))
    (if (not (eq state-var term))
        (prog2$ (er hard? 'check-and-split-one-rep-term "Unexpected core term: ~X01." term nil)
                (mv (erp-t) nil nil nil))
      (mv (and xws-okp writes-okp flags-okp)
          xw-triples
          write-triples
          flag-pairs))))

;; Keep only the fields and indices (drop the values)
(defun get-xw-pairs (xw-triples)
  (if (endp xw-triples)
      nil
    (let ((triple (first xw-triples)))
      (cons (list (first triple)
                  (second triple))
            (get-xw-pairs (rest xw-triples))))))

;; Keep only the numbytes and base-addrs (drop the values)
(defun get-write-pairs (write-triples)
  (if (endp write-triples)
      nil
    (let ((triple (first write-triples)))
      (cons (list (first triple)
                  (second triple))
            (get-write-pairs (rest write-triples))))))

;; Keep only the addresses (drop the numbytes and value)
(defun get-write-addresses (write-triples)
  (if (endp write-triples)
      nil
    (let* ((triple (first write-triples))
           (base-addr (second triple)))
      (cons base-addr
            (get-write-addresses (rest write-triples))))))

;; Keep only the flag names (drop the values)
(defun get-flag-names (flag-pairs)
  (if (endp flag-pairs)
      nil
    (let* ((pair (first flag-pairs))
           (flag-name (first pair)))
      (cons flag-name
            (get-flag-names (rest flag-pairs))))))

;;
;; Checking for aliasing
;;

;; Returns (mv erp res state).
(defun no-overlap-between-write-pairs (write-pair1
                                       write-pair2
                                       assumptions
                                       rules
                                       state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  ;; make a dag
  (b* ((num-bytes1 (first write-pair1))
       (base-addr1 (second write-pair1))
       (num-bytes2 (first write-pair2))
       (base-addr2 (second write-pair2))
       (- (cw "(Proving that there is no overlap between ~x0 bytes starting at ~x1 and ~x2 bytes starting at ~x3.~%" (unquote num-bytes1) base-addr1 (unquote num-bytes2) base-addr2))
       (separation-term `(separate ':r ,num-bytes1 ,base-addr1 ':r ,num-bytes2 ,base-addr2))
       ((mv erp result state)
        (acl2::simp-term separation-term
                         :rules rules
                         :assumptions assumptions))
       ((when erp) (mv erp nil state)))
    (if (equal result *t*)
        (progn$ (cw "Proved that there is not overlap.)~%")
                (mv nil t state))
      (progn$ (cw "ERROR: Failed to prove no overlap between ~x0 bytes starting at ~x1 and ~x2 bytes starting at ~x3.~%" num-bytes1 base-addr1 num-bytes2 base-addr2)
              (acl2::print-list result)
              (cw "Assumptions:~%")
              (acl2::print-list assumptions)
;              (cw ")")
              (hard-error 'no-overlap-between-write-pairs "Failed overlap check (see above)." nil)
              (mv (erp-t) nil state)))))

;; Returns (mv erp res state).
(defun no-overlap-between-write-pair-and-write-pairs (write-pair
                                                      write-pairs
                                                      assumptions
                                                      rules
                                                      state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (if (endp write-pairs)
      (mv nil t state)
    (b* ((write-pair2 (first write-pairs))
         ((mv erp res state)
          (no-overlap-between-write-pairs write-pair
                                          write-pair2
                                          assumptions
                                          rules
                                          state))
         ((when erp) (mv erp res state)))
      (if res
          (no-overlap-between-write-pair-and-write-pairs write-pair
                                                         (rest write-pairs)
                                                         assumptions
                                                         rules
                                                         state)
        (mv nil nil state)  ;failed
        ))))

;todo: repace write- with mem- in these functions
;; Returns (mv erp res state).
(defun no-overlap-in-write-pairs (write-pairs
                                  assumptions
                                  rules
                                  state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (if (endp write-pairs)
      (mv nil t state)
    (b* (((mv erp res state)
          (no-overlap-between-write-pair-and-write-pairs (first write-pairs) (rest write-pairs) assumptions rules state))
         ((when erp) (mv erp nil state)))
      (if res
          (no-overlap-in-write-pairs (rest write-pairs) assumptions rules state)
        (mv nil nil state) ;; we failed
        ))))

;; Returns (mv erp okp state).
(defun ensure-addresses-unchanged-by-body (address-terms ;todo: what vars are in this?
                                           one-rep-term
                                           state-var
                                           ;; assumptions
                                           rules
                                           state)
  (declare (xargs :stobjs (state)
                  :mode :program))
  (if (endp address-terms)
      (mv nil t state)
    (b* ((address-term (first address-terms))
         (address-unchanged-term
          `(equal ,address-term ,(acl2::sublis-var-simple (acons state-var one-rep-term nil) address-term)))
         ((mv erp result state)
          (acl2::simp-term address-unchanged-term
                           :rules rules
                           ;; :assumptions assumptions
                           ))
         ((when erp) (mv erp nil state)))
      (if (equal result *t*)
          (prog2$ (cw "(Proved that address ~x0 is unchanged.)~%" address-term)
                  (ensure-addresses-unchanged-by-body (rest address-terms) one-rep-term state-var rules state))
        (prog2$ (er hard 'addresses-unchanged-by-body "Failed to show that address ~x0 is unchanged by the loop body.  Result ~x1." address-term result)
                (mv (erp-t) nil state) ;; we failed
                )))))

;; Returns a name (a symbol), or a string to indicate failure.  TODO: Should I be using msgps here?
;; expr should be the application of something like xr to a state variable.
;; If state-var is non-nil, all state-vars in the expr must match it.
(defun name-of-state-component-aux (expr state-var)
  (declare (xargs :guard (and (pseudo-termp expr)
                              (symbolp state-var))))
  ;; Match a register access:
  (mv-let (matchp alist)
    (acl2::unify-term expr '(xr ':rgf :index :state-var))
    (if matchp
        (if (and state-var
                 (not (equal state-var (lookup-eq :state-var alist))))
            "State-var mismatch"
          (let ((index (lookup-eq :index alist)))
            (if (myquotep index)
                (let ((index (unquote index)))
                  (if (and (natp index)
                           (< index (len *register-names*)))
                      (nth index *register-names*)
                    "Bad register number"))
              "Register number is not a quoted constant")))
      ;; Match the undefined count:
      (mv-let (matchp alist)
        (acl2::unify-term expr '(xr ':undef 'nil :state-var))
        (if matchp
            (if (and state-var
                     (not (equal state-var (lookup-eq :state-var alist))))
                "State-var mismatch"
              'undef)
          ;; Match a flag:
          (mv-let (matchp alist)
            (acl2::unify-term expr '(get-flag :flag-name :state-var))
            (if matchp
                (if (and state-var
                         (not (equal state-var (lookup-eq :state-var alist))))
                    "State-var mismatch"
                  (let ((flag-name (lookup-eq :flag-name alist)))
                    (if (not (myquotep flag-name))
                        "Flag name is not a quoted constant."
                      (let ((flag-name (unquote flag-name)))
                        (case flag-name
                          (:af 'flag-af)
                          (:cf 'flag-cf)
                          (:pf 'flag-pf)
                          (:of 'flag-of)
                          (:sf 'flag-sf)
                          (:zf 'flag-zf) ;todo: add more flags
                          (otherwise "Unsupported flag name.")
                          )))))
              ;; Handle a read:
              (mv-let (matchp alist)
                ;; in general, the two state-vars here may not match (e.g., x86_0 and :initial-loop-top-state)
                (acl2::unify-term expr '(read '4 (binary-+ :offset (XR ':RGF '4 :state-var)) :state-var2))
                (if matchp
                    (if (and state-var
                             (or (not (equal state-var (lookup-eq :state-var alist)))
                                 (not (equal state-var (lookup-eq :state-var2 alist)))))
                        "State-var mismatch"
                      (let ((offset (lookup-eq :offset alist)))
                        (if (not (and (myquotep offset)
                                      (integerp (unquote offset))
                                      (< (unquote offset) 0)))
                            "Unsupported memory read."
                          (pack-in-package-of-symbol 'var 'var (- (unquote offset))))))
                  "Unexpected state component.")))))))))

(defun name-of-state-component (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (let ((res (name-of-state-component-aux expr nil)))
    (if (stringp res) ;an error
        (er hard? 'name-of-state-component "Unexpected state component expr: ~X01.  Result: ~s2"
            expr ;(untranslate expr nil (w state)) ;;todo: thread in w here?
            nil res)
      res)))

;; Return a name for EXPR, if it represents a component of X86_0, or nil to
;; indicate failure.
(defun maybe-name-of-initial-state-component (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (let ((res (name-of-state-component-aux expr 'x86_0)))
    (if (stringp res) ;error
        nil
      res)))

;; Replace components of X86_0 with suitable names
(mutual-recursion
 (defun replace-components-of-initial-state-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :guard-hints (("Goal" :in-theory (enable pseudo-termp)))))
   (or (maybe-name-of-initial-state-component term)
       (if (variablep term)
           term
         (if (quotep term)
             term
           (cons (ffn-symb term)
                 (replace-components-of-initial-state-in-terms (fargs term)))))))

 (defun replace-components-of-initial-state-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :guard-hints (("Goal" :in-theory (enable pseudo-termp)))))
   (if (endp terms)
       nil
     (cons (replace-components-of-initial-state-in-term (first terms))
           (replace-components-of-initial-state-in-terms (rest terms))))))

;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist).
(defun make-loop-parameters-for-xw-triples (xw-triples next-param-number
                                                       updated-state-term
                                                       paramnum-update-alist
                                                       paramnum-extractor-alist
                                                       paramnum-name-alist)
  (if (endp xw-triples)
      (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
    (b* ((xw-triple (first xw-triples))
         (field (first xw-triple))  ;not quoted
         (index (second xw-triple)) ;not quoted
         )
      (if (and (equal field :rip)
               (equal index nil))
          ;; Don't make a param for the RIP:
          (make-loop-parameters-for-xw-triples (rest xw-triples)
                                               next-param-number
                                               updated-state-term
                                               paramnum-update-alist
                                               paramnum-extractor-alist
                                               paramnum-name-alist)
        (b* ((value-term (third xw-triple))
             (updated-state-term `(xw ',field ',index (nth ',next-param-number :loop-function-result) ,updated-state-term))
             (paramnum-update-alist (acons next-param-number value-term paramnum-update-alist))
             (paramnum-extractor `(xr ',field ',index :initial-loop-top-state))
             (paramnum-extractor-alist (acons next-param-number paramnum-extractor paramnum-extractor-alist))
             (param-name (name-of-state-component paramnum-extractor))
             (- (cw "(Param ~x0 is ~x1.)~%" next-param-number param-name))
             (paramnum-name-alist (acons next-param-number param-name paramnum-name-alist)) ;just some name
             )
          (make-loop-parameters-for-xw-triples (rest xw-triples)
                                               (+ 1 next-param-number)
                                               updated-state-term
                                               paramnum-update-alist
                                               paramnum-extractor-alist
                                               paramnum-name-alist))))))

;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist).
(defun make-loop-parameters-for-write-triples (write-triples next-param-number updated-state-term
                                                             paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
  (if (endp write-triples)
      (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
    (b* ((write-triple (first write-triples))
         (n (first write-triple))  ;often quoted
         (base-addr (second write-triple))
         (value-term (third write-triple))
         (updated-state-term `(write ,n ,base-addr (nth ',next-param-number :loop-function-result) ,updated-state-term))
         (paramnum-update-alist (acons next-param-number value-term paramnum-update-alist))
         (paramnum-extractor `(read ,n ,base-addr :initial-loop-top-state))
         (paramnum-extractor-alist (acons next-param-number paramnum-extractor paramnum-extractor-alist))
         (param-name (name-of-state-component paramnum-extractor))
         (- (cw "(Param ~x0 is ~x1.)~%" next-param-number param-name))
         (paramnum-name-alist (acons next-param-number param-name paramnum-name-alist)) ;just some name
         )
      (make-loop-parameters-for-write-triples (rest write-triples)
                                              (+ 1 next-param-number)
                                              updated-state-term
                                              paramnum-update-alist
                                              paramnum-extractor-alist
                                              paramnum-name-alist))))

;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist).
(defun make-loop-parameters-for-flag-pairs (flag-pairs next-param-number updated-state-term
                                                       paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
  (if (endp flag-pairs)
      (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
    (b* ((flag-pair (first flag-pairs))
         (flag-name (first flag-pair)) ;not quoted
         (value-term (second flag-pair))
         (updated-state-term `(set-flag ',flag-name (nth ',next-param-number :loop-function-result) ,updated-state-term))
         (paramnum-update-alist (acons next-param-number value-term paramnum-update-alist))
         (paramnum-extractor `(get-flag ',flag-name :initial-loop-top-state))
         (paramnum-extractor-alist (acons next-param-number paramnum-extractor paramnum-extractor-alist))
         (param-name (name-of-state-component paramnum-extractor) ;(list :flag flag-name)
                     )
         (- (cw "(Param ~x0 is ~x1.)~%" next-param-number param-name))
         (paramnum-name-alist (acons next-param-number param-name paramnum-name-alist)) ;just some name
         )
      (make-loop-parameters-for-flag-pairs (rest flag-pairs)
                                           (+ 1 next-param-number)
                                           updated-state-term
                                           paramnum-update-alist
                                           paramnum-extractor-alist
                                           paramnum-name-alist))))

;; maps param-extractors over :initial-loop-top-state to the corresponding names
(defun make-replacement-alist (paramnum-extractor-alist paramnum-name-alist state-var)
  (if (endp paramnum-extractor-alist)
      nil
    (let* ((entry (car paramnum-extractor-alist))
           (parameter-number (car entry))
           (parameter-name (lookup-safe parameter-number paramnum-name-alist))
           (term (cdr entry))
;           (term (dag-to-term dag))
           (term (acl2::sublis-var-simple (acons :initial-loop-top-state state-var nil) term)))
      (acons term
             parameter-name ;;`(nth ',parameter-number params)
             (make-replacement-alist (cdr paramnum-extractor-alist) paramnum-name-alist state-var)))))

;; Check that each of the INVARIANTS holds over ONE-REP-TERM
;; Returns (mv erp proved-invariants failed-invariants state)
(defun prove-invariants-preserved (invariants ; the invariants left to check
                                   state-var
                                   one-rep-term
                                   assumptions ;the invariants over the state-var
                                   extra-rules
                                   remove-rules
                                   rules-to-monitor
                                   proved-invariants-acc failed-invariants-acc
                                   lifter-rules
                                   state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-term-listp invariants)
                              (symbolp state-var)
                              (pseudo-termp one-rep-term)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor))
                  :mode :program))
  (if (endp invariants)
      (mv (erp-nil) proved-invariants-acc failed-invariants-acc state)
    (b* ((invariant (first invariants))
         (- (cw "(Attempting to prove invariant ~X01:~%" invariant nil))
         (term-to-prove (acl2::sublis-var-simple (acons state-var one-rep-term nil) invariant))
         ((mv erp simplified-invariant state)
          (acl2::simp-term-to-term term-to-prove
                                 (set-difference-eq
                                  (append (invariant-preservation-rules)
                                          lifter-rules
                                         extra-rules)
                                  remove-rules)
                                 :assumptions assumptions
                                 :monitor rules-to-monitor))
         ((when erp) (mv erp nil nil state)))
      (if (equal *t* simplified-invariant)
          (prog2$ (cw "Proved it!)~%")
                  (prove-invariants-preserved (rest invariants)
                                              state-var
                                              one-rep-term
                                              assumptions ;the invariants over the state-var
                                              extra-rules
                                              remove-rules
                                              rules-to-monitor
                                              (cons invariant proved-invariants-acc)
                                              failed-invariants-acc
                                              lifter-rules
                                              state))
        (prog2$ (cw "Failed.  Candidate invariant rewrote to ~X01)~%" simplified-invariant nil)
                (prove-invariants-preserved (rest invariants)
                                            state-var
                                            one-rep-term
                                            assumptions ;the invariants over the state-var
                                            extra-rules
                                            remove-rules
                                            rules-to-monitor
                                            proved-invariants-acc
                                            (cons invariant failed-invariants-acc)
                                            lifter-rules
                                            state))))))
(defforall-simple nat-listp)

;todo: or use doublets
(defun loop-alistp (alist)
  (and (alistp alist)
       (nat-listp (strip-cars alist))
       (acl2::all-nat-listp (strip-cdrs alist))))

(defun acl2::pack-in-package-of-base-symbol-list (base-sym items)
  (if (endp items)
      nil
    (cons (pack-in-package-of-symbol base-sym base-sym (first items))
          (acl2::pack-in-package-of-base-symbol-list base-sym (rest items)))))

(mutual-recursion

 ;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
 (defun make-read-only-parameters-for-exprs (exprs
                                             next-param-number
                                             updated-state-term
                                             paramnum-update-alist
                                             paramnum-extractor-alist
                                             paramnum-name-alist
                                             state-var
                                             extra-vars)
   (if (endp exprs)
       (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
     (b* ((expr (first exprs))
          ((mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
           (make-read-only-parameters-for-expr expr
                                               next-param-number
                                               updated-state-term
                                               paramnum-update-alist
                                               paramnum-extractor-alist
                                               paramnum-name-alist
                                               state-var
                                               extra-vars)))
       (make-read-only-parameters-for-exprs (rest exprs)
                                            next-param-number
                                            updated-state-term
                                            paramnum-update-alist
                                            paramnum-extractor-alist
                                            paramnum-name-alist
                                            state-var
                                            extra-vars))))

 ;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
 ;; TODO Handle more things here!
 (defun make-read-only-parameters-for-expr (expr
                                            next-param-number
                                            updated-state-term
                                            paramnum-update-alist
                                            paramnum-extractor-alist
                                            paramnum-name-alist
                                            state-var
                                            extra-vars)
   (if (member-equal (acl2::sublis-var-simple (acons state-var :initial-loop-top-state nil) expr)
                     (strip-cdrs paramnum-extractor-alist)) ;this expr already corresponds to a param
       (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
     (if (variablep expr)
         (if (member-eq expr extra-vars)
             (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
           (prog2$ (er hard? 'make-read-only-parameters-for-expr "Unexpected var: ~x0." expr)
                   (mv nil nil nil nil nil)))
       (if (quotep expr)
           ;; nothing to do:
           (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (let ((fn (ffn-symb expr)))
           (if (eq 'read fn)
               (b* ((n (farg1 expr)) ;often quoted
                    (base-addr (farg2 expr))
                    (state-term (farg3 expr))
                    ((when (not (eq state-term state-var)))
                     (er hard 'make-read-only-parameters-for-expr "Unexpected read term: ~x0." expr)
                     (mv nil nil nil nil nil))
                    ;; make a read-only param:
                    ;; TODO: If it's a read-only-param, why are we writing it here?:
                    ;; (updated-state-term `(write ,n ,base-addr (nth ',next-param-number :loop-function-result) ,updated-state-term))
                    ;; The param gets updated with the read expression itself:
                    (paramnum-update-alist (acons next-param-number expr ;value-term
                                                  paramnum-update-alist))
                    (paramnum-extractor `(read ,n ,base-addr :initial-loop-top-state))
                    (paramnum-extractor-alist (acons next-param-number paramnum-extractor paramnum-extractor-alist))
                    (param-name (name-of-state-component paramnum-extractor)) ;for now, just some name
                    (- (cw "(Param ~x0 is ~x1.)~%" next-param-number param-name))
                    (paramnum-name-alist (acons next-param-number param-name paramnum-name-alist))
                    )
                 (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist))
             (if (eq 'xr fn)
                 (b* ((fld (farg1 expr)) ;often quoted
                      (index (farg2 expr))
                      (state-term (farg3 expr))
                      ((when (not (and (equal fld '':rgf)
                                       (quotep index)
                                       (eq state-term state-var))))
                       (er hard 'make-read-only-parameters-for-expr "Unexpected xr term: ~x0." expr)
                       (mv nil nil nil nil nil))
                      ;; make a read-only param:
                      ;; TODO: If it's a read-only-param, why are we writing it here?:
                      ;; (updated-state-term `(xw ':rgf ,index (nth ',next-param-number :loop-function-result) ,updated-state-term))
                      ;; The param gets updated with the read expression itself:
                      (paramnum-update-alist (acons next-param-number expr ;value-term
                                                    paramnum-update-alist))
                      (paramnum-extractor `(xr ':rgf ,index :initial-loop-top-state))
                      (paramnum-extractor-alist (acons next-param-number paramnum-extractor paramnum-extractor-alist))
                      (param-name (name-of-state-component paramnum-extractor)) ;for now, just some name
                      (- (cw "(Param ~x0 is ~x1.)~%" next-param-number param-name))
                      (paramnum-name-alist (acons next-param-number param-name paramnum-name-alist))
                      )
                   (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist))
               ;;  Otherwise, recur on the args:
               (make-read-only-parameters-for-exprs (fargs expr)
                                                    next-param-number
                                                    updated-state-term
                                                    paramnum-update-alist
                                                    paramnum-extractor-alist
                                                    paramnum-name-alist
                                                    state-var
                                                    extra-vars)))))))))


;; Returns (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
(defun make-read-only-parameters (paramnum-update-alist-to-check
                                  next-param-number
                                  updated-state-term
                                  paramnum-update-alist
                                  paramnum-extractor-alist
                                  paramnum-name-alist
                                  state-var
                                  extra-vars)
  (if (endp paramnum-update-alist-to-check)
      (mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
    (b* ((entry (first paramnum-update-alist-to-check))
         (update-expr (cdr entry))
         ((mv next-param-number updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
          (make-read-only-parameters-for-expr update-expr
                                              next-param-number
                                              updated-state-term
                                              paramnum-update-alist
                                              paramnum-extractor-alist
                                              paramnum-name-alist
                                              state-var
                                              extra-vars)))
      (make-read-only-parameters (rest paramnum-update-alist-to-check)
                                 next-param-number
                                 updated-state-term
                                 paramnum-update-alist
                                 paramnum-extractor-alist
                                 paramnum-name-alist
                                 state-var
                                 extra-vars))))

(defun make-initial-params-terms (paramnum-extractor-alist paramnum-name-alist param-update-terms)
  (if (endp paramnum-extractor-alist)
      nil
    (b* ((entry (first paramnum-extractor-alist))
         (paramnum (car entry))
         (extractor (cdr entry))
         ;;check for write-only;
         (term-to-seek ;`(nth ',paramnum params)
          (lookup-safe paramnum paramnum-name-alist))
         (occursp (acl2::subterm-of-anyp term-to-seek param-update-terms))
         (initial-value-term (if occursp
                                 extractor
                               (prog2$
                                (cw "(Note that param ~x0, ~x1, is write-only.)~%" paramnum extractor)
                                '':unused))))
      (cons initial-value-term
            (make-initial-params-terms (rest paramnum-extractor-alist) paramnum-name-alist param-update-terms)))))

(defun get-mem-pairs (param-extractors)
  (if (endp param-extractors)
      nil
    (let ((param-extractor (first param-extractors)))
      (if (and (call-of 'read param-extractor)
               (eql 3 (len (fargs param-extractor))) ;for guards
               )
          (cons (list (farg1 param-extractor) ;num-bytes
                      (farg2 param-extractor) ;base-addr
                      )
                (get-mem-pairs (rest param-extractors)))
        (get-mem-pairs (rest param-extractors))))))


(mutual-recursion

 ;; Returns (mv erp dag generated-events next-loop-num state)
 ;; TODO: What answers are needed?
 (defun lift-loop (loop-top-state-dag ;should be standing at a loop header
                   loop-depth
                   generated-events
                   next-loop-num
                   assumptions ;over x86_0 and perhaps other vars (see the Essay on Variables) ?
;                   original-rsp-term ; the RSP for the initial state (which the assumptions describe)
                   extra-rules
                   remove-rules
                   rules-to-monitor
                   loop-alist
                   print
                   measure-alist
                   base-name
                   lifter-rules
                   state

                   )
   (declare (xargs :stobjs (state)
                   :mode :program
                   :guard (and (posp loop-depth)
                               (pseudo-term-listp assumptions)
;                               (pseudo-termp original-rsp-term)
                               (symbol-listp extra-rules)
                               (symbol-listp remove-rules)
                               (symbol-listp rules-to-monitor)
                               (loop-alistp loop-alist)
                               (symbolp base-name)
                               ;; todo: strengthen:
                               (or (eq :skip measure-alist)
                                   (alistp measure-alist)))))
   (b* ((- (cw "(Lifting loop ~x0 (depth ~x1).~%" next-loop-num loop-depth))
        (this-loop-num next-loop-num)
        (next-loop-num (+ 1 next-loop-num))
        (state-var (pack-in-package-of-symbol 'x86_ 'x86_ loop-depth))
        (previous-state-nums (acl2::ints-in-range 0 (+ -1 loop-depth)))
        (previous-state-vars (my-pack-list2 'x86_ previous-state-nums))
        ;; Check the assumption vars:
        (assumption-vars (all-vars assumptions))
        ((when (member-eq state-var assumption-vars))
         (prog2$ (er hard 'lift-loop "Assumptions should not mention the state var ~x0." state-var)
                 (mv (erp-t) nil nil nil state)))
        ;; Extract the PC at the loop top:
        ((mv erp loop-top-pc-dag state)
         (extract-pc-dag loop-top-state-dag
                         assumptions
                         extra-rules
                         remove-rules
                         lifter-rules
                         state
                         ))
        ((when erp) (mv erp nil nil nil state))
        (loop-top-pc-term (dag-to-term loop-top-pc-dag))
        (- (cw "(Loop top PC is ~x0.)~%" loop-top-pc-term))
        (pc-offset (get-added-offset loop-top-pc-term 'text-offset))
        (pc-assumption `(equal (xr ':rip 'nil ,state-var) ,loop-top-pc-term))
        (- (cw "(Loop top PC assumpton: ~x0.)~%" pc-assumption))
        ;; Extract the RSP at the loop top:
        ((mv erp loop-top-rsp-dag state)
         (extract-rsp-dag extra-rules
                          remove-rules
                          loop-top-state-dag
                          lifter-rules
                          state
                          ))
        ((when erp) (mv erp nil nil nil state))
        (loop-top-rsp-term (dag-to-term loop-top-rsp-dag))
        ;; (- (cw "(Original RSP was ~x0.)~%" original-rsp-term)) ;will always be (xr ':rgf '4 x86_0) ?
        ;; ((when (not (equal original-rsp-term '(xr ':rgf '4 x86_0)))) ;todo: allow x86_1, etc. here
        ;;  (prog2$ (er hard 'lift-loop "Unexpected RSP term.")
        ;;          (mv (erp-t) nil nil nil state)))
        (- (cw "(Loop top RSP is ~x0.)~%" loop-top-rsp-term))

        ;; ((mv rsp-difference state)
        ;;  (acl2::simplify-term5 `(binary-+ ,loop-top-rsp-term (unary-- ,original-rsp-term))
        ;;                        (append lifter-rules
        ;;                                extra-rules)))
        ;; (- (cw "(RSP difference is ~x0.)~%" rsp-difference))
        ;; ((when (not (quotep rsp-difference)))
        ;;  (prog2$ (er hard 'lift-loop "RSP difference between initial state and loop top must be a constant.")
        ;;          (mv nil nil state)))
        ;; (rsp-adjustment (- (unquote rsp-difference)))
        ;; (- (cw "(RSP adjustment is ~x0.)~%" rsp-adjustment))

        ;; Extract the RBP at the loop top:
        ((mv erp loop-top-rbp-dag state)
         (extract-rbp-dag extra-rules
                          remove-rules
                          loop-top-state-dag
                          lifter-rules
                          state
                          ))
        ((when erp) (mv erp nil nil nil state))
        (loop-top-rbp-term (dag-to-term loop-top-rbp-dag))
        (- (cw "(Loop top RBP is ~x0.)~%" loop-top-rbp-term))

        (- (cw "(Determining which assumptions still hold before the loop:~%"))
        (candidate-assumptions assumptions
                               ;; (acl2::replace-in-terms assumptions
                               ;;                         (acons '(xr ':rgf '4 x86_0) ;todo: generalize the _0
                               ;;                                `(binary-+ ',rsp-adjustment (xr ':rgf '4 x86_1))
                               ;;                                nil))
                               )
        ;; ((mv candidate-assumptions state)
        ;;  (acl2::simplify-terms-to-new-terms candidate-assumptions
        ;;                                     (acl2::make-rule-alist '(ACL2::FOLD-CONSTS-IN-+) (w state)) ; just combine constants
        ;;                                     ))
        (- (cw "(Candidate assumptions: ~x0)~%" candidate-assumptions)) ;these are still over the old state-var?

        ;; The assumption about the RIP almost certainly won't still hold.
        ((mv erp loop-top-assumptions failed-loop-top-assumptions state)
         (try-to-update-assumptions candidate-assumptions
                                    extra-rules
                                    remove-rules
                                    rules-to-monitor loop-top-state-dag state-var previous-state-vars
                                    assumptions
                                    nil nil lifter-rules state))
        ((when erp) (mv erp nil nil nil state))
        (- (cw "Done determining which assumptions hold before the loop)~%"))
        (- (cw "(~x0 assumptions hold before the loop: ~x1.)~%" (len loop-top-assumptions) loop-top-assumptions))
        (- (cw "(~x0 assumptions failed to hold at the loop top: ~x1)~%" (len failed-loop-top-assumptions) failed-loop-top-assumptions))
        ;; Now lift the loop body wrt the loop-top-assumptions
        (this-loop-offsets (lookup-safe pc-offset loop-alist))
        (this-loop-offsets-no-header (remove pc-offset this-loop-offsets))
        (- (cw "(PC offsets in this loop: ~x0.)~%" this-loop-offsets))
        ;; (segment-pc-terms (relative-pc-terms this-loop-offsets 'text-offset))
        ;; (- (cw "(segment-pc-terms: ~x0)~%" segment-pc-terms))
        ;; TODO: This assumes there is a single loop:
        (all-loop-header-pc-terms (relative-pc-terms (list pc-offset) 'text-offset))
        (- (cw "(all-loop-header-pc-terms ~x0)~%" all-loop-header-pc-terms))
        ;; (term-to-run `(run-until-exit-segment-or-hit-loop-header (xr ':rgf '4 ,state-var) ;;starting-rsp
        ;;                                                          ,(acl2::make-cons-nest segment-pc-terms)
        ;;                                                          ,(acl2::make-cons-nest all-loop-header-pc-terms)
        ;;                                                          ;; Step once to start, to get past the loop header:
        ;;                                                          (x86-fetch-decode-execute ,state-var)))
        ;; (- (cw "(Term for symbolically executing the loop body: ~x0)~%" term-to-run))
        (loop-invariants ;; The base pointer and stack pointer should not change inside the routine (TODO: Do I need this?):
         (append `((equal (xr ':rgf '5 ,state-var) ;; this "pushes" back the RBP to some expression over the initial state
                          ,loop-top-rbp-term)
                   (equal (xr ':rgf '4 ,state-var) ;; this "pushes" back the RSP to some expression over the initial state
                          ,loop-top-rsp-term))
                 loop-top-assumptions
                 assumptions ;these are about previous state vars and should still hold (and things about state-var may be "pushed back" so we need these)
                 ))
        (loop-body-assumptions (cons pc-assumption loop-invariants))
        (- (cw "(Assumptions for symbolically executing the loop body: ~x0)~%" (untranslate-terms loop-body-assumptions nil (w state))))


        ;; Perform the symbolic execution of the loop body:
        ((mv erp loop-body-dag generated-events
             ;; & ;generated-rules
             next-loop-num
             state
            )
         (lift-code-segment loop-depth
                            generated-events
                            next-loop-num
                            this-loop-offsets-no-header
                            loop-body-assumptions
                            extra-rules
                            remove-rules
                            rules-to-monitor
                            loop-alist
                            print
                            measure-alist
                            base-name
                            lifter-rules
                            state
                           ))
        ((when erp)
         (mv erp nil nil nil state))
        (- (cw "(Loop body DAG: ~x0)~%" loop-body-dag))
        (loop-body-term (dag-to-term loop-body-dag)) ;todo: watch for blow-up here
        (- (cw "(Loop body term: ~x0)~%" (untranslate loop-body-term nil (w state))))
        ((when (member-eq 'run-until-exit-segment-or-hit-loop-header
                          (dag-fns loop-body-dag)))
         (cw "~X01" (dag-to-term loop-body-dag) nil) ;todo: can blow up
         (er hard 'lift-loop "Symbolic execution for loop body did not finish; a call of run-until-exit-segment-or-hit-loop-header remains in the DAG (see above).")
         (mv erp nil nil nil state))
        ;; Figure out which leaves returned to the loop top, etc.:
        ;; TODO: Maybe use dags instead of terms here
        ((mv erp one-rep-term exit-term exit-test-term state)
         (analyze-loop-body loop-body-term loop-top-pc-term '(xr ':rgf '4 x86_1) extra-rules remove-rules lifter-rules assumptions state))
        ((when erp) (mv erp nil nil nil state))
        (- (cw "(one-rep-term: ~x0)~%" (untranslate one-rep-term nil (w state))))
        (- (cw "(exit-term: ~x0)~%" (untranslate exit-term nil (w state))))
        (- (cw "(exit-test-term: ~x0)~%" (untranslate exit-test-term nil (w state))))
        (- (cw "(Attempting to prove invariants:~%"))
        ;; TODO: No need to try to prove invariants that don't mention state-var.
        ((mv erp
             & ;proved-invariants
             failed-invariants
             state)
         ;; TODO: In general, we may need to assume the negation of the exit test here:
         (prove-invariants-preserved loop-invariants
                                     state-var
                                     one-rep-term
                                     loop-invariants ;assume the invariants hold on the state-var
                                     extra-rules
                                     remove-rules
                                     rules-to-monitor
                                     nil
                                     nil
                                     lifter-rules
                                     state))
        ((when erp) (mv erp nil nil nil state))
        ((when failed-invariants) ;todo: be more flexible: throw out failed invariants and try again
         (prog2$ (er hard? 'lift-loop "An invariant failed (see above).")
                 (mv (erp-t) nil nil nil state)))
        (- (cw "All invariants proved)~%"))

        ;; Process the state updates done by the loop body:
        ((mv okp xw-triples write-triples flag-pairs)
         (check-and-split-one-rep-term one-rep-term state-var))
        ((if (not okp))
         (prog2$ (er hard? 'lift-loop "Bad one rep term: ~x0." one-rep-term)
                 (mv (erp-t) nil nil nil state)))
        (- (cw "(xw-triples: ~x0.)~%" xw-triples))
        (- (cw "(write-triples: ~x0)~%" write-triples))
        (- (cw "(flag-pairs: ~x0)~%" flag-pairs))
        ((when (not (no-duplicatesp (get-xw-pairs xw-triples))))
         (er hard 'lift-loop "Duplicates detected in xw calls: ~x0." xw-triples)
         (mv (erp-t) nil nil nil state))
        ((when (not (no-duplicatesp (get-flag-names flag-pairs))))
         (er hard 'lift-loop "Duplicates detected in flag updates: ~x0." flag-pairs)
         (mv (erp-t) nil nil nil state))
        ;; Writes are harder (have to show unchangedness and lack of aliasing):

        ;(write-pairs (get-write-pairs write-triples))
        (write-addresses (get-write-addresses write-triples))

        (- (cw "(Proving that ~x0 addresses are unchanged:~%" (len write-addresses))) ;todo: also throw in read-addresses here!
        ((mv erp res state)
         (ensure-addresses-unchanged-by-body write-addresses ;todo: what vars are in these?
                                             one-rep-term
                                             state-var
                                             ;; assumptions
                                             (set-difference-eq
                                              (append extra-rules (lifter-rules2) lifter-rules)
                                              remove-rules)
                                             state))
        ((when erp) (mv erp nil nil nil state))
        ((when (not res))
         (er hard 'lift-loop "Failed to show that addresses are unchanged: ~x0." write-addresses)
         (mv (erp-t) nil nil nil state))
        (- (cw "Done proving that addresses are unchanged.)~%"))


        ;; Make the params:
        (next-param-number 0)

        ;; UPDATED-STATE-TERM represents writing the return values of the loop
        ;; function back into the state after the loop. It is a nest of updates
        ;; to :initial-loop-top-state where the values written are components of
        ;; the variable :loop-function-result, which will be replaced below by
        ;; the call of the loop function.
        (updated-state-term :initial-loop-top-state)

        ;;  The paramnum-update-alist maps each paramnum to a term
        ;;  representing the updated value of that param after the
        ;;  loop body (in terms of what state-var, previous state-vars, and inputs)
        (paramnum-update-alist nil)
        ;; The paramnum-extractor-alist maps each paramnum to a term
        ;; representing how to extract it from :initial-loop-top-state. May also
        ;; mention previous state-vars (and inputs?) since heap
        ;; addresses may mention those.
        (paramnum-extractor-alist nil)
        ;;maps paramnums to their "names" for debugging.
        (paramnum-name-alist nil)

        (- (cw "(Making loop params for XW triples:~%"))
        ((mv next-param-number
             updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (make-loop-parameters-for-xw-triples xw-triples next-param-number updated-state-term
                                              paramnum-update-alist paramnum-extractor-alist paramnum-name-alist))
        (- (cw "Done.)~%"))

        (- (cw "(Making loop params for write triples:~%"))
        ((mv next-param-number
             updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (make-loop-parameters-for-write-triples write-triples next-param-number updated-state-term
                                                 paramnum-update-alist paramnum-extractor-alist paramnum-name-alist))
        (- (cw "Done.)~%"))

        (- (cw "(Making loop params for flag pairs:~%"))
        ((mv next-param-number
             updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (make-loop-parameters-for-flag-pairs flag-pairs next-param-number updated-state-term
                                              paramnum-update-alist paramnum-extractor-alist paramnum-name-alist))
        (- (cw "Done.)~%"))

        (- (cw "(Making read-only loop params:~%"))
        ((mv next-param-number
             updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (make-read-only-parameters paramnum-update-alist next-param-number updated-state-term
                                    paramnum-update-alist paramnum-extractor-alist paramnum-name-alist
                                    state-var
                                    nil))
        (- (cw "Done.)~%"))

        ;; Add params for any additional read-only values read in the exit-test-term:
        (- (cw "(Making params for read-only values in the exit-term term:%"))
        ((mv & ;next-param-number
             updated-state-term paramnum-update-alist paramnum-extractor-alist paramnum-name-alist)
         (make-read-only-parameters-for-expr exit-test-term
                                             next-param-number
                                             updated-state-term
                                             paramnum-update-alist
                                             paramnum-extractor-alist
                                             paramnum-name-alist
                                             state-var
                                             nil))
        (- (cw "Done.)~%"))

        (paramnum-update-alist (reverse paramnum-update-alist))
        (paramnum-extractor-alist (reverse paramnum-extractor-alist))
        (paramnum-name-alist (reverse paramnum-name-alist))

        (- (cw "(updated-state-term: ~X01)~%" updated-state-term nil))
        (- (cw "(param updates: ~X01)~%" paramnum-update-alist nil))
        (- (cw "(param extractors: ~X01)~%" paramnum-extractor-alist nil))
        (- (cw "(param names: ~X01)~%" paramnum-name-alist nil))
        ;; TODO: Think about the order of param-names.  What do we prefer?

        ;; Check for aliasing among the params:
        (- (cw "(Proving lack of aliasing:~%"))
        (param-mem-pairs (get-mem-pairs (strip-cdrs paramnum-extractor-alist)))
        (- (cw "(Param-mem-pairs: ~x0)~%" param-mem-pairs))
        ((mv erp res state)
         (no-overlap-in-write-pairs param-mem-pairs
                                    loop-invariants
                                    (append (lifter-rules2)
                                            lifter-rules)
                                    state))
        ((when erp) (mv erp nil nil nil state))
        ((when (not res))
         (er hard 'lift-loop "Overlap detected in writes: ~x0." write-triples)
         (mv (erp-t) nil nil nil state))
        (- (cw "Done proving lack of aliasing)~%"))

        (loop-fn (pack-in-package-of-first-symbol base-name '-loop- this-loop-num))

        ;; Rewrite the update functions and exit test in terms of params:
        (param-names (strip-cdrs paramnum-name-alist))
        (param-update-terms (strip-cdrs paramnum-update-alist))
        ;(param-update-term (make-cons-nest param-update-terms))
        ;; Now we have to replace expressions in this that are over state-var with expressions over params:
        (replacement-alist (make-replacement-alist paramnum-extractor-alist paramnum-name-alist state-var))
        ;; (- (cw "(Replacement-alist: ~X01)~%" replacement-alist nil))
        (param-update-terms (acl2::replace-in-terms param-update-terms replacement-alist))
        (- (cw "(param-update-terms: ~x0)~%" param-update-terms))
        ;; Same for the exit test
        (exit-test-term (acl2::replace-in-term exit-test-term replacement-alist))

        (exit-test-vars (acl2::get-vars-from-term exit-test-term))
        ((when (not (subsetp-eq exit-test-vars
                                     param-names ;'(params)
                                     )))
         (er hard 'lift-loop "Unexpected vars (~x2) in exit-test-term: ~X01." exit-test-term nil
             (set-difference-eq exit-test-vars param-names))
         (mv (erp-t) nil nil nil state))
        ((when (not (subsetp-eq (acl2::get-vars-from-terms param-update-terms)
                                     param-names ;'(params)
                                     )))
         (er hard 'lift-loop "Unexpected vars in param-update-terms: ~X01." param-update-terms nil)
         (mv (erp-t) nil nil nil state))

        ;; TODO: What vars can be in the exit-term?  maybe we don't have to check anything.  that happens outside the loop function...

        (measure (if (eq :skip measure-alist)
                     :skip
                   (if (assoc pc-offset measure-alist)
                       (lookup pc-offset measure-alist) ;might be :skip
                     (er hard? 'lift-loop "No measure (not even :skip) given for ~x0" loop-fn))))
        (defun-body `(if ,exit-test-term
                         (list ,@param-names)  ;todo: don't return the read-only params
                       (,loop-fn ,@param-update-terms)))
        ;; TODO: Consider letifying to avoid repeated-calls to nested loops:
        (defun (if (eq :skip measure)
                   (prog2$ (cw "(WARNING: Skipping termination proof for ~x0.)~%" loop-fn)
                           `(skip-proofs
                             (defun ,loop-fn (,@param-names)
                               ,defun-body
                               )))
                 `(defun ,loop-fn (,@param-names)
                    (declare (xargs :measure ,measure))
                    ,defun-body)))
        (state (submit-event defun state))

        ;; TODO: Need to prove that x86p is preserved... ugh... example: show that nth 0 of the loop function is a SIGNED-BYTE-P '64.

        (- (cw "(Splicing in the loop function:~%"))
        ;; Build the new DAG that includes the effect of the loop
;        (initial-params-terms (strip-cdrs paramnum-extractor-alist)) ;these are over :INITIAL-LOOP-TOP-STATE and perhaps previous state vars and inputs (may occur in addresses)
        (initial-params-terms (make-initial-params-terms paramnum-extractor-alist paramnum-name-alist param-update-terms))
        ;(initial-params-term (make-cons-nest initial-params-terms))
        (loop-function-call-term `(,loop-fn ,@initial-params-terms))
        ;; Simplify it (applies read over write rules):
        ((mv erp loop-function-call-dag state)
         (acl2::simp-term loop-function-call-term :rules (append (lifter-rules2) lifter-rules)))
        ((when erp) (mv erp nil nil nil state))
        ;; Write the values computed by the loop back into the state:
        ((mv erp new-state-dag) (compose-term-and-dag updated-state-term :loop-function-result loop-function-call-dag))
        ((when erp) (mv erp nil nil nil state))
        ;; Apply the effect of the exit branches:
        ((mv erp new-state-dag) (compose-term-and-dag exit-term state-var new-state-dag))
        ((when erp) (mv erp nil nil nil state))
        ;; Apply the effect of the loop to the initial loop-top-state-dag:
        ((mv erp new-state-dag) (compose-dags new-state-dag :initial-loop-top-state loop-top-state-dag t))
        ((when erp) (mv erp nil nil nil state))
        ;; Simplify again:
        ((mv erp new-state-dag state)
         (acl2::simp-dag new-state-dag
                         :rules (append (lifter-rules2) lifter-rules)
                         :print nil
                         :monitor '(;;x86isa::set-flag-set-flag-same
                                    ;;x86isa::x86p-set-flag
                                    ;;x86p-of-write
                                    ;;x86isa::x86p-xw
                                    )))
        ((when erp) (mv erp nil nil nil state))
        (- (cw "Done Splicing in the loop function)~%"))
        (generated-events (append generated-events
                                  (list `(progn ,defun))))
        (- (cw "Done lifting loop ~x0 (depth ~x1)).~%" this-loop-num loop-depth)))
     (mv nil new-state-dag generated-events next-loop-num state)))

 ;; STATE-TERM is a myif-nest some of whose leaves are standing at loop headers.
 ;; Decompiles loops at the leaves of STATE-TERM that are standing at loop headers. Leaves other leaves alone.
 ;; Returns (mv erp changep dag generated-events next-loop-num state).
 (defun lift-loop-leaves (state-term ;todo: process dags directly instead of terms?
                          changep    ;an accumulator
                          loop-depth ;0 if not in a loop, yet, 1 for the body of the first loop (2 or greater for the body of a nested loop)
                          generated-events
                          next-loop-num
                          segment-offsets
                          assumptions ; over x86_0 and perhaps other vars (see the Essay on Variables)
                          extra-rules ; rules to enable
                          remove-rules
                          rules-to-monitor ; rules to monitor
                          loop-alist ; maps loop headers (PC offsets) to lists of PC offsets in the corresponding loops
                          print
                          measure-alist
                          base-name
                          lifter-rules
                          state
                          )
   (declare (xargs :stobjs (state)
                   :mode :program
                   :guard (and (posp loop-depth)
                               (pseudo-term-listp assumptions)
                               ;;(pseudo-termp original-rsp-term)
                               (symbol-listp extra-rules)
                               (symbol-listp remove-rules)
                               (symbol-listp rules-to-monitor)
                               (loop-alistp loop-alist)
                               (symbolp base-name)
                               ;; todo: strengthen:
                               (or (eq :skip measure-alist)
                                   (alistp measure-alist)))))
   (if (not (consp state-term)) ;is this case possible?
       (mv-let (erp state-dag)
         (dagify-term2 state-term)
         (if erp
             (mv erp nil nil nil nil state)
           (mv (erp-nil) changep state-dag generated-events next-loop-num state)))
     (if (eq 'myif (ffn-symb state-term)) ;todo: pass the test as an asumption?
         (b* ((- (cw "(Handling a myif with test ~x0.)~%" (farg1 state-term)))
              ((mv erp changep then-branch-dag generated-events next-loop-num state)
               (lift-loop-leaves (farg2 state-term)
                                 changep
                                 loop-depth
                                 generated-events
                                 next-loop-num
                                 segment-offsets
                                 assumptions
                                 extra-rules
                                 remove-rules
                                 rules-to-monitor
                                 loop-alist
                                 print
                                 measure-alist
                                 base-name
                                 lifter-rules
                                 state
                                 ))
              ((when erp) (mv erp nil nil nil nil state))
              ((mv erp changep else-branch-dag generated-events next-loop-num state)
               (lift-loop-leaves (farg3 state-term)
                                 changep
                                 loop-depth
                                 generated-events
                                 next-loop-num
                                 segment-offsets
                                 assumptions
                                 extra-rules
                                 remove-rules
                                 rules-to-monitor
                                 loop-alist
                                 print
                                 measure-alist
                                 base-name
                                 lifter-rules
                                 state
                                 ))
              ((when erp) (mv erp nil nil nil nil state))
              (all-state-nums (acl2::ints-in-range 0 loop-depth))
              (all-state-vars (ACL2::PACK-IN-PACKAGE-OF-base-SYMBOL-list 'x86_ all-state-nums)) ;could pass these in
              (result-dag ;(mv erp result-dag)
               ;; todo: this is a non-array function:
               (compose-term-and-dags `(myif ,(farg1 state-term)
                                             :then-part
                                             :else-part)
                                      (acons :then-part then-branch-dag
                                             (acons :else-part else-branch-dag
                                                    nil))
                                      :extra-vars (cons 'text-offset all-state-vars)))
              ;((when erp) (mv erp nil nil nil nil state))
              )
           (mv nil changep result-dag generated-events next-loop-num state))
       ;; Not a myif, so test whether we have exited the segment:
       ;; TODO: Begin by comparing the stack height?
       (b* (((mv erp exitedp state)
             (b* ( ;; Extract the PC:
                  (- (cw "(Checking the PC.)~%"))
                  (- (cw "(State term is ~x0)~%" state-term))
                  ((mv erp state-dag)
                   (dagify-term2 state-term))
                  ((when erp) (mv erp nil state))
                  ((mv erp pc-dag state)
                   (extract-pc-dag state-dag
                                   assumptions
                                   extra-rules
                                   remove-rules
                                   lifter-rules
                                   state
                                   ))
                  ((when erp) (mv erp nil state))
                  (pc-term (dag-to-term pc-dag))
                  (- (cw "(PC term is ~x0.)~%" pc-dag)))
               (if (equal pc-term
                          ;; We've jumped to the return address of the main subroutine, so we've exited the segment:
                          ;; TODO: Check this:
                          '(READ '8 (XR ':RGF '4 X86_0) X86_0))
                   (mv (erp-nil) t state)
                 (let ((pc-offset (get-added-offset pc-term 'text-offset)))
                   (if (member pc-offset segment-offsets)
                       (mv (erp-nil) nil state)
                     (mv (erp-nil) t state)))))))
         (if erp
             (mv erp nil nil nil nil state)
           (if exitedp
               (mv-let (erp state-dag)
                 (dagify-term2 state-term)
                 (if erp
                     (mv erp nil nil nil nil state)
                   ;; We have exited the code segment, so there is no loop to lift:
                   (mv (erp-nil) changep state-dag generated-events next-loop-num state)))
             (b* (((mv erp state-dag0) (dagify-term2 state-term))
                  ((when erp) (mv erp nil nil nil nil state))
                  ((mv erp state-dag generated-events next-loop-num state)
                   ;; TODO: Do we need to check the stack height (maybe only if we are going to support recursion)?
                   ;; We are still in the code segment, so we must be at a loop top:
                   (lift-loop state-dag0
                              (+ 1 loop-depth)
                              generated-events
                              next-loop-num
                              assumptions
                              ;;rsp-term
                              extra-rules
                              remove-rules
                              rules-to-monitor
                              loop-alist
                              print
                              measure-alist
                              base-name
                              lifter-rules
                              state
                              ))
                  ((when erp) (mv erp nil nil nil nil state)))
               (mv (erp-nil)
                   t ;we made a change
                   state-dag generated-events next-loop-num state))))))))

 ;; Repeatedly push forward and lift loops at leaves.
 ;; Returns (mv erp new-state-dag generated-events next-loop-num state).
 (defun lift-code-segment-aux (state-dag
                               rsp-dag
                               all-state-vars
                               loop-depth
                               generated-events
                               next-loop-num
                               segment-offsets
                               assumptions
                               ;; rsp-term
                               extra-rules
                               remove-rules
                               rules-to-monitor
                               loop-alist
                               print
                               measure-alist
                               base-name
                               lifter-rules
                               state
                              )
   (declare (xargs :mode :program
                   :guard (and (natp loop-depth)
                               (posp next-loop-num)
                               (symbolp base-name)
                               (loop-alistp loop-alist)
                               (nat-listp segment-offsets)
                               ;; todo: strengthen:
                               (or (eq :skip measure-alist)
                                   (alistp measure-alist)))
                   :stobjs (state)))
   (b* ((segment-pc-terms (relative-pc-terms segment-offsets 'text-offset))
        (all-loop-header-offsets (strip-cars loop-alist))
        (all-loop-header-pc-terms (relative-pc-terms all-loop-header-offsets 'text-offset))
        ;; TODO: Do we need to pass the RSP here, or is it enough to check whether we are in the code segment?
        (dag-to-run ;(mv erp dag-to-run)
         (compose-term-and-dags `(run-until-exit-segment-or-hit-loop-header :starting-rsp
                                                                                       ,(make-cons-nest segment-pc-terms)
                                                                                       ,(make-cons-nest all-loop-header-pc-terms)
                                                                                       :state-dag)
                                           (acons :starting-rsp rsp-dag (acons :state-dag state-dag nil))
                                           :extra-vars (cons 'text-offset all-state-vars)))
        ;((when erp) (mv erp nil nil nil state))
        (- (cw "(DAG to symbolically execute: ~x0)~%" dag-to-run))
        ;; Perform the symbolic execution:
        ;; TODO: Suppress printing of result here?:
        ;; TODO: Add support for printing a combined summary at the end of all rewrite phases...
        ((mv erp state-dag state)
         (simp-dag dag-to-run
                   :rules (set-difference-eq
                           (append (lifter-rules2)
                                   lifter-rules
                                   (symbolic-execution-rules)
                                   extra-rules)
                           remove-rules)
                   :assumptions assumptions
                   :monitor (append '( ;read-in-terms-of-nth-and-pos-eric
                                      get-flag-of-set-flag
                                      )
                                    rules-to-monitor)
                   :print print
                   :simplify-xorsp nil
                   :check-inputs nil))
        ((when erp) (mv erp nil nil nil state))
        ;; Check for problems:
        ((when (member-eq 'run-until-exit-segment-or-hit-loop-header
                          (dag-fns state-dag)))
         (er hard 'lift-code-segment "run-until-exit-segment-or-hit-loop-header remains in the DAG.")
         (mv (erp-t) nil nil nil state))
        ;; Print the result of running:
        (- (cw "(DAG after running: ~x0)~%" state-dag))
        (state-term (dag-to-term state-dag))
        (- (cw "(Term after running: ~x0)~%" state-term))
        ;; Now, handle any loops:
        ((mv erp changep state-dag generated-events next-loop-num state)
         (lift-loop-leaves state-term
                           nil ;changep
                           loop-depth
                           generated-events
                           next-loop-num
                           segment-offsets
                           assumptions
                           ;; rsp-term
                           extra-rules
                           remove-rules
                           rules-to-monitor
                           loop-alist
                           print
                           measure-alist
                           base-name
                           lifter-rules
                           state
                          ))
        ((when erp) (mv erp nil nil nil state)))
     (if changep
         (lift-code-segment-aux state-dag
                                rsp-dag
                                all-state-vars
                                loop-depth
                                generated-events
                                next-loop-num
                                segment-offsets
                                assumptions
                                ;; rsp-term
                                extra-rules
                                remove-rules
                                rules-to-monitor
                                loop-alist
                                print
                                measure-alist
                                base-name
                                lifter-rules
                                state
                               )
       ;; No loops were lifted, so we are done
       (mv nil state-dag generated-events next-loop-num state))))

 ;; TODO: Fix/improve printing done when simplifying dags here: Returns (mv erp
 ;; dag generated-events next-loop-num state).  The state should already be
 ;; stepped past the loop header (because we stop symbolic execution when we
 ;; hit the loop header again?).  !! For now, this assumes that the code
 ;; segment being lifted is at the start of the routine, preceding the
 ;; routine's single loop.  We always step the state at least once.
 (defun lift-code-segment ( ;initial-state-dag ;over the var x86_0 and perhaps other vars representing inputs (see the Essay on Variables) -- always just the initial-state-dag in var form?
                           loop-depth ;0 if not in a loop, yet, 1 for the body of the first loop (2 or greater for the body of a nested loop)
                           generated-events
                           next-loop-num
                           segment-offsets ;;these represent PCs of the code segment to lift (if it's a loop body, should not include the loop header)
                           assumptions ; over x86_0 and perhaps other vars (see the Essay on Variables)
                           extra-rules ; rules to enable
                           remove-rules ; rules to disable
                           rules-to-monitor ; rules to monitor
;                          starting-rsp ;tells us the stack height of the current subroutine
                           loop-alist ; maps loop headers (PC offsets) to lists of PC offsets in the corresponding loops
                           print
                           measure-alist ;may be :skip
                           base-name
                           lifter-rules
                           state
                          )
   (declare (xargs :mode :program
                   :guard (and (natp loop-depth)
                               (posp next-loop-num)
                               (symbolp base-name)
                               (loop-alistp loop-alist)
                               (nat-listp segment-offsets)
                               ;; todo: strengthen:
                               (or (eq :skip measure-alist)
                                   (alistp measure-alist)))
                   :stobjs (state)))
   (b* ((- (cw "(Unsimplified assumptions for lifting: ~x0)~%" assumptions)) ;todo: untranslate these and other things that get printed
        ;; Simplify the assumptions: TODO: Pull this out into the caller?
        ((mv erp rule-alist)  ;todo: include the extra-rules?
         (make-rule-alist (append '(x86isa::rip) ;why was this not needed before?
                                  (assumption-simplification-rules))
                          (w state)))
        ((when erp) (mv erp nil nil nil state))
        ((mv erp assumptions state)
         (simplify-terms-using-each-other assumptions rule-alist))
        ((when erp) (mv erp nil nil nil state))
        (- (cw "(Simplified assumptions for lifting: ~x0)~%" assumptions))
        (state-var (pack-in-package-of-symbol 'x86 'x86_ loop-depth))
        ((mv erp state-dag) (dagify-term2 state-var))
        ((when erp) (mv erp nil nil nil state))

        ;; Extract the RSP:
        ((mv erp rsp-dag state)
         (extract-rsp-dag extra-rules
                          remove-rules
                          state-dag
                          lifter-rules
                          state
                          ))
        ((when erp) (mv erp nil nil nil state))
        (rsp-term (dag-to-term rsp-dag))
        (- (cw "(RSP is ~x0.)~%" rsp-term))
        ;; Run until all leaves are at a loop header or have exited the
        ;; segment (perhaps by exiting the subroutine):
        (previous-state-nums (acl2::ints-in-range 0 (+ -1 loop-depth)))
        (previous-state-vars (acl2::my-pack-listb 'x86_ previous-state-nums)) ;could pass these in
        (all-state-vars (cons state-var previous-state-vars))
        ;; Step once to start (e.g., to get past the loop header, if the segment is a loop body):
        (state-dag ;(mv erp state-dag)
         (compose-term-and-dags '(x86-fetch-decode-execute :state-dag) (acons :state-dag state-dag nil)))
;        ((when erp) (mv erp nil nil nil state))
        ;; Now repeatedly push forward and lift loops:
        ((mv erp new-state-dag generated-events ;;generated-rules
             next-loop-num state)
         (lift-code-segment-aux state-dag
                                rsp-dag
                                all-state-vars
                                loop-depth
                                generated-events
                                next-loop-num
                                segment-offsets
                                assumptions
                                ;; rsp-term
                                extra-rules
                                remove-rules
                                rules-to-monitor
                                loop-alist
                                print
                                measure-alist
                                base-name
                                lifter-rules
                                state
                               ))
        ((when erp) (mv erp nil nil nil state))
        (- (cw "(DAG after code segment: ~x0)~%" new-state-dag)))
     (mv nil ;no error
         new-state-dag
         generated-events
         ;; nil          ; generated rules
         next-loop-num
         state))))

;; Returns (mv erp event state)
(defun lift-subroutine-fn (lifted-name
                           subroutine-name
                           parsed-executable
                           stack-slots-needed
                           subroutine-length ;todo: drop this (would need to support :all for the segment-pcs?)
                           loop-alist
                           extra-rules
                           remove-rules
                           produce-theorem
                           ;;output
                           user-assumptions ;;These should be over the variable x86_0 and perhaps additional vars (but not x86_1, etc.)
                           non-executable
                           ;;restrict-theory
                           rules-to-monitor
                           print
                           measures
                           whole-form
                           state
                          )
  (declare (xargs :stobjs (state)
                  :guard (and (symbolp lifted-name)
                              (stringp subroutine-name)
;                              (output-indicatorp output)
                              (booleanp non-executable)
                              (symbol-listp rules-to-monitor))
                  :mode :program)
           (ignore produce-theorem non-executable))
  (b* ( ;; Check whether this call to the lifter has already been made:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       (- (cw "(Lifting subroutine ~x0:~%" subroutine-name))
       ;; Check user input:
       ((when (not (natp stack-slots-needed)))
        (prog2$ (er hard 'lift-subroutine-fn "Bad value for stack-slots-needed: ~x0" stack-slots-needed)
                (mv (erp-t) nil state)))
       ((when (not (natp subroutine-length)))
        (prog2$ (er hard 'lift-subroutine-fn "Bad value for subroutine-length: ~x0" subroutine-length)
                (mv (erp-t) nil state)))
       ((when (not (and (loop-alistp loop-alist)
                        ;(all-< loop-header-offset subroutine-length)
                        )))
        (prog2$ (er hard 'lift-subroutine-fn "Bad value for loop-alist: ~x0" loop-alist)
                (mv (erp-t) nil state)))

       ;; Generate assumptions for lifting:
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (user-assumptions (acl2::translate-terms user-assumptions 'lift-subroutine-fn (w state)))
       ;; assumptions (these get simplified below to put them into normal form):
       (assumptions (if (eq :mach-o-64 executable-type)
                        (cons `(standard-assumptions-mach-o-64 ',subroutine-name
                                                             ',parsed-executable
                                                             ',stack-slots-needed
                                                             text-offset
                                                             x86_0)
                              user-assumptions)
                      (if (eq :pe-64 executable-type) ;; TODO: Support :pe-32
                          (cons `(standard-assumptions-pe-64 ',subroutine-name
                                                                   ',parsed-executable
                                                                   ',stack-slots-needed
                                                                   text-offset
                                                                   x86_0)
                                user-assumptions)
                        user-assumptions)))
       ;; TODO: Not all of these are necessarily PCs (should we give a range?):
       ;; TODO: What about offset 0?
       (segment-offsets (offsets-up-to (- subroutine-length 1)))
       (measure-alist (if (eq :skip measures)
                          :skip
                        (doublets-to-alist measures)))
       (lifter-rules (if (member-eq executable-type '(:pe-32 :mach-o-32))
                         (lifter-rules32)
                       (lifter-rules64)))
       ((mv erp dag events
            ;; & ;;rules
            & ;;next-loop-num
            state)
        (lift-code-segment
;         initial-state-dag
         0 ;loop-depth;
         nil ;generated-events
         1 ;next-loop-num
         segment-offsets
         assumptions
         extra-rules
         remove-rules
         rules-to-monitor
         loop-alist
         print
         measure-alist
         lifted-name
         lifter-rules
         state
         ))
       ((when erp) (mv erp nil state))
       ;; Extract the output (TODO: generalize!)
       ((mv erp output-dag) (compose-term-and-dag '(xr ':rgf '0 :dag) :dag dag))
       ((when erp) (mv erp nil state))
       (- (cw "(output-dag: ~x0)~%" output-dag))
       ((mv erp output-dag state)
        (simp-dag output-dag
                  :rules (set-difference-eq
                          (append (lifter-rules2)
                                  lifter-rules
                                  (symbolic-execution-rules)
                                  extra-rules)
                          remove-rules)
                  :assumptions assumptions
                  :monitor rules-to-monitor
                  :print print
                  :simplify-xorsp nil
                  :check-inputs nil))
       ((when erp) (mv erp nil state))
       (output-term (dag-to-term output-dag))
       ;; TODO: Generalize:
       (output-term (replace-components-of-initial-state-in-term output-term))
       ;; (output-term (acl2::replace-in-term output-term
       ;;                                     '(((xr ':rgf '0 x86_0) . rax)
       ;;                                       ((xr ':rgf '1 x86_0) . rcx)
       ;;                                       ((xr ':rgf '2 x86_0) . rdx)
       ;;                                       ((xr ':rgf '3 x86_0) . rbx)
       ;;                                       ((xr ':rgf '4 x86_0) . rsp) ;todo: should not occur?
       ;;                                       ((xr ':rgf '5 x86_0) . rbp) ;todo: should not occur?
       ;;                                       ((xr ':rgf '6 x86_0) . rsi)
       ;;                                       ((xr ':rgf '7 x86_0) . rdi)
       ;;                                       ((xr ':rgf '8 x86_0) . r8)
       ;;                                       ((xr ':rgf '9 x86_0) . r9)
       ;;                                       ((xr ':rgf '10 x86_0) . r10)
       ;;                                       ((xr ':rgf '11 x86_0) . r11)
       ;;                                       ((xr ':rgf '12 x86_0) . r12)
       ;;                                       ((xr ':rgf '13 x86_0) . r13)
       ;;                                       ((xr ':rgf '14 x86_0) . r14)
       ;;                                       ((xr ':rgf '15 x86_0) . r15)
       ;;                                       ((xr ':undef '0 x86_0) . undef)
       ;;                                       ((get-flag '0 x86_0) . flag0) ;todo: get-flag no longer takes numbers to indicate the flags
       ;;                                       ((get-flag '2 x86_0) . flag2)
       ;;                                       ((get-flag '4 x86_0) . flag4)
       ;;                                       ((get-flag '6 x86_0) . flag6)
       ;;                                       ((get-flag '7 x86_0) . flag7)
       ;;                                       ((get-flag '11 x86_0) . flag11)
       ;;                                       ;; TODO: Does flag 12 take 2 bits?
       ;;                                       ;; TODO: Handle this better:
       ;;                                       ((READ '4 (BINARY-+ '-28 (XR ':RGF '4 X86_0)) X86_0)
       ;;                                        .
       ;;                                        var28))))
       ;; TODO: Put these in a better order:
       (vars (acl2::get-vars-from-term output-term)) ;todo: check that x86_0 does not remain
       ((when (member-eq 'x86_0 vars))
        (er hard? 'lift-subroutine-fn "The variable X86_0 remains after replacing state components in the output-term: ~X01." output-term nil)
        (mv (erp-t) nil state))
       (defun `(defun ,lifted-name (,@vars)
                 ,output-term))
       (event `(progn ,@events
                      ,defun))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event)))
       (- (cw "Done Lifting subroutine ~x0)~%" subroutine-name))
       )
    (mv erp event state)))

(defmacro lift-subroutine (&whole
                           whole-form
                           lifted-name ;the name to use for the function created by the lifter
                           subroutine-name
                           parsed-executable
                           stack-slots-needed
                           subroutine-length
                           loop-alist ;offsets (from start of method) of loops, paired with offset lists for their bodies
                           &key
                           (extra-rules 'nil)
                           (remove-rules 'nil)
                           (produce-theorem 't) ;todo: not used.
                           ;;output
                           (assumptions 'nil) ;TODO: Translate these
                           (non-executable 'nil)
                           ;;restrict-theory
                           (monitor 'nil)
                           (print 't)
                           (measures ':skip) ;; :skip or a list of doublets indexed by nats (PC offsets)
                           )
  `(make-event (lift-subroutine-fn ',lifted-name
                                   ',subroutine-name
                                   ,parsed-executable
                                   ',stack-slots-needed
                                   ',subroutine-length
                                   ',loop-alist
                                   ,extra-rules
                                   ,remove-rules
                                   ',produce-theorem
                                   ;;output
                                   ,assumptions ;TODO: Translate these
                                   ',non-executable
                                   ;;restrict-theory
                                   ,monitor
                                   ',print
                                   ',measures
                                   ',whole-form
                                   state
                                  )))

;(defttag t)
;(remove-untouchable acl2::verify-termination-on-raw-program-okp nil)
;(assign acl2::verify-termination-on-raw-program-okp t)
;; (include-book "kestrel/utilities/verify-guards-program" :dir :system)
;; (acl2::verify-guards-program x::lift-loop)
