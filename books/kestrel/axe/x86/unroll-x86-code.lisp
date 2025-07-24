; An unrolling lifter xfor x86 code (based on Axe)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Two approaches: 1. Use X86 as the only variable and get back a term
;; over the single variable X86 that captures the effect of the code.
;; 2. Introduce variables such as X and Y for the inputs and get back
;; a term over x86 and those variables.  This may make it easier to
;; state assumptions (since they can mention X and Y).  We use the
;; second approach here for now.

(include-book "x86-rules")
(include-book "../bitops-rules")
(include-book "../logops-rules-axe")
(include-book "kestrel/x86/if-lowering" :dir :system)
(include-book "kestrel/x86/read-over-write-rules" :dir :system)
(include-book "kestrel/x86/read-over-write-rules32" :dir :system)
(include-book "kestrel/x86/read-over-write-rules64" :dir :system)
(include-book "kestrel/x86/write-over-write-rules" :dir :system)
(include-book "kestrel/x86/write-over-write-rules32" :dir :system)
(include-book "kestrel/x86/write-over-write-rules64" :dir :system)
(include-book "kestrel/x86/x86-changes" :dir :system)
(include-book "kestrel/x86/tools/lifter-support" :dir :system)
(include-book "kestrel/x86/conditions" :dir :system)
(include-book "kestrel/x86/support" :dir :system)
(include-book "kestrel/x86/assumptions32" :dir :system)
(include-book "kestrel/x86/assumptions64" :dir :system)
(include-book "kestrel/x86/assumptions-new" :dir :system)
(include-book "kestrel/x86/floats" :dir :system)
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(include-book "kestrel/x86/separate" :dir :system)
(include-book "kestrel/x86/rflags" :dir :system)
(include-book "kestrel/x86/rflags2" :dir :system)
(include-book "kestrel/x86/support-bv" :dir :system)
(include-book "kestrel/x86/alt-defs" :dir :system)
(include-book "kestrel/x86/read-and-write2" :dir :system)
(include-book "rule-lists")
(include-book "kestrel/x86/run-until-return" :dir :system)
(include-book "kestrel/x86/run-until-return4" :dir :system)
(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "../rules-in-rule-lists")
;(include-book "../rules2") ;for BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-NON-CONST
;(include-book "../rules1") ;for ACL2::FORCE-OF-NON-NIL, etc.
(include-book "../equivalent-dags")
(include-book "../make-term-into-dag-basic")
;(include-book "../basic-rules")
(include-book "../step-increments")
(include-book "../dag-size")
(include-book "../dag-info")
(include-book "../rule-limits")
(include-book "../prune-dag-precisely")
(include-book "../prune-dag-approximately")
(include-book "../arithmetic-rules-axe")
(include-book "../convert-to-bv-rules-axe")
(include-book "../make-evaluator") ; for make-acons-nest ; todo: split out
(include-book "../supporting-functions") ; for get-non-built-in-supporting-fns-list
(include-book "../evaluator") ; todo: this book has skip-proofs
(include-book "rewriter-x86")
(include-book "kestrel/utilities/print-levels" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/if" :dir :system)
(include-book "kestrel/utilities/if-rules" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/booleans/booleans" :dir :system)
(include-book "kestrel/lists-light/take" :dir :system)
(include-book "kestrel/lists-light/nthcdr" :dir :system)
(include-book "kestrel/lists-light/append" :dir :system)
(include-book "kestrel/arithmetic-light/less-than" :dir :system)
(include-book "kestrel/arithmetic-light/fix" :dir :system)
(include-book "kestrel/bv/intro" :dir :system)
(include-book "kestrel/bv/rtl" :dir :system)
(include-book "kestrel/bv/convert-to-bv-rules" :dir :system)
(include-book "ihs/logops-lemmas" :dir :system) ;reduce? for logext-identity
(include-book "kestrel/arithmetic-light/mod" :dir :system)
(include-book "kestrel/arithmetic-light/ash" :dir :system) ; for ash-of-0, mentioned in a rule-list
(include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system) ; for +-OF-+-OF---SAME
(include-book "kestrel/bv/bvif2" :dir :system)
(include-book "kestrel/bv/ash" :dir :system)
(include-book "kestrel/bv/std" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/arithmetic-light/truncate" :dir :system)
(include-book "kestrel/utilities/real-time-since" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)
(local (include-book "kestrel/utilities/get-real-time" :dir :system))
(local (include-book "kestrel/utilities/doublet-listp" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))

(local (in-theory (disable intersection-equal)))

(local (in-theory (disable acl2::append-of-cons-arg1 acl2::append-of-cons))) ; bad?

(in-theory (disable str::coerce-to-list-removal)) ;todo

(acl2::ensure-rules-known (unroller-rules32))
(acl2::ensure-rules-known (unroller-rules64))
(acl2::ensure-rules-known (read-and-write-rules-bv))
(acl2::ensure-rules-known (read-and-write-rules-non-bv))
(acl2::ensure-rules-known (assumption-simplification-rules))
(acl2::ensure-rules-known (step-opener-rules32))
(acl2::ensure-rules-known (step-opener-rules64))

;; ;move
;; ;; We often want these for ACL2 proofs, but not for 64-bit examples
;; (deftheory 32-bit-reg-rules
;;   '(xw-becomes-set-eip
;;     xw-becomes-set-eax
;;     xw-becomes-set-ebx
;;     xw-becomes-set-ecx
;;     xw-becomes-set-edx
;;     xw-becomes-set-esp
;;     xw-becomes-set-ebp
;;     ;; introduce eip too?
;;     xr-becomes-eax
;;     xr-becomes-ebx
;;     xr-becomes-ecx
;;     xr-becomes-edx
;;     xr-becomes-ebp
;;     xr-becomes-esp)
;;   :redundant-okp t)

;; For safety:
(in-theory (disable (:executable-counterpart sys-call)))
(theory-invariant (not (active-runep '(:executable-counterpart sys-call))))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move this util

;; Recognizes an alist from functions to boolean-lists representing which arguments to print.
(defun elision-spec-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (symbolp (car entry))
           (boolean-listp (cdr entry))
           (elision-spec-alistp (rest alist))))))

(defthm elision-spec-alistp-forward-to-alistp
    (implies (elision-spec-alistp alist)
             (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable elision-spec-alistp alistp))))

;; Replace with :elided any large constant list arg that corresponds with nil in the bools.
;; todo: clarify the sense of t and nil (nil means maybe don't print)
(defun apply-elision-spec (args bools)
  (declare (xargs :guard (and (true-listp args)
                              (boolean-listp bools))))
  (if (endp args)
      nil
    (cons (if (and (not (first bools))
                   (let ((arg (first args)))
                     (and (myquotep arg)
                          (consp (unquote arg)) ; checks for a fairly long list
                          (<= 100 (len (unquote arg))))))
              :elided
            (first args))
          (apply-elision-spec (rest args) (rest bools)))))

(defund print-term-elided (term firstp elision-specs)
  (declare (xargs :guard (elision-spec-alistp elision-specs)))
  (let ((elision-spec (and (consp term)
                           (acl2::lookup-eq (car term) elision-specs))))
    (if elision-spec
        ;; eliding:
        (if (not (true-listp term))
            (er hard? 'print-term-elided "Bad term.")
          (if (not (= (len (rest term)) (len elision-spec))) ; todo: optimize via same-lengthp
              (er hard? 'print-term-elided "Length mismatch in elision spec, ~x0, for ~x1." elision-spec (car term))
            (let ((elided-term (cons (car term) (apply-elision-spec (rest term) elision-spec))))
              (if firstp
                  (cw "(~y0" elided-term)
                (cw " ~y0" elided-term)))))
      ;; not eliding (todo: share code with the above):
      (if firstp
          (cw "(~y0" term)
        (cw " ~y0" term)))))

;; Prints each of the TERMS, each starting with a space and ending with a newline.
;tail recursive, to support printing a large list
(defund print-terms-elided-aux (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (atom terms)
      nil
    (prog2$ (print-term-elided (first terms) nil elision-specs)
            (print-terms-elided-aux (rest terms) elision-specs))))

(defund print-terms-elided (terms elision-specs)
  (declare (xargs :guard (and (true-listp terms)
                              (elision-spec-alistp elision-specs))))
  (if (consp terms)
      (prog2$ (print-term-elided (first terms) t elision-specs) ;print the first element separately to put in an open paren
              (prog2$ (print-terms-elided-aux (rest terms) elision-specs)
                      (cw ")")))
    (cw "nil") ; or could do ()
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-assumptions-about (fns-to-remove terms)
  (declare (xargs :guard (and (symbol-listp fns-to-remove)
                              (pseudo-term-listp terms))))
  (if (endp terms)
      nil
    (let* ((term (first terms))
           ;; strip a NOT if present:
           (core-term (if (and (consp term)
                               (eq 'not (ffn-symb term))
                               (= 1 (len (fargs term))))
                          (farg1 term)
                        term)))
      (if (and (consp core-term)
               (member-eq (ffn-symb core-term) fns-to-remove))
          (remove-assumptions-about fns-to-remove (rest terms))
        (cons term (remove-assumptions-about fns-to-remove (rest terms)))))))

;; Sanity check:
(thm
  (subsetp-equal (remove-assumptions-about fns-to-remove terms)
                 terms)
  :hints (("Goal" :in-theory (enable remove-assumptions-about))))

(local
  (defthm pseudo-term-listp-of-remove-assumptions-about
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (remove-assumptions-about fns-to-remove terms)))
    :hints (("Goal" :in-theory (enable remove-assumptions-about)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These assumptions get removed during pruning (unlikely to help and lead to
;; messages about non-known-boolean literals being dropped)
;; TODO: Add more?
;; TODO: Include IF?
(defconst *non-stp-assumption-functions*
  '(canonical-address-p$inline
    program-at
    separate
    x86p
    cr0bits-p$inline
    cr4bits-p$inline
    alignment-checking-enabled-p
    app-view))

;move
;; ; TODO: Errors about program-only code
;; (defund untranslate-logic (term wrld state)
;;   (declare (xargs :guard (plist-worldp wrld)
;;                   :stobjs state))
;;   (magic-ev-fncall 'untranslate (list term nil wrld) state nil nil))

;; ;; Returns (mv erp result).
;; ;move
;; ; TODO: Errors about program-only code, e.g., for (acl2::translate-terms-logic '((+ x y)) 'ctx (w state) state)
;; (defund acl2::translate-terms-logic (terms ctx wrld state)
;;   (declare (xargs :guard (and (true-listp terms) ; untranslated
;;                                     (plist-worldp wrld))
;;                   :stobjs state))
;;   (mv-let (v1 v2)
;;       (magic-ev-fncall 'translate-terms (list terms ctx wrld) state nil nil)
;;     (if v1
;;         (mv (or v2 :error) nil)
;;         (mv nil v2))))

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(local (in-theory (disable set-print-base-radix
                           w
                           acl2::ilks-plist-worldp
                           acl2::myquotep
                           quotep
                           mv-nth)))

(local (in-theory (enable acl2::weak-dagp-when-pseudo-dagp
                          acl2::true-listp-when-symbol-listp-rewrite-unlimited)))

;move
(local
 (defthm w-of-set-print-base-radix
   (equal (w (set-print-base-radix base state))
          (w state))
   :hints (("Goal" :in-theory (enable set-print-base-radix w)))))

(local
  (defthm not-quotep-forward-to-not-myquotep
    (implies (not (quotep x))
             (not (myquotep x)))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable myquotep)))))

;; If these break, consider how to update the uses of these step-opener functions below:
(thm (equal (len (step-opener-rules32)) 1))
(thm (equal (len (step-opener-rules64)) 1))

(defconst *no-warn-ground-functions* '(feature-flag))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or an unsupported instruction is detected.
;; Returns (mv erp result-dag-or-quotep state).
(defun repeatedly-run (steps-done step-limit step-increment
                                  dag
                                  rule-alist pruning-rule-alist
                                  assumptions 64-bitp rules-to-monitor use-internal-contextsp
                                  prune-precise prune-approx
                                  normalize-xors count-hits print print-base untranslatep memoizep state)
  (declare (xargs :guard (and (natp steps-done)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (acl2::pseudo-dagp dag)
                              (acl2::rule-alistp rule-alist)
                              (acl2::rule-alistp pruning-rule-alist)
                              (pseudo-term-listp assumptions)
                              (booleanp 64-bitp)
                              (symbol-listp rules-to-monitor)
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp memoizep)
                              (acl2::ilks-plist-worldp (w state)) ; why?
                              )
                  :measure (nfix (+ 1 (- (nfix step-limit) (nfix steps-done))))
                  :stobjs state))
  (if (or (not (mbt (and (natp steps-done)
                         (natp step-limit))))
          (<= step-limit steps-done))
      (mv (erp-nil) dag state)
    (b* (;; Decide how many steps to do this time:
         (this-step-increment (acl2::this-step-increment step-increment steps-done))
         (steps-for-this-iteration (min (- step-limit steps-done) this-step-increment))
         ((when (not (posp steps-for-this-iteration))) ; use mbt?
          (er hard? 'repeatedly-run "Temination problem.")
          (mv :termination-problem nil state))
         (- (cw "(Running (up to ~x0 steps):~%" steps-for-this-iteration))
         ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
         (old-dag dag)
         ;; (- (and print (progn$ (cw "(DAG before stepping:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         (limits nil) ; todo: call this empty-rule-limits?
         (limits (acl2::add-limit-for-rules (if 64-bitp
                                                (step-opener-rules64)
                                              (step-opener-rules32))
                                            steps-for-this-iteration
                                            limits)) ; don't recompute for each small run?
         ((mv erp dag-or-constant limits state)
          ;; (if (eq :legacy rewriter)
          ;;     (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
          ;;                     :exhaustivep t
          ;;                     :rule-alist rule-alist
          ;;                     :assumptions assumptions
          ;;                     :monitor rules-to-monitor
          ;;                     ;; :fns-to-elide '(program-at) ; not supported
          ;;                     :use-internal-contextsp use-internal-contextsp
          ;;                     ;; pass print, so we can cause rule hits to be printed:
          ;;                     :print print ; :brief ;nil
          ;;                     ;; :print-interval 10000 ;todo: pass in
          ;;                     :limits limits
          ;;                     :memoizep memoizep
          ;;                     :check-inputs nil)
          (acl2::simplify-dag-x86 dag
                                  assumptions
                                  rule-alist
                                  nil ; interpreted-function-alist
                                  (acl2::known-booleans (w state))
                                  normalize-xors
                                  limits
                                  memoizep
                                  count-hits
                                  print
                                  rules-to-monitor
                                  *no-warn-ground-functions*
                                  '(program-at) ; fns-to-elide
                                  state)
            ;)
          )
         ((when erp) (mv erp nil state))
         ;; usually 0, unless we are done (can this ever be negative?):
         (remaining-limit ;; todo: clean this up: there is only a single rule:
           (acl2::limit-for-rule (first (if 64-bitp
                                            (step-opener-rules64)
                                          (step-opener-rules32)))
                                 limits))
         (steps-done-this-time (- steps-for-this-iteration (ifix remaining-limit))) ; todo: drop the ifix
         ((mv elapsed state) (acl2::real-time-since start-real-time state))
         (- (cw " (~x0 steps took " steps-done-this-time)
            (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
            (cw "s.)"))
         (- (cw ")~%")) ; matches "(Running"
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a quotep
         ;; Prune the DAG quickly but possibly imprecisely (actually, I've seen this be quite slow!):
         ((mv erp dag-or-constant state) (acl2::maybe-prune-dag-approximately prune-approx
                                                                              dag
                                                                              (remove-assumptions-about *non-stp-assumption-functions* assumptions)
                                                                              print
                                                                              60000 ; todo: pass in
                                                                              state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a quotep
         ;; (- (and print (progn$ (cw "(DAG after first pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; Prune precisely if feasible:
         ;; TODO: Maybe don't prune if the run has completed (but do simplify in that case)?
         ((mv erp dag-or-constant state)
          (acl2::maybe-prune-dag-precisely prune-precise ; if a natp, can help prevent explosion.
                                           dag
                                           ;; the assumptions used during lifting (program-at, MXCSR assumptions, etc) seem unlikely
                                           ;; to be helpful when pruning, and user assumptions seem like they should be applied by the
                                           ;; rewriter duing lifting (TODO: What about assumptions only usable by STP?)
                                           nil ; assumptions ; todo: include assumptions about canonical?
                                           :none
                                           pruning-rule-alist
                                           nil ; interpreted-function-alist
                                           rules-to-monitor
                                           t ;call-stp
                                           print
                                           state))
         ((when erp) (mv erp nil state))
         ((when (quotep dag-or-constant))
          (cw "Result is a constant!~%")
          (mv (erp-nil) dag-or-constant state))
         (dag dag-or-constant) ; it wasn't a quotep
         (- (and print ;(acl2::print-level-at-least-tp print)
                 (progn$ (cw "(DAG after this limited run:~%")
                         (cw "~X01" dag nil)
                         (cw ")~%"))))
         ;; TODO: Error if dag too big (must be able to add it to old dag, or make a version of equivalent-dagsp that signals an error):
         ;; (- (and print (progn$ (cw "(DAG after second pruning:~%")
         ;;                       (cw "~X01" dag nil)
         ;;                       (cw ")~%"))))
         ;; TODO: If pruning did something, consider doing another rewrite here (pruning may have introduced bvchop or bool-fix$inline).  But perhaps now there are enough rules used in pruning to handle that?
         (dag-fns (acl2::dag-fns dag))
         ;; Stop if we hit an unimplemented instruction (what if it's on an unreachable branch?):
         ((when (member-eq 'x86isa::x86-step-unimplemented dag-fns))
          (progn$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                  (cw "~%")
                  (mv (erp-nil) dag state))) ; todo: return an error?  the instruction might be in dead code.
         ((mv erp nothing-changedp) (acl2::equivalent-dagsp2 dag old-dag)) ; todo: can we test equivalence up to xor nest normalization?
         ((when erp) (mv erp nil state))
         ((when nothing-changedp)
          (cw "Note: Stopping the run because nothing changed.~%")
          (mv (erp-nil) dag state)) ; todo: return an error?  or maybe this can happen if we hit one of the stop-pcs
         (run-completedp (not (intersection-eq '(run-until-stack-shorter-than
                                                 run-until-stack-shorter-than-or-reach-pc
                                                 ;; new scheme:
                                                 run-until-rsp-is
                                                 run-until-rsp-is-or-reach-pc
                                                 ;; newer scheme:
                                                 run-until-rsp-is-above
                                                 run-until-rsp-is-above-or-reach-pc
                                                 run-until-esp-is-above
                                                 run-until-esp-is-above-or-reach-pc
                                                 ;; new:
                                                 x86-fetch-decode-execute
                                                 )
                                               dag-fns))))
      (if run-completedp
          ;; stop if the run is done
          ;; Simplify one last time (since pruning may have done something -- todo: skip this if pruning did nothing):
          (b* ((- (cw " The run has completed.~%"))
               (- (cw "(Doing final simplification:~%"))
               ((mv erp dag-or-constant state) ; todo: check if it is a constant?
                ;; (if (eq :legacy rewriter)
                ;;     (acl2::simp-dag dag ; todo: call the basic rewriter, but it needs to support :use-internal-contextsp
                ;;                     :exhaustivep t
                ;;                     :rule-alist rule-alist
                ;;                     :assumptions assumptions
                ;;                     :monitor rules-to-monitor
                ;;                     :use-internal-contextsp use-internal-contextsp
                ;;                     ;; pass print, so we can cause rule hits to be printed:
                ;;                     :print print ; :brief ;nil
                ;;                     ;; :print-interval 10000 ;todo: pass in
                ;;                     :limits limits
                ;;                     :memoizep memoizep
                ;;                     :check-inputs nil)
                (mv-let (erp result limits state)
                  (acl2::simplify-dag-x86 dag
                                          assumptions
                                          rule-alist
                                          nil ; interpreted-function-alist
                                          (acl2::known-booleans (w state))
                                          normalize-xors
                                          limits
                                          memoizep
                                          count-hits
                                          print
                                          rules-to-monitor
                                          *no-warn-ground-functions*
                                          '(program-at code-segment-assumptions32-for-code) ; fns-to-elide
                                          state)
                  (declare (ignore limits)) ; todo: use the limits?
                  (mv erp result state))
                  ;)
                ;; todo: also prune here?
                )
               ((when erp) (mv erp nil state))
               (- (cw " Done with final simplification.)~%")) ; balances "(Doing final simplification"
               ;; Check for error branches:
               (dag-fns (if (quotep dag-or-constant) nil (acl2::dag-fns dag-or-constant)))
               (error-branch-functions (intersection-eq dag-fns
                                                        ;; the presence of the indicates that we could not rule out an error branch
                                                        '(set-ms
                                                          set-fault)))
               ((when error-branch-functions)
                (cw "~X01" dag nil)
                (er hard? 'repeatedly-run "Unresolved error branches occur (offending functions in the DAG above: ~x0)." error-branch-functions)
                (mv :unresolved-error-branches nil state)))
            (mv (erp-nil) dag-or-constant state))
        ;; Continue the symbolic execution:
        (b* ((steps-done (+ steps-for-this-iteration steps-done))
             (- (cw "(Steps so far: ~x0.)~%" steps-done))
             (state ;; Print as a term unless it would be huge:
               (if (acl2::print-level-at-least-tp print)
                   (if (acl2::dag-or-quotep-size-less-than dag 1000) ; todo: drop the "-or-constant"
                       (b* ((- (cw "(Term after ~x0 steps:~%" steps-done))
                            (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                       (set-print-base-radix print-base state)
                                     state))
                            (term (dag-to-term dag))
                            (term (if untranslatep (acl2::untranslate$ term nil state) term))
                            ((when erp)
                             (er hard? 'repeatedly-run "Error untranslating.")
                             state)
                            (- (cw "~X01" term nil))
                            (state (set-print-base-radix 10 state)) ;make-event sets it to 10
                            (- (cw ")~%"))) ; matches "(Term after"
                         state)
                     (b* ((- (cw "(DAG after ~x0 steps:~%" steps-done))
                          (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
                                     (set-print-base-radix print-base state)
                                   state))
                          (- (cw "~X01" dag nil))
                          (state (set-print-base-radix 10 state))
                          (- (cw "(DAG has ~x0 IF-branches.)~%" (acl2::count-top-level-if-branches-in-dag dag))) ; todo: if 1, say "no ifs"
                          (- (cw ")~%"))) ; matches "(DAG after"
                       state))
                 state)))
          (repeatedly-run steps-done step-limit
                          step-increment
                          dag rule-alist pruning-rule-alist assumptions 64-bitp rules-to-monitor use-internal-contextsp prune-precise prune-approx normalize-xors count-hits print print-base untranslatep memoizep
                          state))))))

(local (in-theory (disable ;; new-normal-form-rules-common
                           ;; (:e new-normal-form-rules-common)
                           ;; assumption-simplification-rules
                           ;; (:e assumption-simplification-rules)
                           ;; new-normal-form-rules64
                           ;; (:e new-normal-form-rules64)
                    )))

;(defthm symbol-listp-of-new-normal-form-rules64 (symbol-listp (new-normal-form-rules64)))
;(defthm symbol-listp-of-read-and-write-rules-bv (symbol-listp (read-and-write-rules-bv)))

;(local (in-theory (disable (:e read-and-write-rules-bv) read-and-write-rules-bv)))
;(local (in-theory (disable (:e new-normal-form-rules64) new-normal-form-rules64)))
;(local (in-theory (disable (:e constant-opener-rules) constant-opener-rules)))

;(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Returns (mv erp assumptions assumption-rules state)
(defund simplify-assumptions (assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp new-style-elf-assumptionsp state)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (symbol-listp extra-assumption-rules)
                              (symbol-listp remove-assumption-rules)
                              (booleanp 64-bitp)
                              (acl2::count-hits-argp count-hits)
                              (booleanp bvp)
                              (acl2::ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* ((- (cw "(Simplifying assumptions...~%"))
       ((mv assumption-simp-start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ;; todo: optimize):
       (assumption-rules (set-difference-equal
                           (append extra-assumption-rules
                                   (new-normal-form-rules-common)
                                   (assumption-simplification-rules)
                                   (if 64-bitp
                                       ;; needed to match the normal forms used during lifting:
                                       (append (new-normal-form-rules64)
                                               (if bvp (read-and-write-rules-bv) (read-and-write-rules-non-bv))
                                               (if new-style-elf-assumptionsp
                                                   (append (unsigned-canonical-rules)
                                                           (canonical-rules-bv))
                                                 (canonical-rules-non-bv)))
                                     nil ; todo: why not use (new-normal-form-rules32)?
                                     ))
                           remove-assumption-rules))
       ((mv erp assumption-rule-alist)
        (acl2::make-rule-alist assumption-rules (w state)))
       ((when erp) (mv erp nil nil state))
       ;; TODO: Option to turn this off, or to do just one pass:
       ((mv erp assumptions)
        (acl2::simplify-conjunction-basic ;simplify-terms-repeatedly
          assumptions
          assumption-rule-alist
          (acl2::known-booleans (w state))
          nil ;; rules-to-monitor ; do we want to monitor here?  What if some rules are not included?
          *no-warn-ground-functions*
          nil ; don't memoize (avoids time spent making empty-memoizations)
          count-hits
          t   ; todo: warn just once
          ))
       ((when erp) (mv erp nil nil state))
       (assumptions (acl2::get-conjuncts-of-terms2 assumptions)) ; should already be done above, when repeatedly simplifying?
       ((mv assumption-simp-elapsed state) (acl2::real-time-since assumption-simp-start-real-time state))
       (- (cw " (Simplifying assumptions took ") ; usually <= .01 seconds
          (acl2::print-to-hundredths assumption-simp-elapsed)
          (cw "s.)~%"))
       (- (cw " Done simplifying assumptions)~%")))
    (mv nil assumptions assumption-rules state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In 32-bit mode, the upper 32-bits of the 64-bit register in the model are
;; unused, so we can assume they are equal to 0, without loss of generality.
;; Note that WR32 zeros out the upper 32-bits of a register; these assumptions
;; let us show that that has no effect.
(defund register-high-bit-assumptions ()
  (declare (xargs :guard t))
  '((equal (rax-high x86) 0)
    (equal (rbx-high x86) 0)
    (equal (rcx-high x86) 0)
    (equal (rdx-high x86) 0)
    (equal (rsp-high x86) 0)
    (equal (rbp-high x86) 0)))

;; Returns (mv erp result-dag-or-quotep assumptions input-assumption-vars lifter-rules-used assumption-rules-used term-to-simulate state).
;; This is also called by the formal unit tester.
(defun unroll-x86-code-core (target
                             parsed-executable
                             extra-assumptions ; todo: can these introduce vars for state components?  now we have :inputs for that.  could also replace register expressions with register names (vars) -- see what do do for the Tester.
                             suppress-assumptions
                             inputs-disjoint-from
                             stack-slots
                             existing-stack-slots
                             position-independent
                             inputs
                             type-assumptions-for-array-varsp
                             output-indicator
                             use-internal-contextsp
                             prune-precise
                             prune-approx
                             extra-rules
                             remove-rules
                             extra-assumption-rules ; todo: why "extra"?
                             remove-assumption-rules
                             step-limit
                             step-increment
                             stop-pcs
                             memoizep
                             monitor
                             normalize-xors
                             count-hits
                             print
                             print-base
                             untranslatep
                             bvp ; whether to use new-style, BV-friendly assumptions
                             state)
  (declare (xargs :guard (and (lifter-targetp target)
                              ;; parsed-executable ; todo: add a guard (even if it's weak for now)
                              (true-listp extra-assumptions) ; untranslated terms
                              (booleanp suppress-assumptions)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (or (natp existing-stack-slots)
                                  (eq :auto existing-stack-slots))
                              (member-eq position-independent '(t nil :auto))
                              (or (eq :skip inputs) (names-and-typesp inputs))
                              (booleanp type-assumptions-for-array-varsp)
                              ;; (output-indicatorp output-indicator) ; no recognizer for this, we just call wrap-in-output-extractor and see if it returns an error
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (symbol-listp remove-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (nat-listp stop-pcs)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp bvp))
                  :stobjs state
                  :mode :program ; todo: need a magic wrapper for translate-terms (must translate at least the user-supplied assumptions)
                  ))
  (b* ((- (cw "(Lifting ~s0.~%" target)) ;todo: print the executable name, also handle non-string targets better
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (state (acl2::widen-margins state))
       ;; Get and check the executable-type:
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (- (and (acl2::print-level-at-least-briefp print) (cw "(Executable type: ~x0.)~%" executable-type)))
       (- (acl2::ensure-x86 parsed-executable))
       ;; Handle a :position-independent of :auto:
       (position-independentp (if (eq :auto position-independent)
                                  (if (eq executable-type :mach-o-64)
                                      t ; since clang seems to produce position-independent code by default ; todo: look at the PIE bit in the header.
                                    (if (eq executable-type :elf-64)
                                        (let ((elf-type (acl2::parsed-elf-type parsed-executable)))
                                          (prog2$ (cw "ELF type: ~x0.~%" elf-type)
                                                  (if (acl2::parsed-elf-program-header-table parsed-executable)
                                                      ;; For ELF64, we treat :dyn and :rel as position-independent (addresses relative to the var base-address) and :exec as absolute:
                                                      (if (member-eq elf-type '(:rel :dyn)) t nil)
                                                    ;; TODO: Get this to work:
                                                    nil)))
                                      ;; TODO: Think about the other cases:
                                      t))
                                ;; the user supplied a value for position-independent, so use it:
                                position-independent))
       ((when (and (not position-independentp) ; todo: think about this:
                   (not (member-eq executable-type '(:mach-o-64 :elf-64)))))
        (er hard? 'unroll-x86-code-core "Non-position-independent lifting is currently only supported for ELF64 and MACHO64 files.")
        (mv :bad-options nil nil nil nil nil nil state))
       (- (if position-independentp (cw " Using position-independent lifting.~%") (cw " Using non-position-independent lifting.~%")))
       ;; (new-style-elf-assumptionsp (and (eq :elf-64 executable-type)

       ;;                                  ;; todo: remove this, but we have odd, unlinked ELFs that put both the text and data segments at address 0 !
       ;;                                  ;; todo: remove this, but we have some unlinked ELFs without sections.  we also have some unlinked ELFs that put both the text and data segments at address 0 !
       ;;                                  ;(acl2::parsed-elf-program-header-table parsed-executable) ; there are segments present (todo: improve the "new" behavior to use sections when there are no segments)
       ;;                                  ))
       (new-canonicalp (or (eq :elf-64 executable-type)
                           (eq :mach-o-64 executable-type)
                           (eq :pe-64 executable-type) ; todo, also need to change the assumptions
                           ))
       ;; (- (and (eq :elf-64 executable-type) (if new-style-elf-assumptionsp (cw " Using new-style ELF64 assumptions.~%")  (cw " Not using new-style ELF64 assumptions.~%"))))
       (- (and (stringp target)
               ;; Throws an error if the target doesn't exist:
               (acl2::ensure-target-exists-in-executable target parsed-executable)))
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       (existing-stack-slots (if (eq :auto existing-stack-slots)
                                 (if (eq :pe-64 executable-type)
                                     5 ; 1 for the saved return address, and 4 for registers on the stack (todo: think more about this)
                                   1 ; todo: think about the 32-bit cases
                                   )
                               existing-stack-slots))
       ;; Generate assumptions:
       ((mv erp assumptions untranslated-assumptions
            assumption-rules ; drop? todo: includes rules that were not used, but we return these as an RV named assumption-rules-used
            input-assumption-vars
            state)
        (if (eq :elf-64 executable-type)
            ;; New assumption generation behavior for ELF64:
            (b* (;; These are untranslated (in general):
                 ((mv erp automatic-assumptions input-assumption-vars)
                  (if suppress-assumptions
                      (mv nil nil nil) ; todo: this also suppresses input assumptions - should it?  the user can just not give inputs..
                    (assumptions-elf64-new target
                                           position-independentp ;(if (eq :auto position-independent) :auto position-independent) ; todo: clean up the handling of this
                                           stack-slots
                                           existing-stack-slots
                                           'x86
                                           inputs
                                           type-assumptions-for-array-varsp
                                           inputs-disjoint-from ; disjoint-chunk-addresses-and-lens
                                           bvp
                                           new-canonicalp
                                           parsed-executable)))
                 ((when erp) (mv erp nil nil nil nil state))
                 (untranslated-assumptions (append automatic-assumptions extra-assumptions)) ; includes any user assumptions
                 ;; Translate all the assumptions:
                 (assumptions (acl2::translate-terms untranslated-assumptions 'unroll-x86-code-core (w state)))
                 ;; Maybe simplify the assumptions:
                 ((mv erp assumptions assumption-rules state)
                  (if extra-assumptions
                      ;; If there are extra-assumptions, we need to simplify (e.g., an extra assumption could replace RSP with 10000, and then all assumptions about RSP need to mention 10000 instead):
                      (simplify-assumptions assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp t state)
                    (mv nil assumptions nil state)))
                 ((when erp) (mv erp nil nil nil nil state)))
              (mv nil assumptions
                  untranslated-assumptions ; seems ok to use the original, unrewritten assumptions here
                  assumption-rules input-assumption-vars state))
          (if (eq :mach-o-64 executable-type) ; todo: combine with the case above?
              ;; New assumption generation behavior for MACHO64:
              (b* (;; These are untranslated (in general):
                   ((mv erp automatic-assumptions input-assumption-vars)
                    (if suppress-assumptions
                        (mv nil nil nil) ; todo: this also suppresses input assumptions - should it?  the user can just not give inputs..
                      (assumptions-macho64-new target
                                               position-independentp ;(if (eq :auto position-independent) :auto position-independent) ; todo: clean up the handling of this
                                               stack-slots
                                               existing-stack-slots
                                               'x86
                                               inputs
                                               type-assumptions-for-array-varsp
                                               inputs-disjoint-from ; disjoint-chunk-addresses-and-lens
                                               bvp
                                               new-canonicalp
                                               parsed-executable)))
                   ((when erp) (mv erp nil nil nil nil state))
                   (untranslated-assumptions (append automatic-assumptions extra-assumptions)) ; includes any user assumptions
                   ;; Translate all the assumptions:
                   (assumptions (acl2::translate-terms untranslated-assumptions 'unroll-x86-code-core (w state)))
                   ;; Maybe simplify the assumptions:
                   ((mv erp assumptions assumption-rules state)
                    (if extra-assumptions
                        ;; If there are extra-assumptions, we need to simplify (e.g., an extra assumption could replace RSP with 10000, and then all assumptions about RSP need to mention 10000 instead):
                        (simplify-assumptions assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp t state)
                      (mv nil assumptions nil state)))
                   ((when erp) (mv erp nil nil nil nil state)))
                (mv nil assumptions
                    untranslated-assumptions ; seems ok to use the original, unrewritten assumptions here
                    assumption-rules input-assumption-vars state))
            (if (eq :pe-64 executable-type) ; todo: combine with the cases above?
                ;; New assumption generation behavior for PE64:
                (b* (;; These are untranslated (in general):
                     ((mv erp automatic-assumptions input-assumption-vars)
                      (if suppress-assumptions
                          (mv nil nil nil) ; todo: this also suppresses input assumptions - should it?  the user can just not give inputs..
                        (assumptions-pe64-new target
                                              position-independentp ;(if (eq :auto position-independent) :auto position-independent) ; todo: clean up the handling of this
                                              stack-slots
                                              existing-stack-slots
                                              'x86
                                              inputs
                                              type-assumptions-for-array-varsp
                                              inputs-disjoint-from ; disjoint-chunk-addresses-and-lens
                                              bvp
                                              new-canonicalp
                                              parsed-executable)))
                     ((when erp) (mv erp nil nil nil nil state))
                     (untranslated-assumptions (append automatic-assumptions extra-assumptions)) ; includes any user assumptions
                     ;; Translate all the assumptions:
                     (assumptions (acl2::translate-terms untranslated-assumptions 'unroll-x86-code-core (w state)))
                     ;; Maybe simplify the assumptions:
                     ((mv erp assumptions assumption-rules state)
                      (if extra-assumptions
                          ;; If there are extra-assumptions, we need to simplify (e.g., an extra assumption could replace RSP with 10000, and then all assumptions about RSP need to mention 10000 instead):
                          (simplify-assumptions assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp t state)
                        (mv nil assumptions nil state)))
                     ((when erp) (mv erp nil nil nil nil state)))
                  (mv nil assumptions
                      untranslated-assumptions ; seems ok to use the original, unrewritten assumptions here
                      assumption-rules input-assumption-vars state))

              ;; (b* (((when (eq :entry-point target)) ; todo
              ;;       (er hard? 'unroll-x86-code-core "Starting from the :entry-point is currently only supported for PE32 files and certain ELF64 files.")
              ;;       (mv :bad-entry-point nil nil nil nil state))
              ;;      ((when (natp target)) ; todo
              ;;       (er hard? 'unroll-x86-code-core "Starting from a numeric offset is currently only supported for PE32 files and certain ELF64 files.")
              ;;       (mv :bad-entry-point nil nil nil nil state))
              ;;      (text-section-bytes (acl2::get-mach-o-code parsed-executable)) ;all the code, not just the given subroutine
              ;;      (text-section-offset (acl2::get-mach-o-code-address parsed-executable))
              ;;      (text-section-length (len text-section-bytes))
              ;;      (base-var 'base-address) ; only used if position-independentp
              ;;      ;(offset-to-subroutine (- subroutine-address text-section-offset))
              ;;      (text-address-term (if position-independentp
              ;;                             (if bvp
              ;;                                 (if (= 0 text-section-offset)
              ;;                                     base-var ; avoids adding 0
              ;;                                   `(bvplus 64 ',text-section-offset ,base-var))
              ;;                               (if (= 0 text-section-offset)
              ;;                                   base-var ; avoids adding 0
              ;;                                 `(binary-+ ',text-section-offset ,base-var)))
              ;;                           text-section-offset))
              ;;      ((mv erp standard-assumptions)
              ;;       (if suppress-assumptions
              ;;           ;; Suppress tool-generated assumptions; use only the explicitly provided ones:
              ;;           (mv nil nil)
              ;;         (b* ((state-var 'x86)
              ;;              (subroutine-offset (acl2::subroutine-address-mach-o target parsed-executable))
              ;;              ((mv erp assumptions-for-text-section)
              ;;               (assumptions-for-memory-chunk text-section-offset text-section-bytes position-independentp state-var base-var stack-slots bvp new-canonicalp))
              ;;              ((when erp) (mv erp nil))

              ;;              ((mv erp text-const-assumptions) ; todo: do the main text section like this too -- really do all reasonable sections
              ;;               (make-section-assumptions-mach-o-64 "__TEXT" "__const" parsed-executable position-independentp stack-slots bvp base-var state-var)) ; pass new-canonicalp?
              ;;              ((when erp) (mv erp nil))
              ;;              ((mv erp data-assumptions)
              ;;               (make-section-assumptions-mach-o-64 "__DATA" "__data" parsed-executable position-independentp stack-slots bvp base-var state-var)) ; pass new-canonicalp?
              ;;              ((when erp) (mv erp nil)))
              ;;           (mv nil ; no error
              ;;               (append
              ;;                 assumptions-for-text-section
              ;;                 text-const-assumptions
              ;;                 data-assumptions
              ;;                 ;; todo: use this?
              ;;                 ;; (make-standard-assumptions64-new stack-slots 'x86 'base-address ; only needed if position-independentp
              ;;                 ;;                                  target-offset
              ;;                 ;;                                  position-independentp
              ;;                 ;;                                  bvp)
              ;;                 (make-standard-state-assumptions-fn state-var)
              ;;                 (if new-canonicalp
              ;;                     `((integerp ,base-var))
              ;;                   `((canonical-address-p ,base-var)) ; at least for now
              ;;                   )

              ;;                 `((equal (64-bit-modep ,state-var) t)

              ;;                   ;; Alignment checking is turned off:
              ;;                   (not (alignment-checking-enabled-p ,state-var))

              ;;                   ;; The RSP is 8-byte aligned (TODO: check with Shilpi):
              ;;                   ;; This may not be respected by malware.
              ;;                   ;; TODO: Try without this
              ;;                   (equal 0 (bvchop 3 (rgfi *rsp* ,state-var)))

              ;;                   ;; The return address must be canonical because we will transfer
              ;;                   ;; control to that address when doing the return:
              ;;                   ,@(if new-canonicalp
              ;;                         `((unsigned-canonical-address-p (read 8 (rsp ,state-var) ,state-var)))
              ;;                       `((canonical-address-p (logext 64 (read 8 (rsp ,state-var) ,state-var)))))

              ;;                   ;; The stack must be canonical:
              ;;                   ,@(if new-canonicalp ; todo: what if not bvp?
              ;;                         ;; todo: think about this:
              ;;                         `((canonical-regionp ,(+ 16 (* 8 stack-slots))
              ;;                                              ,(if (= 0 stack-slots)
              ;;                                                   `(rsp ,state-var)
              ;;                                                 `(bvplus 64 ',(* -8 stack-slots) (rsp ,state-var)))))
              ;;                       ;; old-style
              ;;                       (append `(;; The stack slot contaning the return address must be canonical
              ;;                                 ;; because the stack pointer returns here when we pop the saved
              ;;                                 ;; RBP:
              ;;                                 (canonical-address-p (rsp ,state-var))

              ;;                                 ;; The stack slot 'below' the return address must be canonical
              ;;                                 ;; because the stack pointer returns here when we do the return:
              ;;                                 (canonical-address-p (+ 8 (rsp ,state-var))))
              ;;                               (if (posp stack-slots)
              ;;                                   `(;;add to make-standard-state-assumptions-64-fn?
              ;;                                     (x86isa::canonical-address-p (+ -8 (rsp ,state-var)))
              ;;                                     (x86isa::canonical-address-p (binary-+ ',(* -8 stack-slots) (rsp ,state-var))) ; todo: drop if same as above
              ;;                                     )
              ;;                                 ;; ;; todo: modernize:
              ;;                                 ;; ;; Stack addresses are canonical (could use something like all-addreses-of-stack-slots here, but these addresses are by definition canonical):
              ;;                                 ;; (x86isa::canonical-address-listp (addresses-of-subsequent-stack-slots ,stack-slots (rgfi *rsp* ,state-var))) ; todo: use rsp
              ;;                                 ;; ;; old: (canonical-address-p (+ -8 (rgfi *rsp* ,state-var))) ;; The stack slot where the RBP will be saved
              ;;                                 nil)))

              ;;                   ;; ;; todo: modernize:
              ;;                   ;; (bytes-loaded-at-address-64 ',text-section-bytes ,text-address-term
              ;;                   ;;                             ,bvp , state-var)

              ;;                   ;; The program counter is at the start of the routine to lift:
              ;;                   (equal (rip ,state-var) (logext 64 ,(if position-independentp
              ;;                                                           (if bvp
              ;;                                                               (if (= 0 subroutine-offset)
              ;;                                                                   base-var ; avoids adding 0
              ;;                                                                 `(bvplus 64 ',subroutine-offset ,base-var))
              ;;                                                             (if (= 0 subroutine-offset)
              ;;                                                                 base-var ; avoids adding 0
              ;;                                                               `(binary-+ ',subroutine-offset ,base-var)))
              ;;                                                         subroutine-offset)))

              ;;                   ;; ;; The program is disjoint from the part of the stack that is written:
              ;;                   ;; ,@(if (posp stack-slots)
              ;;                   ;;       ;; todo: make a better version of separate that doesn't require the Ns to be positive (and that doesn't have the useless rwx params):
              ;;                   ;;       (if bvp
              ;;                   ;;           ;; essentially the same as the below SEPARATE claim:
              ;;                   ;;           `((disjoint-regions48p ,(len text-section-bytes) ,text-address-term ; todo: drop the 2 bvchop
              ;;                   ;;                                  (* 8 ,stack-slots) (bvchop 48 (+ (* -8 ,stack-slots) (rgfi *rsp* ,state-var)))))
              ;;                   ;;         `((separate :r ,(len text-section-bytes) ,text-address-term
              ;;                   ;;                     ;; Only a single stack slot is written
              ;;                   ;;                     ;;old: (create-canonical-address-list 8 (+ -8 (rgfi *rsp* ,state-var)))
              ;;                   ;;                     :r (* 8 ,stack-slots) (+ (* -8 ,stack-slots) (rgfi *rsp* ,state-var)))))
              ;;                   ;;     ;; Can`'t call separate here because (* 8 stack-slots) = 0.
              ;;                   ;;     nil)
              ;;                   ))))))
              ;;      ((when erp) (mv erp nil nil nil nil state))
              ;;      ;; maybe we should check suppress-assumptions here, but if they gave an :inputs, they must want the assumptions:
              ;;      ((mv input-assumptions input-assumption-vars)
              ;;       (if (not (equal inputs :skip)) ; really means generate no assumptions
              ;;           (assumptions-and-vars-for-inputs inputs ; these are names-and-types
              ;;                                            ;; todo: handle zmm regs and values passed on the stack?!:
              ;;                                            ;; handle structs that fit in 2 registers?
              ;;                                            ;; See the System V AMD64 ABI
              ;;                                            '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
              ;;                                            stack-slots
              ;;                                            (acons text-address-term text-section-length nil) ;; disjoint-chunk-addresses-and-lens
              ;;                                            type-assumptions-for-array-varsp
              ;;                                            nil nil
              ;;                                            new-canonicalp)
              ;;         (mv nil nil)))
              ;;      (automatic-assumptions (append standard-assumptions input-assumptions))
              ;;      (untranslated-assumptions (append automatic-assumptions extra-assumptions))
              ;;      (assumptions (acl2::translate-terms untranslated-assumptions 'unroll-x86-code-core (w state)))
              ;;      (- (and (acl2::print-level-at-least-tp print) (progn$ (cw "(Unsimplified assumptions:~%")
              ;;                                                            (print-terms-elided assumptions
              ;;                                                                                '(;(standard-assumptions-elf-64 t nil t t t t)
              ;;                                                                                  (standard-assumptions-mach-o-64 t nil t t t t)
              ;;                                                                                  ;(standard-assumptions-pe-64 t nil t t t t)
              ;;                                                                                  (equal t nil)
              ;;                                                                                  )) ; todo: more?
              ;;                                                            (cw ")~%"))))
              ;;      ;; Next, we simplify the assumptions.  This allows us to state the
              ;;      ;; theorem about a lifted routine concisely, using an assumption
              ;;      ;; function that opens to a large conjunction before lifting is
              ;;      ;; attempted.  We need to assume some assumptions when simplifying the
              ;;      ;; others, because opening things like read64 involves testing
              ;;      ;; canonical-addressp (which we know from other assumptions is true):
              ;;      ((mv erp assumptions assumption-rules state)
              ;;       (simplify-assumptions assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp nil state))
              ;;      ((when erp) (mv erp nil nil nil nil state)))
              ;;   (mv nil assumptions
              ;;       untranslated-assumptions ; seems ok to use the original, unrewritten assumptions here
              ;;       assumption-rules input-assumption-vars state))

              ;; legacy case (generate some assumptions and then simplify them):
              ;; Covers pe-64, pe-32, elf-32, and mach-o-32.
              ;; TODO: Why is assumptions-and-vars-for-inputs in this legacy case?
              (b* (;;todo: finish adding support for :entry-point!
                   ((when (and (eq :entry-point target)
                               (not (eq :pe-32 executable-type))))
                    (er hard? 'unroll-x86-code-core "Starting from the :entry-point is currently only supported for PE32 files and certain ELF64 files.")
                    (mv :bad-entry-point nil nil nil nil state))
                   ((when (and (natp target)
                               (not (eq :pe-32 executable-type))))
                    (er hard? 'unroll-x86-code-core "Starting from a numeric offset is currently only supported for PE32 files and certain ELF64 files.")
                    (mv :bad-entry-point nil nil nil nil state))
                   (text-offset
                     (and 64-bitp ; todo
                          (if (eq :pe-64 executable-type)
                              'text-offset ; todo: match what we do for other executable types
                            (if (or (eq :elf-32 executable-type)
                                    ;;(eq :elf-64 executable-type)
                                    )
                                (if position-independentp 'text-offset `,(acl2::get-elf-text-section-address parsed-executable)) ; todo: think about the 32-bit case, esp wrt position independence
                              (if (eq :mach-o-32 executable-type)
                                  nil ; todo
                                (if (eq :pe-32 executable-type)
                                    nil ; todo
                                  (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type)))))))
                   (code-length
                     (and 64-bitp ; todo
                          (if (eq :pe-64 executable-type)
                              10000 ; fixme
                            (if (or (eq :elf-32 executable-type)
                                    ;;(eq :elf-64 executable-type)
                                    )
                                (len (acl2::get-elf-code parsed-executable))
                              (if (eq :mach-o-32 executable-type)
                                  nil ; todo
                                (if (eq :pe-32 executable-type)
                                    nil ; todo
                                  (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type)))))))
                   (standard-assumptions
                     (if suppress-assumptions
                         ;; Suppress tool-generated assumptions; use only the explicitly provided ones:
                         nil
                       (if (eq :pe-64 executable-type) ; todo: impossible?
                           `((standard-assumptions-pe-64 ',target
                                                         ',parsed-executable
                                                         ',stack-slots
                                                         ',existing-stack-slots
                                                         text-offset
                                                         ',bvp
                                                         x86))
                         ;; (if (eq :elf-64 executable-type)
                         ;;     `((standard-assumptions-elf-64 ',target
                         ;;                                    ',parsed-executable
                         ;;                                    ',stack-slots
                         ;;                                    ,text-offset
                         ;;                                    ',bvp
                         ;;                                    x86))
                         (if (eq :mach-o-32 executable-type)
                             (gen-standard-assumptions-mach-o-32 target parsed-executable stack-slots)
                           (if (eq :pe-32 executable-type)
                               ;; todo: try without expanding this:
                               (gen-standard-assumptions-pe-32 target parsed-executable stack-slots)
                             ;;todo: add support for :elf-32
                             (er hard? 'unroll-x86-code-core "Unsupported executable type: ~x0.~%" executable-type)))
                     ;  )
                         )))
                   ;; Add 32-bit-specific assumptions:
                   (standard-assumptions (if 64-bitp
                                             standard-assumptions
                                           (append (register-high-bit-assumptions)
                                                   standard-assumptions)))

                   ;; maybe we should check suppress-assumptions here, but if they gave an :inputs, they must want the assumptions:
                   ((mv input-assumptions input-assumption-vars)
                    (if (and 64-bitp                                      ; todo
                             (not (equal inputs :skip)) ; really means generate no assumptions
                             )
                        (assumptions-and-vars-for-inputs inputs ; these are names-and-types
                                                         ;; todo: handle zmm regs and values passed on the stack?!:
                                                         ;; handle structs that fit in 2 registers?
                                                         ;; See the System V AMD64 ABI
                                                         '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                                         stack-slots
                                                         existing-stack-slots
                                                         (acons text-offset code-length nil) ;; disjoint-chunk-addresses-and-lens
                                                         type-assumptions-for-array-varsp
                                                         nil nil
                                                         new-canonicalp)
                      (mv nil nil)))
                   (assumptions (append standard-assumptions input-assumptions)) ; call these automatic-assumptions?
                   (assumptions (append assumptions extra-assumptions))
                   (assumptions-to-return assumptions) ; untranslated?
                   (assumptions (acl2::translate-terms assumptions 'unroll-x86-code-core (w state))) ; perhaps don't translate the automatic-assumptions?
                   (- (and (acl2::print-level-at-least-tp print) (progn$ (cw "(Unsimplified assumptions:~%")
                                                                         (print-terms-elided assumptions
                                                                                             '(;; (standard-assumptions-elf-64 t nil t t t t)
                                                                                               ;; (standard-assumptions-mach-o-64 t nil t t t t)
                                                                                               (standard-assumptions-pe-64 t nil t t t t)
                                                                                               (equal t nil)
                                                                                               )) ; todo: more?
                                                                         (cw ")~%"))))
                   ;; Next, we simplify the assumptions.  This allows us to state the
                   ;; theorem about a lifted routine concisely, using an assumption
                   ;; function that opens to a large conjunction before lifting is
                   ;; attempted.  We need to assume some assumptions when simplifying the
                   ;; others, because opening things like read64 involves testing
                   ;; canonical-addressp (which we know from other assumptions is true):
                   ((mv erp assumptions assumption-rules state)
                    (simplify-assumptions assumptions extra-assumption-rules remove-assumption-rules 64-bitp count-hits bvp nil state))
                   ((when erp) (mv erp nil nil nil nil state)))
                (mv nil assumptions assumptions-to-return assumption-rules input-assumption-vars state))))))
       ((when erp)
        (er hard? 'unroll-x86-code-core "Error generating assumptions: ~x0." erp)
        (mv erp nil nil nil nil nil nil state))
       (- (and print (progn$ (cw "(Assumptions for lifting:~%") ; should we untranslate these?
                             (if (acl2::print-level-at-least-tp print)
                                 (acl2::print-list assumptions)
                               (print-terms-elided assumptions '((program-at t nil t) ; the program can be huge
                                                                 (equal t nil))))
                             (cw ")~%"))))
       ;; Prepare for symbolic execution:
       (- (and stop-pcs (cw "Will stop execution when any of these PCs are reached: ~x0.~%" stop-pcs))) ; todo: print in hex?
       (- (and stop-pcs
               position-independentp
               (er hard? 'unroll-x86-code-core ":stop-pcs are not supported with position-independentp.")))
       (term-to-simulate (if stop-pcs
                             (if 64-bitp
                                 `(run-until-return-or-reach-pc3 ',stop-pcs x86)
                               `(run-until-return-or-reach-pc4 ',stop-pcs x86))
                           (if 64-bitp
                               '(run-until-return3 x86)
                             '(run-until-return4 x86))))
       (term-to-simulate (wrap-in-output-extractor output-indicator term-to-simulate (w state))) ;TODO: delay this if lifting a loop?
       (- (cw "(Limiting the total steps to ~x0.)~%" step-limit))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (acl2::make-term-into-dag-basic term-to-simulate nil))
       ((when erp) (mv erp nil nil nil nil nil nil state))
       ((when (quotep dag-to-simulate))
        (er hard? 'unroll-x86-code-core "Unexpected quotep: ~x0." dag-to-simulate)
        (mv :unexpected-quotep nil nil nil nil nil nil state))
       ;; Choose the lifter rules to use:
       (lifter-rules (if 64-bitp (unroller-rules64) (unroller-rules32)))
       (lifter-rules (append (if bvp (read-and-write-rules-bv) (read-and-write-rules-non-bv))       ;todo: only need some of these for 64-bits?
                             (if new-canonicalp (append (unsigned-canonical-rules) (canonical-rules-bv)) (canonical-rules-non-bv)) ; todo: use new-canonicalp more
                             lifter-rules))
       (symbolic-execution-rules (if stop-pcs
                                     (if 64-bitp
                                         (symbolic-execution-rules-with-stop-pcs64)
                                       (symbolic-execution-rules-with-stop-pcs32))
                                   (if 64-bitp
                                       (symbolic-execution-rules64)
                                     (symbolic-execution-rules32))))
       (lifter-rules (append symbolic-execution-rules lifter-rules))
       ;; Add any extra-rules:
       (- (let ((intersection (intersection-eq extra-rules lifter-rules))) ; todo: optimize (sort and then compare, and also use sorted lists below...)
            (and intersection
                 (cw "Warning: The extra-rules include these rules that are already present: ~X01.~%" intersection nil))))
       (lifter-rules (append extra-rules lifter-rules)) ; todo: use union?  sort by symbol first and merge (may break things)?
       ;; Remove any remove-rules:
       (- (let ((non-existent-remove-rules (set-difference-eq remove-rules lifter-rules)))
            (and non-existent-remove-rules
                 (cw "WARNING: The following rules in :remove-rules were not present: ~X01.~%" non-existent-remove-rules nil))))
       (lifter-rules (set-difference-eq lifter-rules remove-rules))
       ((mv erp lifter-rule-alist)
        (acl2::make-rule-alist lifter-rules (w state))) ; todo: allow passing in the rule-alist (and don't recompute for each lifted function)
       ((when erp) (mv erp nil nil nil nil nil nil state))
       ;; Now make a rule-alist for pruning (must exclude rules that require the x86 rewriter):
       (pruning-rules (set-difference-eq lifter-rules (x86-rewriter-rules))) ; optimize?  should we pre-sort rule-lists?
       ((mv erp pruning-rule-alist)
        (acl2::make-rule-alist pruning-rules (w state)))
       ((when erp) (mv erp nil nil nil nil nil nil state))
       ;; Decide which rules to monitor:
       (debug-rules (if 64-bitp (debug-rules64) (debug-rules32)))
       (rules-to-monitor (maybe-add-debug-rules debug-rules monitor))
       ;; Do the symbolic execution:
       ((mv erp result-dag-or-quotep state)
        (repeatedly-run 0 step-limit step-increment dag-to-simulate lifter-rule-alist pruning-rule-alist assumptions 64-bitp rules-to-monitor use-internal-contextsp prune-precise prune-approx normalize-xors count-hits print print-base untranslatep memoizep state))
       ((when erp) (mv erp nil nil nil nil nil nil state))
       (state (acl2::unwiden-margins state))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Lifting took ")
          (acl2::print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       ;; Print the result (todo: allow suppressing this):
       (- (if (quotep result-dag-or-quotep)
              (cw " Lifting produced the constant ~x0.)~%" result-dag-or-quotep) ; matches (Lifting...
            (progn$ (cw " Lifting produced a dag:~%")
                    (acl2::print-dag-info result-dag-or-quotep 'result t)
                    (cw ")~%") ; matches (Lifting...
                    ))))
    (mv (erp-nil) result-dag-or-quotep untranslated-assumptions input-assumption-vars lifter-rules assumption-rules term-to-simulate state)))

;; Returns (mv erp event state)
;; TODO: Consider using the current print-base (:auto value) by default.
(defun def-unrolled-fn (lifted-name
                        target
                        executable
                        inputs
                        output-indicator
                        extra-assumptions
                        suppress-assumptions
                        inputs-disjoint-from
                        stack-slots
                        existing-stack-slots
                        position-independent
                        type-assumptions-for-array-varsp
                        use-internal-contextsp
                        prune-precise
                        prune-approx
                        extra-rules
                        remove-rules
                        extra-assumption-rules
                        remove-assumption-rules
                        step-limit
                        step-increment
                        stop-pcs
                        memoizep
                        monitor
                        normalize-xors
                        count-hits
                        print
                        print-base
                        untranslatep
                        produce-function
                        non-executable
                        produce-theorem
                        prove-theorem ;whether to try to prove the theorem with ACL2 (rarely works)
                        restrict-theory
                        bvp
                        whole-form
                        state)
  (declare (xargs :guard (and (symbolp lifted-name)
                              (lifter-targetp target)
                              ;; executable
                              ;; extra-assumptions ; untranslated-terms
                              (booleanp suppress-assumptions)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (natp stack-slots)
                              (or (natp existing-stack-slots)
                                  (eq :auto existing-stack-slots))
                              (member-eq position-independent '(t nil :auto))
                              (or (eq :skip inputs) (names-and-typesp inputs))
                              (booleanp type-assumptions-for-array-varsp)
                              ;; (output-indicatorp output-indicator) ; no recognizer for this, we just call wrap-in-output-extractor and see if it returns an error
                              (booleanp use-internal-contextsp)
                              (or (eq nil prune-precise)
                                  (eq t prune-precise)
                                  (natp prune-precise))
                              (or (eq nil prune-approx)
                                  (eq t prune-approx)
                                  (natp prune-approx))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (symbol-listp extra-assumption-rules)
                              (symbol-listp remove-assumption-rules)
                              (natp step-limit)
                              (acl2::step-incrementp step-increment)
                              (nat-listp stop-pcs)
                              (booleanp memoizep)
                              (or (symbol-listp monitor)
                                  (eq :debug monitor))
                              (acl2::normalize-xors-optionp normalize-xors)
                              (acl2::count-hits-argp count-hits)
                              (acl2::print-levelp print)
                              (member print-base '(10 16))
                              (booleanp untranslatep)
                              (booleanp produce-function)
                              (member-eq non-executable '(t nil :auto))
                              (booleanp produce-theorem)
                              (booleanp prove-theorem)
                              (booleanp restrict-theory)
                              (booleanp bvp))
                  :stobjs state
                  :mode :program ; todo
                  ))
  (b* (;; Check whether this call to the lifter is redundant:
       (previous-result (previous-lifter-result whole-form state))
       ((when previous-result)
        (mv nil '(value-triple :redundant) state))
       ;; Start timing:
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       ;; Handle filename vs parsed-structure
       ((mv erp parsed-executable state)
        (if (stringp executable)
            ;; it's a filename, so parse the file:
            (acl2::parse-executable executable state)
          ;; it's already a parsed-executable: ; todo: can we deprecate this case?
          (mv nil executable state)))
       ((when erp)
        (er hard? 'def-unrolled-fn "Error (~x0) parsing executable: ~s1." erp executable)
        (mv t nil state))
       ;; Lift the function to obtain the DAG:
       ((mv erp result-dag assumptions assumption-vars lifter-rules-used assumption-rules-used term-to-simulate state)
        (unroll-x86-code-core target parsed-executable
          extra-assumptions suppress-assumptions inputs-disjoint-from stack-slots existing-stack-slots position-independent
          inputs type-assumptions-for-array-varsp output-indicator use-internal-contextsp prune-precise prune-approx extra-rules remove-rules extra-assumption-rules remove-assumption-rules
          step-limit step-increment stop-pcs memoizep monitor normalize-xors count-hits print print-base untranslatep bvp state))
       ((when erp) (mv erp nil state))
       ;; TODO: Fully handle a quotep result here:
       (result-dag-size (acl2::dag-or-quotep-size result-dag))
       (result-dag-fns (acl2::dag-fns result-dag))
       ;; Sometimes the presence of text-offset may indicate that something
       ;; wasn't resolved, but other times it's just needed to express some
       ;; junk left on the stack
       (result-dag-vars (acl2::dag-vars result-dag))
       ;; Build the defconst:
       (defconst-form `(defconst ,(pack-in-package-of-symbol lifted-name '* lifted-name '*) ',result-dag))
       ;; (fn-formals result-dag-vars) ; we could include x86 here, even if the dag is a constant
       (executable-type (acl2::parsed-executable-type parsed-executable))
       (64-bitp (member-equal executable-type '(:mach-o-64 :pe-64 :elf-64)))
       ;; Now sort the formals:
       (param-names (if (and 64-bitp
                             (not (equal :skip inputs)))
                        ;; The user gave names to the params (and/or their components, etc), and those vars will be put in:
                        assumption-vars ; (strip-cars inputs) ; fixme: handle array and pointer values (just look at the dag vars?) -- done?
                      ;; The register names may be being introduced (todo: deprecate this?):
                      '(rdi rsi rdx rcx r8 r9))) ; todo: handle 32-bit calling convention
       (common-formals (append param-names '(x86))) ; todo: handle 32-bit calling convention
       ;; these will be ordered like common-formals:
       (expected-formals (intersection-eq common-formals result-dag-vars))
       (unexpected-formals (set-difference-eq result-dag-vars common-formals)) ; todo: warn if inputs given?  maybe x86 will sometimes be needed?
       (fn-formals (append expected-formals unexpected-formals))
       ;; Do we want a check like this?
       ;; ((when (not (subsetp-eq result-vars '(x86 text-offset))))
       ;;  (mv t (er hard 'lifter "Unexpected vars, ~x0, in result DAG!" (set-difference-eq result-vars '(x86 text-offset))) state))
       ;; TODO: Maybe move some of this to the -core function:
       ;; (state (if (not (eql 10 print-base)) ; make-event always sets the print-base to 10
       ;;            (set-print-base-radix print-base state)
       ;;          state)) ; todo: do this better
       ((when (intersection-eq result-dag-fns '(run-until-stack-shorter-than run-until-return
                                                run-until-stack-shorter-than-or-reach-pc run-until-return-or-reach-pc
                                                run-until-rsp-is-above run-until-rsp-is-above-or-reach-pc
                                                run-until-esp-is-above run-until-esp-is-above-or-reach-pc)))
        (if (< result-dag-size 100000) ; todo: make customizable
            (progn$ (cw "(Term:~%")
                    (cw "~X01" (let ((term (dag-to-term result-dag)))
                                 (if untranslatep
                                     (untranslate term nil (w state))
                                   term))
                        nil)
                    (cw ")~%"))
          (progn$ (cw "(DAG:~%")
                  (cw "~X01" result-dag nil)
                  (cw ")~%")))
        (mv t (er hard 'lifter "Lifter error: The run did not finish.") state))
       ;; Not valid if (not (< result-dag-size 10000)):
       (maybe-result-term (and (< result-dag-size 10000) ; avoids exploding
                               (acl2::dag-to-term result-dag)))
       ;; Print the result:
       (- (and print
               (if (< result-dag-size 10000)
                   (cw "(Result: ~x0)~%" maybe-result-term)
                 (progn$ (cw "(Result:~%")
                         (cw "~X01" result-dag nil)
                         (cw ")~%")))))
       ;; Possibly produce a defun:
       ((mv erp defuns) ; defuns is nil or a singleton list
        (if (not produce-function)
            (mv (erp-nil) nil)
          (b* (;;TODO: consider untranslating this, or otherwise cleaning it up:
               (function-body (if (< result-dag-size 1000)
                                  maybe-result-term
                                `(acl2::dag-val-with-axe-evaluator ',result-dag
                                                                   ,(acl2::make-acons-nest result-dag-vars)
                                                                   ',(acl2::make-interpreted-function-alist (acl2::get-non-built-in-supporting-fns-list result-dag-fns acl2::*axe-evaluator-functions* (w state)) (w state))
                                                                   '0 ;array depth (not very important)
                                                                   )))
               (function-body-untranslated (if untranslatep (untranslate function-body nil (w state)) function-body)) ;todo: is this unsound (e.g., because of user changes in how untranslate works)?
               (function-body-retranslated (acl2::translate-term function-body-untranslated 'def-unrolled-fn (w state)))
               ;; TODO: I've seen this check fail when (if x y t) got turned into (if (not x) (not x) y):
               ((when (not (equal function-body function-body-retranslated))) ;todo: make a safe-untranslate that does this check?
                (er hard? 'lifter "Problem with function body.  Untranslating and then re-translating did not give original body.  Body was ~X01.  Re-translated body was ~X23" function-body nil function-body-retranslated nil)
                (mv :problem-with-function-body nil))
               ;;(- (cw "Runes used: ~x0" runes)) ;TODO: Have Axe return these?
               ;;use defun-nx by default because stobj updates are not all let-bound to x86
               (non-executable (if (eq :auto non-executable)
                                   (if (member-eq 'x86 fn-formals) ; there may be writes to the stobj (perhaps with unresolved reads around them), so we use defun-nx (todo: do a more precise check)
                                       ;; (eq :all output-indicator) ; we use defun-nx since there is almost certainly a stobj update (and updates are not properly let-bound)
                                       t
                                     nil)
                                 non-executable))
               (defun-variant (if non-executable 'defun-nx 'defun))
               (defun `(,defun-variant ,lifted-name (,@fn-formals)
                         (declare (xargs ,@(if (member-eq 'x86 fn-formals)
                                               `(:stobjs x86)
                                             nil)
                                         :verify-guards nil ;TODO
                                         )
                                  ,@(let ((ignored-vars (set-difference-eq fn-formals result-dag-vars)))
                                      (and ignored-vars
                                           `((ignore ,@ignored-vars)))))
                         ,function-body-untranslated)))
            (mv (erp-nil) (list defun)))))
       ((when erp) (mv erp nil state))
       (produce-theorem (and produce-theorem
                             (if (not produce-function)
                                 ;; todo: do something better in this case?
                                 (prog2$ (cw "NOTE: Suppressing theorem because :produce-function is nil.~%")
                                         nil)
                               t)))
       (defthms ; either nil or a singleton list
         (and produce-theorem
              (if stop-pcs
                  (prog2$ (cw "Suppressing theorem because :stop-pcs were given.~%")
                          nil)
                t)
              (let* ((defthm `(defthm ,(acl2::pack$ lifted-name '-correct)
                                (implies (and ,@assumptions)
                                         (equal ,term-to-simulate
                                                (,lifted-name ,@fn-formals)))
                                :hints ,(if restrict-theory
                                            `(("Goal" :in-theory '(,lifted-name ;,@runes ;without the runes here, this won't work
                                                                   )))
                                          `(("Goal" :in-theory (enable ,@lifter-rules-used
                                                                       ,@assumption-rules-used))))))
                     (defthm (if prove-theorem
                                 defthm
                               `(skip-proofs ,defthm))))
                (list defthm))))
       (events (cons defconst-form (append defuns defthms)))
       (event-names (acl2::strip-cadrs events))
       (event `(progn ,@events))
       (event (acl2::extend-progn event `(table x86-lifter-table ',whole-form ',event)))
       (event (acl2::extend-progn event `(value-triple '(,@event-names))))
       ((mv elapsed state) (acl2::real-time-since start-real-time state))
       (- (cw " (Unrolling ~x0 took " lifted-name)
          (acl2::print-to-hundredths elapsed)
          (cw "s, not including event submission.)~%")))
    (mv nil event state)))

;TODO: Add show- variant
;bad name?
;; TODO: :print nil is not fully respected
;; Creates some events to represent the unrolled computation, including a defconst for the DAG and perhaps a defun and a theorem.
(defmacrodoc def-unrolled (&whole whole-form
                                  lifted-name
                                  executable
                                  &key
                                  (target ':entry-point)
                                  (inputs ':skip)
                                  (output ':all)
                                  (extra-assumptions 'nil)
                                  (suppress-assumptions 'nil)
                                  (inputs-disjoint-from ':code)
                                  (stack-slots '100)
                                  (existing-stack-slots ':auto)
                                  (position-independent ':auto)
                                  (type-assumptions-for-array-vars 't)
                                  (use-internal-contextsp 't)
                                  (prune-precise '1000)
                                  (prune-approx 't)
                                  (extra-rules 'nil)
                                  (remove-rules 'nil)
                                  (extra-assumption-rules 'nil)
                                  (remove-assumption-rules 'nil)
                                  (step-limit '1000000)
                                  (step-increment '100)
                                  (stop-pcs 'nil)
                                  (memoizep 't)
                                  (monitor 'nil)
                                  (normalize-xors 'nil)
                                  (count-hits 'nil)
                                  (print ':brief)             ;how much to print
                                  (print-base '10)
                                  (untranslatep 't)
                                  (produce-function 't)
                                  (non-executable ':auto)
                                  (produce-theorem 'nil)
                                  (prove-theorem 'nil)
                                  (restrict-theory 't)       ;todo: deprecate
                                  (bvp 't)
                                  )
  `(,(if (acl2::print-level-at-least-tp print) 'make-event 'acl2::make-event-quiet)
    (def-unrolled-fn
      ',lifted-name
      ,target
      ,executable ; gets evaluated
      ',inputs
      ',output
      ,extra-assumptions
      ',suppress-assumptions
      ',inputs-disjoint-from
      ',stack-slots
      ',existing-stack-slots
      ',position-independent
      ',type-assumptions-for-array-vars
      ',use-internal-contextsp
      ',prune-precise
      ',prune-approx
      ,extra-rules ; gets evaluated since not quoted
      ,remove-rules ; gets evaluated since not quoted
      ,extra-assumption-rules ; gets evaluated since not quoted
      ,remove-assumption-rules ; gets evaluated since not quoted
      ',step-limit
      ',step-increment
      ,stop-pcs
      ',memoizep
      ,monitor ; gets evaluated since not quoted
      ',normalize-xors
      ',count-hits
      ',print
      ',print-base
      ',untranslatep
      ',produce-function
      ',non-executable
      ',produce-theorem
      ',prove-theorem
      ',restrict-theory
      ',bvp
      ',whole-form
      state))
  :parents (acl2::axe-x86 acl2::axe-lifters)
  :short "A tool to lift x86 binary code into logic, unrolling loops as needed."
  :args ((lifted-name "A symbol, the name to use for the generated function.  The name of the generated constant is created by adding stars to the front and back of this symbol.")
         (executable "The x86 binary executable that contains the target function.  Usually a string (a filename), or this can be a parsed executable of the form created by defconst-x86.")
         (target "Where to start lifting (a numeric offset, the name of a subroutine (a string), or the symbol :entry-point)")
         (extra-assumptions "Extra assumptions for lifting, in addition to the standard-assumptions")
         (suppress-assumptions "Whether to suppress the standard assumptions.  This does not suppress any assumptions generated about the :inputs.")
         (inputs-disjoint-from "What to assume about the inputs (specified using the :inputs option) being disjoint from the sections/segments in the executable.  The value :all means assume the inputs are disjoint from all sections/segments.  The value :code means assume the inputs are disjoint from the code/text section.  The value nil means do not include any assumptions of this kind.")
         (stack-slots "How much available stack space to assume exists.") ; 4 or 8 bytes each?
         (existing-stack-slots "How much available stack space to assume exists.  Usually at least 1, for the saved return address.") ; 4 or 8 bytes each?
         (position-independent "Whether to attempt the lifting without assuming that the binary is loaded at a particular position.")
         (inputs "Either the special value :skip (meaning generate no additional assumptions on the input) or a doublet list pairing input names with types.  Types include things like u32, u32*, and u32[2].")
         (type-assumptions-for-array-vars "Whether to put in type assumptions for the variables that represent elements of input arrays.")
         (output "An indication of which state component(s) will hold the result of the computation being lifted.  See output-indicatorp.")
         (use-internal-contextsp "Whether to use contextual information from ovararching conditionals when simplifying DAG nodes.")
         ;; todo: better name?  only for precise pruning:
         (prune-precise "Whether to prune DAGs using precise contexts.  Either t or nil or a natural number representing the smallest dag size that we deem too large for pruning (where here the size is the number of nodes in the corresponding term).  This kind of pruning can blow up if attempted for DAGs that represent huge terms.")
         (prune-approx "Whether to prune DAGs using approximate contexts.  Either t or nil or a natural number representing the smallest dag size that we deem too large for pruning (where here the size is the number of nodes in the corresponding term).  This kind of pruning should not blow up but doesn't use fully precise contextual information.")
         ;; todo: how do these affect assumption simp:
         (extra-rules "Rules to use in addition to (unroller-rules32) or (unroller-rules64) plus a few others.")
         (remove-rules "Rules to turn off.")
         (extra-assumption-rules "Extra rules to be used when simplifying assumptions.")
         (remove-assumption-rules "Rules to be removed when simplifying assumptions.")
         (step-limit "Limit on the total number of symbolic executions steps to allow (total number of steps over all branches, if the simulation splits).")
         (step-increment "Number of model steps to allow before pausing to simplify the DAG and remove unused nodes.")
         (stop-pcs "A list of program counters (natural numbers) at which to stop the execution, for debugging.")
         (memoizep "Whether to memoize during rewriting (when not using contextual information -- as doing both would be unsound).")
         (monitor "Rule names (symbols) to be monitored when rewriting.") ; during assumptions too?
         (normalize-xors "Whether to normalize BITXOR and BVXOR nodes when rewriting (t, nil, or :compact).")
         (count-hits "Whether to count rule hits during rewriting (t means count hits for every rule, :total means just count the total number of hits, nil means don't count hits)")
         (print "Verbosity level.") ; todo: values
         (print-base "Base to use when printing during lifting.  Must be either 10 or 16.")
         (untranslatep "Whether to untranslate term when printing.")
         (produce-function "Whether to produce a function, not just a constant DAG, representing the result of the lifting.")
         (non-executable "Whether to make the generated function non-executable, e.g., because stobj updates are not properly let-bound.  Either t or nil or :auto.")
         (produce-theorem "Whether to try to produce a theorem (possibly skip-proofed) about the result of the lifting.")
         (prove-theorem "Whether to try to prove the theorem with ACL2 (rarely works, since Axe's Rewriter is different and more scalable than ACL2's rewriter).")
         (restrict-theory "To be deprecated...")
         (bvp "Whether to use new-style, BV-friendly assumptions.")
         )
  :description ("Lift some x86 binary code into an ACL2 representation, by symbolic execution including inlining all functions and unrolling all loops."
                "Usually, @('def-unrolled') creates both a function representing the lifted code (in term or DAG form, depending on the size) and a @(tsee defconst) whose value is the corresponding DAG (or, rarely, a quoted constant).  The function's name is @('lifted-name') and the @('defconst')'s name is created by adding stars around  @('lifted-name')."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))
