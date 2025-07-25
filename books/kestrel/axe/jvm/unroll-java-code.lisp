; A tool to unroll Java code
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

;; TODO: The JVM lifters use debugging information (which may or may not be
;; present) in the .class file, to choose names for parameters of generated
;; functions (using default names param0, param1, etc. if no debugging
;; information is present).  To prevent confusion, we could require an explicit
;; user option to allow lifting files without debugging information.  This
;; would serve as a clear reminder to users to compile with the -g flag. (But
;; then is such a check all-or-nothing, or might some methods have the
;; information and others not have it?).

(include-book "unroll-java-code-common")
(include-book "nice-output-indicators")
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/defmacrodoc" :dir :system)
(include-book "kestrel/utilities/check-boolean" :dir :system)
(include-book "kestrel/utilities/rational-printing" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)
(include-book "../make-term-into-dag-basic")
(include-book "rewriter-jvm")
(include-book "../make-evaluator") ; for make-acons-nest, todo
(include-book "../supporting-functions")
;(include-book "../rewriter") ; for simp-dag
(include-book "../evaluator") ; for *axe-evaluator-functions* and dag-val-with-axe-evaluator
(include-book "../prune-dag-approximately") ;brings in rewriter-basic
(include-book "../prune-dag-precisely") ;brings in rewriter-basic
(include-book "../dag-info")
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

(local (in-theory (enable symbolp-of-lookup-equal-when-param-slot-to-name-alistp)))

(local (in-theory (disable acl2-count ;for speed
                           )))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; Returns a boolean
(defun dag-ok-after-symbolic-execution (dag assumptions error-on-incomplete-runsp state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              ;; assumptions
                              (booleanp error-on-incomplete-runsp)
                              )
                  :stobjs state))
;  (declare (xargs :mode :program)) ; because this calls untranslate
  (let ((dag-fns (dag-fns dag)))
    (if (or (member-eq 'run-until-return-from-stack-height dag-fns) ;todo: pass in a set of functions to look for?
            (member-eq 'jvm::run-n-steps dag-fns)
            (member-eq 'jvm::do-inst dag-fns)
            (member-eq 'jvm::error-state dag-fns))
        (progn$ (if (dag-or-quotep-size-less-thanp! dag 10000)
                    (progn$ (cw "(Result Term:~%")
                            (cw "~X01" (untranslate$ (dag-to-term dag) nil state) nil)
                            (cw ")~%"))
                  (cw "(Result DAG: ~x0)~%" dag))
                (cw "(Assumptions were: ~x0)~%" assumptions)
                (and error-on-incomplete-runsp
                     ;; todo: pass in ctx:
                     (er hard? 'unroll-java-code-fn "ERROR: Symbolic simulation did not seem to finish (see DAG and assumptions above).")))
      t)))

;; Works for terms or dag-exprs
(defund elide-make-frame-args (fn args)
  (declare (xargs :guard t)) ;strengthen?
  (if (and (eq fn 'jvm::make-frame)
           (= 6 (len args))
           ;; for termination:
           (myquotep (fifth args))
           (consp (unquote (fifth args)))
           )
      (list (first args)
            (second args)
            (third args)
            (fourth args)
            '':method-info-elided ;; (fifth args)
            (sixth args))
    args))

(defthm pseudo-term-listp-of-elide-make-frame-args
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (elide-make-frame-args fn args)))
  :hints (("Goal" :in-theory (enable elide-make-frame-args))))

(defthm len-of-elide-make-frame-args
  (equal (len (elide-make-frame-args fn args))
         (len args))
  :hints (("Goal" :in-theory (enable elide-make-frame-args))))

(mutual-recursion
 (defun elide-method-info-in-term (term)
   (declare (xargs :guard t  ; or require pseudo-termp, but that might take time to check?
                   :hints (("Goal" :in-theory (enable elide-make-frame-args)))))
   (if (or (not (consp term)) ; var
           (eq 'quote (ffn-symb term)))
       term
     (let* ((fn (ffn-symb term))
            (args (elide-make-frame-args fn (fargs term)))
            (new-args (elide-method-info-in-terms args)))
       (cons fn new-args))))
 (defun elide-method-info-in-terms (terms)
   (declare (xargs :guard t)) ; or require pseudo-term-listp, but that might take time to check?
   (if (not (consp terms))
       nil
     (cons (elide-method-info-in-term (first terms))
           (elide-method-info-in-terms (rest terms))))))

(local (make-flag elide-method-info-in-term :hints (("Goal" :in-theory (enable elide-make-frame-args)))))

(defthm-flag-elide-method-info-in-term)

(defthm len-of-elide-method-info-in-terms
  (equal (len (elide-method-info-in-terms terms))
         (len terms))
  :hints (("Goal" :in-theory (enable (:i len)))))

(defthm-flag-elide-method-info-in-term
  (defthm pseudo-termp-of-elide-method-info-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (elide-method-info-in-term term)))
    :flag elide-method-info-in-term)
  (defthm pseudo-term-listp-of-elide-method-info-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (elide-method-info-in-terms terms)))
    :flag elide-method-info-in-terms))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defund print-dag-array-with-elided-method-info-aux (nodenum dag-array-name dag-array first-elementp)
;;   (declare (xargs :guard (and (integerp nodenum)
;;                               (<= -1 nodenum)
;;                               (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))
;;                   :measure (+ 1 (nfix (+ 1 nodenum)))
;; ;                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
;;                   :split-types t)
;;            (type integer nodenum))
;;   (if (or (< nodenum 0)
;;           (not (mbt (integerp nodenum))))
;;       nil
;;     (let* ((expr (aref1 dag-array-name dag-array nodenum))
;;            (expr (or (not (consp expr))
;;                      (eq 'quote (ffn-symb expr)))
;;                  expr
;;                  (let ((fn (ffn-symb expr)))
;;                    (cons fn (elide-make-frame-args fn (cdr expr))))))
;;       (progn$ (if (not first-elementp) (cw "~% ") nil)
;;               (cw "~F0" (cons nodenum expr)) ;; TODO: Avoid this cons?
;;               (print-dag-array-with-elided-method-info-aux (+ -1 nodenum)
;;                                        dag-array-name
;;                                        dag-array
;;                                        nil)))))

;; ;; Print the entire dag, from NODENUM down to 0, including nodes not supporting NODENUM, if any.
;; (defund print-dag-array-with-elided-method-info (nodenum dag-array-name dag-array)
;;   (declare (xargs :guard (and (integerp nodenum)
;;                               (<= -1 nodenum)
;;                               (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))))
;;   (progn$ (cw "(")
;;           (print-dag-array-with-elided-method-info-aux nodenum dag-array-name dag-array t)
;;           (cw ")~%")))

(defund print-dag-with-elided-method-info-aux (dag first-elementp)
  (declare (xargs :guard (and (weak-dagp-aux dag)
                              (booleanp first-elementp))))
  (if (endp dag)
      nil
    (let* ((entry (first dag))
           (nodenum (car entry))
           (expr (cdr entry))
           (expr (if (or (not (consp expr))
                         (eq 'quote (ffn-symb expr)))
                     expr
                   (let ((fn (ffn-symb expr)))
                     (cons fn (elide-make-frame-args fn (cdr expr)))))))
      (progn$ (if (not first-elementp) (cw "~% ") nil)
              (cw "~F0" (cons nodenum expr)) ;; TODO: Avoid this cons?
              (print-dag-with-elided-method-info-aux (rest dag) nil)))))

;; Print the entire dag, from NODENUM down to 0, including nodes not supporting NODENUM, if any.
(defund print-dag-with-elided-method-info (dag)
  (declare (xargs :guard (weak-dagp-aux dag)))
  (progn$ (cw "(")
          (print-dag-with-elided-method-info-aux dag t)
          (cw ")~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable ilks-plist-worldp w)))

(defthm count-hits-argp-when-booleanp
  (implies (booleanp x)
           (count-hits-argp x))
  :hints (("Goal" :in-theory (enable count-hits-argp booleanp))))

(defthm not-quotep-forward-to-not-myquotep
  (implies (not (quotep x))
           (not (myquotep x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable myquotep))))

(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(local
  (defthm min-helper
    (<= (min x y) x)))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or unsupported instruction is detected.  Returns (mv
;; erp result-dag-or-quotep state).
(defund repeatedly-run (dag
                        steps-left
                        step-increment
                        rule-alists
                        assumptions
                        normalize-xors
                        rules-to-monitor
                        ;;use-internal-contextsp
                        print
                        print-interval
                        memoizep
                        prune-precise
                        prune-approx ; currently pruning is too slow for proofs like DES
                        total-steps
                        state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (natp steps-left)
                              (step-incrementp step-increment)
                              (rule-alistsp rule-alists)
                              (pseudo-term-listp assumptions)
                              (booleanp normalize-xors)
                              (symbol-listp rules-to-monitor)
;                              (booleanp use-internal-contextsp)
                              (print-levelp print)
                              (booleanp memoizep)
                              (prune-precise-optionp prune-precise)
                              (prune-approx-optionp prune-approx)
                              (natp total-steps)
                              (ilks-plist-worldp (w state)))
;                  :mode :program ;; because we call untranslate
                  :measure (nfix steps-left)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (e/d (true-listp-when-symbol-listp-rewrite-unlimited)
                                                        (myquotep ;looped
                                                         quotep
                                                         min
                                                         ))))
                  )
           (irrelevant print-interval) ; todo
           )
  (if (or (zp steps-left)
          (not (mbt (and (step-incrementp step-increment)
                         (natp total-steps)))))
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         (old-dag dag)
         (limits `((step-state-with-pc-and-call-stack-height-becomes-step-axe . ,steps-for-this-iteration)
                   (run-until-return-from-stack-height-opener-fast-axe . ,steps-for-this-iteration)))
         ;; ((mv erp dag-or-quotep state)
         ;;  (simp-dag dag
         ;;            :assumptions assumptions
         ;;            :rule-alists rule-alists
         ;;            :use-internal-contextsp t ;new!
         ;;            :print (reduce-print-level print)         ;(if monitored-rules t nil)
         ;;            :print-interval print-interval
         ;;            :monitor rules-to-monitor
         ;;            :normalize-xors normalize-xors
         ;;            :memoizep memoizep
         ;;            ;;:exhaustivep (if chunkedp t nil)
         ;;            ;; todo: do we need both of these?:
         ;;            :limits limits
         ;;            :check-inputs nil))
         ((mv erp dag-or-quotep
              & ;limits
              )
          (acl2::simplify-dag-with-rule-alists-jvm dag
                                                   assumptions
                                                   rule-alists
                                                   nil ; interpreted-function-alist
                                                   (acl2::known-booleans (w state))
                                                   normalize-xors
                                                   limits
                                                   memoizep
                                                   (print-level-at-least-verbosep print) ; count-hits ; todo: pass in separately
                                                   (reduce-print-level print)
                                                   rules-to-monitor
                                                   nil ; no-warn-ground-functions
                                                   '(program-at) ; fns-to-elide
                                                   ))
         ((when erp) (mv erp dag state))
         ((when (quotep dag-or-quotep))
          (cw "Note: The run produced the constant ~x0.~%" dag-or-quotep)
          (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; renames it, since we know it's not a quotep
         ;; todo: which kind(s) of pruning should we use?  this is our chance to apply STP to prune away impossible branches.
         ((mv erp dag-or-quotep state)
          (maybe-prune-dag-approximately prune-approx dag assumptions print
                                         60000 ; todo: pass in
                                         state))
         ((when erp) (mv erp dag state))
         ((when (quotep dag-or-quotep))
          (cw "Note: The run produced the constant ~x0.~%" dag-or-quotep)
          (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; renames it, since we know it's not a quotep
         ((mv erp dag-or-quotep state) (maybe-prune-dag-precisely prune-precise
                                                                  dag
                                                                  assumptions
                                                                  nil ; todo: use some rules?
                                                                  :none ; todo: pass a rule-alist here?
                                                                  nil ; todo?
                                                                  nil
                                                                  t ; call-stp
                                                                  print
                                                                  state))
         ((when erp) (mv erp dag state))
         ((when (quotep dag-or-quotep))
          (cw "Note: The run produced the constant ~x0.~%" dag-or-quotep)
          (mv (erp-nil) dag-or-quotep state))
         (dag dag-or-quotep) ; renames it, since we know it's not a quotep
         (dag-fns (dag-fns dag)))
      (if (not (or (member-eq 'run-until-return-from-stack-height dag-fns)
                   (member-eq 'jvm::run-n-steps dag-fns)
                   (member-eq 'jvm::do-inst dag-fns))) ;; stop if the run is done
          (prog2$ (cw "Note: The run has completed.~%")
                  (mv (erp-nil) dag state))
        (if nil ;todo: (member-eq 'x86isa::x86-step-unimplemented dag-fns) ;; stop if we hit an unimplemented instruction
            (prog2$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                    (mv (erp-nil) dag state))
          (b* (((mv erp equivalentp)
                (equivalent-dagsp2 dag old-dag))
               ((when erp) (mv erp dag state))
               ((when equivalentp)
                (cw "Note: Stopping the run because nothing changed.~%")
                (and print
                     (prog2$ (cw "(DAG:~%")
                             (cw "~X01)" dag nil)))
                (mv (erp-nil) dag state))
               (total-steps (+ steps-for-this-iteration total-steps))
               (- (and print
                       (if (eq :brief print)
                           (cw "(~x0 steps done.):~%" total-steps)
                         ;; Print as a term unless it would be huge:
                         (if (dag-or-quotep-size-less-thanp! dag 1000)
                             (progn$ (cw "(Term after ~x0 steps:~%" total-steps)
                                     (cw "~X01" (untranslate$ (elide-method-info-in-term (dag-to-term dag)) nil state) nil)
                                     (cw ")~%"))
                           (progn$ (cw "(DAG after ~x0 steps:~%" total-steps)
                                   (print-dag-with-elided-method-info dag)
                                   (cw ")")))))))
            (repeatedly-run dag
                            (- steps-left steps-for-this-iteration)
                            step-increment rule-alists assumptions normalize-xors rules-to-monitor ; use-internal-contextsp
                            print
                            print-interval
                            memoizep
                            prune-precise
                            prune-approx
                            total-steps
                            state)))))))

(defthm pseudo-dagp-of-mv-nth-1-of-repeatedly-run
  (implies (and (pseudo-dagp dag)
                (natp steps-left)
                (step-incrementp step-increment)
                (rule-alistsp rule-alists)
                (pseudo-term-listp assumptions)
                (booleanp normalize-xors)
                (symbol-listp rules-to-monitor)
;                              (booleanp use-internal-contextsp)
                (print-levelp print)
                (booleanp memoizep)
                ;; (prune-precise-optionp prune-precise)
                ;; (prune-approx-optionp prune-approx)
                (natp total-steps)
                (ilks-plist-worldp (w state)))
           (equal (pseudo-dagp (mv-nth 1 (repeatedly-run dag steps-left step-increment rule-alists assumptions normalize-xors rules-to-monitor print print-interval memoizep prune-precise prune-approx total-steps state)))
                  (not (quotep (mv-nth 1 (repeatedly-run dag steps-left step-increment rule-alists assumptions normalize-xors rules-to-monitor print print-interval memoizep prune-precise prune-approx total-steps state))))))
  :hints (("Goal" :induct t
           :in-theory (e/d (repeatedly-run)
                           (myquotep ; todo: loop with SIMPLIFY-DAG-WITH-RULE-ALISTS-JVM-RETURN-TYPE1-COROLLARY2
                            quotep
                            min)))))

(defthm w-of-mv-nth-2-of-repeatedly-run
  (equal (w (mv-nth 2 (repeatedly-run dag steps-left step-increment rule-alists assumptions normalize-xors rules-to-monitor print print-interval memoizep prune-precise prune-approx total-steps state)))
         (w state))
  :hints (("Goal" :in-theory (enable repeatedly-run))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Chunked execution can be necessary to make use of overarching if-conditions.
;; For example, we may have a test that ensures that a later loop terminates.

(local
  (in-theory (disable unroll-java-code-rules (:e unroll-java-code-rules)
                      natp
                      nat-listp
                      alistp
                      strip-cars
                      symbol-alistp
                      make-param-slot-to-name-alist
                      make-param-slot-to-name-alist-aux
                      jvm::all-keys-bound-to-method-infosp
                      parameter-assumptions
                      build-run-term-for-method2
                      build-make-state-for-method
                      jvm::method-staticp
                      jvm::method-namep
                      method-designator-stringp
                      no-duplicatesp-equal ; why?
                      strip-cars-of-non-consp
                      assoc-equal-when-member-equal-of-strip-cars
                      subsetp-equal
                      ilks-plist-worldp-forward-to-plist-worldp
                      default-car
                      default-cdr
                      ;; pseudo-term-listp
                      state-p
                      )))

(local (in-theory (enable symbol-listp-of-strip-cars-when-array-length-alistp
                          lookup-equal-when-class-table-alistp-iff
                          symbol-listp-of-strip-cdrs-when-param-slot-to-name-alistp
                          alistp-when-param-slot-to-name-alistp)))

(local
  (defthm eqlable-listp-when-symbol-listp
    (implies (symbol-listp x)
             (eqlable-listp x))))

;; This is separate to avoid causing case splits in the slow guard proof for unroll-java-code-fn-aux.
(defund classes-to-assume-initialized-optionp (classes-to-assume-initialized)
  (declare (xargs :guard t))
  (or (eq :all classes-to-assume-initialized)
      (jvm::all-class-namesp classes-to-assume-initialized)))

;; This is separate to avoid causing case splits in the slow guard proof for unroll-java-code-fn-aux.
(defund choose-classes-to-assume-initialized (classes-to-assume-initialized class-alist)
  (declare (xargs :guard (and (classes-to-assume-initialized-optionp classes-to-assume-initialized)
                              (class-table-alistp class-alist))))
  (if (eq :all classes-to-assume-initialized)
      (strip-cars class-alist)
    classes-to-assume-initialized))

(defund steps-optionp (steps)
  (declare (xargs :guard t))
  (or (eq :auto steps)
      (natp steps)))

(defund branches-optionp (branches)
  (declare (xargs :guard t))
  (or (eq :smart branches)
      (eq :split branches)))

(defund choose-symbolic-execution-rules (steps branches)
  (declare (xargs :guard (and (steps-optionp steps)
                              (or (eq :smart branches)
                                  (eq :split branches)))))
  (if (eq :auto steps)
      (if (eq branches :smart)
          (run-until-return-from-stack-height-rules-smart)
        (if (eq branches :split)
            (run-until-return-from-stack-height-rules-split)
          (er hard? 'unroll-java-code-fn "Illegal value for :branches: ~x0.  Must be :smart or :split." branches)))
    (symbolic-execution-rules-for-run-n-steps) ;todo: add a :smart analogue of this rule set
    ))

(defthm symbol-listp-of-choose-symbolic-execution-rules
  (symbol-listp (choose-symbolic-execution-rules steps branches))
  :hints (("Goal" :in-theory (enable choose-symbolic-execution-rules))))

;; Returns (mv erp dag all-assumptions term-to-run-with-output-extractor dag-fns parameter-names state).
;; This uses all classes currently in the global-class-alist.
;; Why does this return the dag-fns?
;; Consider
;; (set-inhibit-output-lst '(proof-tree event))
;;when working with this function.
;; Very slow guard proof
(defun unroll-java-code-fn-aux (method-designator-string
                                nice-output-indicator
                                array-length-alist
                                extra-rules  ;to add to default set
                                remove-rules ;to remove from default set
                                rule-alists
                                monitored-rules
                                user-assumptions
                                normalize-xors
                                classes-to-assume-initialized
                                ignore-exceptions
                                ignore-errors
                                print
                                print-interval
                                memoizep
                                vars-for-array-elements
                                prune-precise
                                prune-approx ; todo: separate options for pruning during a run (can be slow) vs at the end?
                                call-stp ;t, nil, or a max-conflicts
                                steps
                                branches
                                param-names ; may be :auto
                                chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                                error-on-incomplete-runsp ;whether to throw a hard error (may be nil if further pruning can be done in the caller)
                                state)
  (declare (xargs :guard (and (method-designator-stringp method-designator-string)
                              (nice-output-indicatorp nice-output-indicator)
                              (array-length-alistp array-length-alist)
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (rule-alistsp rule-alists)
                              (symbol-listp monitored-rules)
                              (pseudo-term-listp user-assumptions)
                              (booleanp normalize-xors)
                              (classes-to-assume-initialized-optionp classes-to-assume-initialized)
                              (booleanp ignore-exceptions)
                              (booleanp ignore-errors)
                              (print-levelp print)
                              ;; print-interval -- drop?
                              (booleanp memoizep)
                              (member-eq vars-for-array-elements '(t nil :bits))
                              (prune-precise-optionp prune-precise)
                              (prune-approx-optionp prune-approx)
                              (call-stp-optionp call-stp)
                              (steps-optionp steps)
                              (branches-optionp branches)
                              (or (eq :auto param-names)
                                  (symbol-listp param-names)) ;todo: check for dups and keywords and case clashes
                              (booleanp chunkedp)
                              (booleanp error-on-incomplete-runsp)
                              (ilks-plist-worldp (w state)))
                  :stobjs state
;                  :verify-guards nil ; todo: works but slow!
                  ;; :guard-simplify :limited
                  :guard-hints (("Goal" :in-theory (e/d (symbol-listp-of-unroll-java-code-rules
                                                         steps-optionp ; todo
                                                         )
                                                        (quotep
                                                         myquotep
                                                         integerp-of-nth-when-all-natp))
                                 ;:do-not '(preprocess)
                                 ))))
  (b* ((method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string)) ;todo: should this be called a descriptor?
       ((when (not (jvm::method-descriptorp method-descriptor)))
        (mv :bad-descriptor nil nil nil nil nil state))
       ;; TODO: If only one method with that name, just put in its descriptor
       ((when (equal method-descriptor ""))
        (mv t
            (er hard? 'unroll-java-code-fn "Method descriptor is missing in ~x0." method-designator-string)
            nil nil nil nil
            state))
       (class-alist (jvm::global-class-alist state))
       ((when (not (class-table-alistp class-alist)))
        (mv :bad-global-class-alist nil nil nil nil nil state))
       ((when (not (assoc-equal method-class class-alist)))
        (mv t
            (er hard? 'unroll-java-code-fn "Class ~x0 not found." method-class)
            nil nil nil nil
            state))
       (class-info (lookup-equal method-class class-alist))
       ((when (not (jvm::class-infop0 class-info))) ; drop?
        (mv :bad-class-info nil nil nil nil nil state))
       (method-info-alist (jvm::class-decl-methods class-info))
       (method-id (cons method-name method-descriptor))
       ((when (not (assoc-equal method-id method-info-alist)))
        (mv t
            (er hard? 'unroll-java-code-fn "Method ~x0 not found." method-id)
            nil nil nil nil
            state))
       (method-info (lookup-equal method-id method-info-alist))
       ((when (not (jvm::method-infop method-info)))
        (mv :bad-method-info nil nil nil nil nil state))
       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info param-names))
       (parameter-names (strip-cdrs param-slot-to-name-alist)) ; the actual names used
       (class-table-term (make-class-table-term-compact class-alist 'initial-class-table))
       (locals-term 'locals)
       (initial-heap-term 'initial-heap)
       (initial-intern-table-term 'initial-intern-table)
       ;; TODO: Not quite right.  Need to allow the byte- or bit-blasted array var names (todo: what about clashes between those and the other param names?):
       ;; (assumption-vars (free-vars-in-terms user-assumptions))
       ;; (allowed-assumption-vars (append parameter-names
       ;;                                  '(locals initial-heap initial-static-field-map and initial-intern-table)))
       ;; ((when (not (subsetp-eq assumption-vars allowed-assumption-vars)))
       ;;  (er hard? 'unroll-java-code-fn-aux "Disallowed variables in assumptions, ~x0.  The only allowed vars are ~x1." user-assumptions allowed-assumption-vars)
       ;;  (mv :bad-assumption-vars nil nil nil nil nil state))
       (user-assumptions (desugar-calls-of-contents-in-terms user-assumptions initial-heap-term))
       ;; todo: have this return all the var names created for array components/bits:
       (parameter-assumptions (parameter-assumptions method-info array-length-alist locals-term initial-heap-term
                                                     vars-for-array-elements
                                                     param-slot-to-name-alist
                                                     method-designator-string))
       (all-assumptions (append `((jvm::heapp ,initial-heap-term) ;assume the heap is well-formed
                                  (jvm::intern-tablep ,initial-intern-table-term) ;assume the intern-table is well-formed
                                  )
                                user-assumptions
                                parameter-assumptions))
       (- (and print (cw "(Parameter names are: ~x0.)~%" parameter-names)))
       ((when (not (no-duplicatesp parameter-names)))
        (mv t
            (er hard? 'unroll-java-code-fn "We don't yet support lifting methods with parameter names that differ only in case, but method ~x0 has params ~x1." method-name parameter-names)
            nil nil nil nil
            state))
       ((when (not (subsetp-eq (strip-cars array-length-alist) parameter-names)))
        (mv t
            (er hard? 'unroll-java-code-fn "Bad :array-length-alist: ~x0.  Should only mention params ~x1.  Note that param names may depend on whether debugging info is present in the .class file." array-length-alist parameter-names)
            nil nil nil nil
            state))
       (- (and print (cw "(Parameter assumptions: ~x0.)~%" parameter-assumptions)))
       (classes-to-assume-initialized (choose-classes-to-assume-initialized classes-to-assume-initialized class-alist))
       (- (and print (cw "(Assuming the following classes are initialized: ~x0.)~%" classes-to-assume-initialized)))

       ;; TODO: The term generated here could be improved by using a let:
       (term-to-run (if (eq :auto steps)
                        (build-run-term-for-method2
                          method-name
                          method-descriptor
                          method-info
                          locals-term
                          method-class
                          initial-heap-term
                          class-table-term
                          'initial-static-field-map
                          ;;fixme currently cheating since java.lang.Object's <clinit> method calls registerNatives, and java.lang.System makes more calls we don't handle:
                          ;;also for now, i guess we are nailing this down so as not to have to split cases depending on which classes have been initialized:
                          (enquote classes-to-assume-initialized)
                          initial-intern-table-term)
                      (build-run-n-steps-term-for-method
                        steps
                        method-name
                        method-descriptor
                        method-info
                        locals-term
                        method-class
                        initial-heap-term
                        class-table-term
                        'initial-static-field-map
                        ;;fixme currently cheating since java.lang.Object's <clinit> method calls registerNatives, and java.lang.System makes more calls we don't handle:
                        ;;also for now, i guess we are nailing this down so as not to have to split cases depending on which classes have been initialized:
                        (enquote classes-to-assume-initialized)
                        'initial-intern-table)))
       (return-type (lookup-eq :return-type method-info))
       ((when (not (or (eq :void return-type)
                       (jvm::typep return-type))))
        (mv :bad-return-type nil nil nil nil nil state))
       (parameter-types (lookup-eq :parameter-types method-info))
       ;; Handle an output-indicator of :rv or a param-name:
       (simple-output-indicator (desugar-nice-output-indicator nice-output-indicator param-slot-to-name-alist parameter-types return-type))
       ((when (not simple-output-indicator))
        (mv :failed-to-resolve-output-indicator nil nil nil nil nil state))
       ;;todo: can we call output-extraction-term here?
       (term-to-run-with-output-extractor (wrap-term-with-output-extractor simple-output-indicator ;return-type
                                                                           locals-term term-to-run class-alist))
       ;; Decide which symbolic execution rule to use:
       (symbolic-execution-rules (choose-symbolic-execution-rules steps branches))
       ;; todo: if rule-alists are applied, should we at least include the symbolic-execution-rules?
       ((mv erp rule-alists)
        (if rule-alists ;use user-supplied rule-alists, if any
            (mv (erp-nil) rule-alists)
          ;; by default, we use 1 rule-alist:
          ;; todo: pre-compute each possibility here (but what about priorities?)
          (b* (((mv erp rule-alist)
                (make-rule-alist (append (unroll-java-code-rules)
                                         symbolic-execution-rules)
                                 (w state)))
               ((when erp) (mv erp nil)))
            (mv (erp-nil) (list rule-alist)))))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;; maybe add some rules (can't call add-to-rule-alists because these are not theorems in the world):
       (rule-alists (extend-rule-alists2 ;; Maybe include the ignore-XXX rules:
                      (append (and ignore-exceptions *ignore-exception-axe-rule-set*)
                              (and ignore-errors *ignore-error-state-axe-rule-set*))
                      rule-alists
                      (w state)))
       ;; Include any :extra-rules given:
       ((mv erp rule-alists) (add-to-rule-alists extra-rules rule-alists (w state)))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;; Exclude any :remove-rules given:
       (rule-alists (remove-from-rule-alists remove-rules rule-alists))
       ;; Simplify the assumptions using themselves (example: an automatic
       ;; assumption replaces an array's contents with a var, and a user
       ;; assumption replaces that var with another term):
       ((mv erp all-assumptions)
        (acl2::simplify-conjunction-with-rule-alists-basic ;simplify-terms-repeatedly
          all-assumptions
          (remove-from-rule-alists '(unsigned-byte-p-when-array-refp) rule-alists) ; could use a separate rules for this assumption simplification
          (acl2::known-booleans (w state))
          nil ; rules-to-monitor ; do we want to monitor here?  What if some rules are not included?
          nil ; no-warn-ground-functions
          nil ; don't memoize (avoids time spent making empty-memoizations)
          (print-level-at-least-tp print) ; count-hits ; todo: pass in
          t   ; todo: warn just once
          ))
       ((when erp) (mv erp nil nil nil nil nil state))
       (- (and (print-level-at-least-tp print)
               (cw "(Simplified assumptions:~%~X01" all-assumptions nil)))
       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (make-term-into-dag-basic term-to-run-with-output-extractor nil))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((when (quotep dag-to-simulate)) ; todo: return it?
        (mv :unexpected-quotep nil nil nil nil nil state))
       (step-limit 1000000)
       (step-increment (if chunkedp 100 1000000)) ; todo: let the chunk size be configurable
       ((mv erp dag state)
        (repeatedly-run dag-to-simulate
                        step-limit
                        step-increment
                        rule-alists
                        all-assumptions
                        normalize-xors
                        monitored-rules
                        print
                        print-interval
                        memoizep
                        prune-precise
                        prune-approx
                        0
                        state))
       ((when erp)
        (er hard? 'unroll-java-code-fn "Error in unrolling.")
        (mv erp nil nil nil nil nil state))
       ((when (quotep dag)) ; todo: test this case
        (mv (erp-nil) dag all-assumptions term-to-run-with-output-extractor nil parameter-names state))
       ;;; Prune irrelevant branches, if instructed:
       ;; TODO: Consider calling prune-dag-approximately here:
       ;; TODO: Consider making this final pruning a separate option
       ((mv erp dag state)
        (maybe-prune-dag-precisely prune-precise
                                   dag
                                   all-assumptions ;are they all needed?
                                   :none ; we give a rule-alist instead
                                   (first rule-alists) ;what should we use here?
                                   nil ; interpreted-function-alist
                                   monitored-rules
                                   call-stp
                                   print
                                   state))
       ((when erp) (mv erp nil nil nil nil nil state))
       ((when (quotep dag)) ; todo: test this case
        (mv (erp-nil) dag all-assumptions term-to-run-with-output-extractor nil parameter-names state))
       ;; Check whether symbolic execution failed:
       (dag-okp (dag-ok-after-symbolic-execution dag all-assumptions error-on-incomplete-runsp state)))
    (mv (if (and (not dag-okp)
                 error-on-incomplete-runsp)
            (erp-t)
          (erp-nil))
        dag all-assumptions term-to-run-with-output-extractor (dag-fns dag) parameter-names state)))

;; Returns (mv erp event state).
(defun unroll-java-code-fn (defconst-name
                             method-indicator
                             nice-output-indicator
                             array-length-alist
                             extra-rules ;to add to default set
                             remove-rules ;to remove from default set
                             rule-alists
                             monitored-rules
                             user-assumptions
                             normalize-xors
                             classes-to-assume-initialized
                             ignore-exceptions
                             ignore-errors
                             print
                             print-interval
                             memoizep
                             vars-for-array-elements
                             prune-precise
                             prune-approx
                             call-stp ;t, nil, or a max-conflicts
                             produce-theorem
                             steps
                             branches
                             param-names
                             produce-function
                             chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                             whole-form
                             state)
  (declare (xargs :guard (and (nice-output-indicatorp nice-output-indicator)
                              (jvm::method-indicatorp method-indicator)
                              (or (eq :all classes-to-assume-initialized)
                                  (jvm::all-class-namesp classes-to-assume-initialized))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (all-rule-alistp rule-alists)
                              (symbol-listp monitored-rules)
                              (array-length-alistp array-length-alist)
                              (booleanp memoizep)
                              (member-eq vars-for-array-elements '(t nil :bits))
                              (prune-precise-optionp prune-precise)
                              (prune-approx-optionp prune-approx)
                              (call-stp-optionp call-stp)
                              (booleanp produce-theorem)
                              (booleanp produce-function)
                              (or (eq :auto steps)
                                  (natp steps))
                              (or (eq :smart branches)
                                  (eq :split branches))
                              (or (eq :auto param-names)
                                  (symbol-listp param-names)) ;todo: check for dups and keywords and case clashes
                              (booleanp chunkedp)
                              (booleanp normalize-xors))
                  :stobjs state
                  :mode :program ;because of FRESH-NAME-IN-WORLD-WITH-$S, and TRANSLATE-TERMS
                  ))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ;; check the name that will be defined:
       ((mv erp & state) (chk-fresh-namep defconst-name 'const 'unroll-java-code (w state) state))
       ((when erp) (mv erp nil state))
       ;; Check inputs:
       ((when (and produce-theorem (not produce-function)))
        (er hard? 'unroll-java-code-fn "When :produce-theorem is t, :produce-function must also be t.")
        (mv (erp-t) nil state))
       (user-assumptions (translate-terms user-assumptions 'unroll-java-code-fn (w state))) ;throws an error on bad input
       ;; Record the start time:
       ((mv start-time state) (acl2::get-real-time state))
       ;; Adds the descriptor if omitted and unambiguous:
       (method-designator-string (jvm::elaborate-method-indicator method-indicator (jvm::global-class-alist state)))
       ;; Printed even if print is nil (seems ok):
       (- (cw "(Unrolling ~x0.~%"  method-designator-string))
       ((mv erp dag-or-quotep all-assumptions term-to-run-with-output-extractor dag-fns parameter-names state)
        (unroll-java-code-fn-aux method-designator-string
                                 nice-output-indicator
                                 array-length-alist
                                 extra-rules ;to add to default set
                                 remove-rules ;to remove from default set
                                 rule-alists
                                 monitored-rules
                                 user-assumptions
                                 normalize-xors
                                 classes-to-assume-initialized
                                 ignore-exceptions
                                 ignore-errors
                                 print
                                 print-interval
                                 memoizep
                                 vars-for-array-elements
                                 prune-precise
                                 prune-approx
                                 call-stp ;t, nil, or a max-conflicts
                                 steps
                                 branches
                                 param-names
                                 chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                                 t ;error on incomplete runs
                                 state))
       ((when erp) (mv erp nil state))
       (- (and (quotep dag-or-quotep)
               (cw "Warning: Code unexpectedly rewrote to the constant ~x0." dag-or-quotep)))
       ;; build the function:
       (function-name (intern-in-package-of-symbol
                       ;;todo: why is the re-interning needed here?
                       (symbol-name (FRESH-NAME-IN-WORLD-WITH-$S (strip-stars-from-name defconst-name) nil (w state)))
                       defconst-name))
       (dag-vars (if (quotep dag-or-quotep)
                     nil
                   ;;todo: check these (what should be allowed)?
                   (sort-vars-with-guidance (dag-vars-unsorted dag-or-quotep) parameter-names)))
       (function-body (if (dag-or-quotep-size-less-thanp dag-or-quotep 1000)
                          (dag-to-term dag-or-quotep)
                        `(dag-val-with-axe-evaluator ,defconst-name
                                                     ,(make-acons-nest dag-vars)
                                                     ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns *axe-evaluator-functions* (w state)) (w state))
                                                     '0 ;array depth (not very important)
                                                     )))
       (theorem-name (pack$ function-name '-correct)) ;not always used
       (event `(progn (defconst ,defconst-name ',dag-or-quotep)
                      ,@(and produce-function `((defun ,function-name ,dag-vars ,function-body)))
                      ,@(and produce-theorem
                             `((skip-proofs
                                (defthm ,theorem-name
                                  (implies (and ,@all-assumptions)
                                           (equal ,term-to-run-with-output-extractor
                                                  (,function-name ,@dag-vars)))))))))
       (items-created (append (list defconst-name)
                              (if produce-function (list function-name) nil)
                              (if produce-theorem (list theorem-name) nil)))
       ((mv end-time state) (acl2::get-real-time state))
       (- (if (= 1 (len items-created))
              (cw "Created ~x0.~%~%" (first items-created))
            (cw "Created ~x0 items: ~X12.~%~%" (len items-created) items-created nil)))
       (- (print-dag-info dag-or-quotep defconst-name nil)) ; maybe suppress with print arg?
       ;; (- (if (quotep dag-or-quotep)
       ;;        nil
       ;;      (if (dag-is-purep-aux dag-or-quotep :all t) ; prints any non-pure nodes
       ;;          (cw "~x0 is a pure dag.~%" defconst-name)
       ;;        (cw "~%WARNING: ~x0 is not a pure dag (see above)!~%" defconst-name))))
       (- (progn$ (cw "~%BYTECODE UNROLLING FINISHED (")
                  (acl2::print-to-hundredths (- end-time start-time))
                  (cw "s).") ; s = seconds
                  ))
       (- (cw ")~%~%")))
    (mv (erp-nil)
        (extend-progn (extend-progn event `(with-output :off :all (table unroll-java-code-table ',whole-form ',event)))
                      ;; `(value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
                      '(value-triple :invisible)
                      )
        state)))

;; This introduces a defconst that represents the unrolled computation
;; performed by the indicated method.
;;TODO: Could make unroll-java-code just be a call to lift-java-code with :unroll t.
;;We need to supply:
;; - the name of the method to unroll
;; - the lengths of the array inputs
;; - the output to extract (e.g., final contents of the array reference returned by the method)
;; - extra rules to use
;; TODO: Have this also return a theorem.
(defmacrodoc unroll-java-code (&whole whole-form
                                      defconst-name
                                      method-indicator
                                      &key
                                      ;; Options affecting what is proved:
                                      (assumptions 'nil) ;TODO: What variables are these over? 'locals'?  well, at least the params of the function
                                      (array-length-alist 'nil)
                                      (classes-to-assume-initialized ''("java.lang.Object" "java.lang.System")) ;TODO; Try making :all the default
                                      (ignore-exceptions 'nil)
                                      (ignore-errors 'nil)
                                      (vars-for-array-elements 't) ;whether to introduce vars for individual array elements
                                      (param-names ':auto)
                                      (output ':rv)
                                      (steps ':auto) ; todo: can this ever be less than the whole run, other than to debug a failed run?
                                      ;; Options affecting how the lifting goes:
                                      (rule-alists 'nil) ;to completely replace the usual sets of rules
                                      (extra-rules 'nil) ; to add to the usual set of rules
                                      (remove-rules 'nil)
                                      (normalize-xors 'nil) ; defaults to nil, since it's better to normalize the xors of the spec and code dags together
                                      (prune-precise 'nil) ; can blow up! was called prune-branches-precisely
                                      (prune-approx 'nil) ;todo: make t the default (but that slows down DES a lot), was called prune-branches-approximately
                                      (call-stp 'nil)
                                      ;; Options affecting performance:
                                      (memoizep 't)
                                      (branches ':smart) ;; either :smart (try to merge at join points) or :split (split the execution and don't re-merge)
                                      (chunkedp 'nil)
                                      ;; Options for debugging:
                                      (monitor 'nil) ;rules to monitor
                                      (print 'nil)
                                      (print-interval 'nil)
                                      ;; Options to produce extra events:
                                      (produce-theorem 'nil)
                                      (produce-function 'nil)
                                      (local 't))
  (let* ((form `(unroll-java-code-fn ',defconst-name
                                     ',method-indicator
                                     ',output
                                     ,array-length-alist
                                     ,extra-rules
                                     ,remove-rules
                                     ,rule-alists
                                     ,monitor
                                     ,assumptions
                                     ',normalize-xors
                                     ,classes-to-assume-initialized
                                     ,ignore-exceptions
                                     ,ignore-errors
                                     ,print
                                     ,print-interval
                                     ,memoizep
                                     ,vars-for-array-elements
                                     ',prune-precise
                                     ',prune-approx
                                     ',call-stp
                                     ',produce-theorem
                                     ',steps
                                     ',branches
                                     ',param-names
                                     ',produce-function
                                     ',chunkedp
                                     ;; end of normal args
                                     ',whole-form
                                     state))
         (form (if print
                   `(make-event ,form)
                 `(with-output ; todo: suppress the output from processing the events even if :print is t?
                    :off :all
                    :on (comment error)
                    :gag-mode nil
                    (make-event ,form))))
         (form (if (check-boolean local)
                   `(local ,form)
                 form)))
    form)
  :parents (axe-jvm axe-lifters)
  :short "A tool to lift a Java/JVM method into a DAG, unrolling loops as needed."
  :args ((defconst-name
           "The name of the constant to create.  This constant will represent the computation in DAG form.  A function may also created (its name is obtained by stripping the stars from the defconst name).")
         (method-indicator
          "The Java method to unroll (a string like \"java.lang.Object.foo(IB)V\").  The descriptor (input and output type) can be omitted if only one method in the given class has the given name.")
         (assumptions             "Terms to assume true when unrolling.  These assumptions can mention the method's parameter names (symbols), the byte-variables and/or bit-variables in the contents of array parameters, and the special variables @('locals'), @('initial-heap'), @('initial-static-field-map'), and @('initial-intern-table').")
         (array-length-alist      "An alist pairing array parameter names (symbols) with their lengths.")
         (classes-to-assume-initialized "Classes to assume the JVM has already initialized (or @(':all'))")
         (ignore-exceptions       "Whether to assume exceptions do not happen (e.g., out-of-bounds array accesses)")
         (ignore-errors           "Whether to assume JVM errors do not happen")
         (rule-alists             "If non-@('nil'), rule-alists to use (these completely replace the usual rule sets)")
         (extra-rules             "Rules to add to the usual set of rules")
         (remove-rules            "Rules to remove from the usual set of rules")
         (vars-for-array-elements "Whether to introduce vars for individual array elements in the input (@('nil'), @('t'), or :@('bits')).  For @('nil'), a single variable is introduced for the entire array.  For @('t'), a variable is introduced for each element of the array.  For @(':bits'), a variable is introduced for each bit of each element of the array.")
         (param-names "Names to use for the parameters (e.g., if no debugging information is available), or @(':auto').")
         (output                  "An indication of which state component to extract")
         (steps "A number of steps to run, or :auto, meaning run until the method returns. (Consider using :output :all when using :steps, especially if the computation may not complete after that many steps.)")
         (normalize-xors           "Whether to normalize xor nests (t or nil)")
         (prune-precise "Whether to prune unreachable branches, using precise contexts, during and after lifting (@('t'), @('nil'), or a dag size threshold).  Warning: Can take an exponential amount of time and space for DAGs with extensive sharing!")
         (prune-approx "Whether to prune unreachable branches, using approximate contexts, during and after lifting (@('t'), @('nil'), or a dag size threshold).  Can be slow but should not cause an exponential blowup.")
         (call-stp                "whether to call STP when pruning (@('t'), @('nil'), or a number of conflicts before giving up)")
         (memoizep "Whether to memoize rewrites during unrolling (a boolean).")
         (branches "How to handle branches in the execution. Either @(':smart') (try to merge at join points) or @(':split') (split the execution and don't re-merge).")
         (chunkedp "whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code)")
         (monitor                 "Rules to monitor (to help debug failures)")
         (print                   "How much to print (@('t') or @('nil') or @(':brief'), etc.)")
         (print-interval "How often to print (number of nodes)")
         (produce-theorem "Whether to produce a theorem about the result of the lifting (currently has to be trusted).")
         (produce-function "Whether to produce a defun in addition to a DAG, a boolean.")
         (local "Whether to make the result of @('unroll-java-code') local to the enclosing book (or @('encapsulate')).  This prevents a large DAG from being stored in the @(tsee certificate) of the book, but it means that the result of @('unroll-java-code') is not accessible from other books.  Usually, the default value of @('t') is appropriate, because the book that calls @('unroll-java-code') is not included by other books."))
  :description ("Given a Java method, extract an equivalent term in DAG form, by symbolic execution including inlining all functions and unrolling all loops."
                "This event creates a @(tsee defconst) whose name is given by the @('defconst-name') argument."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))

;; Ensure all the rules needed by the unroller are included:
(assert-event (ensure-all-theoremsp (unroll-java-code-rules) (w state)))
