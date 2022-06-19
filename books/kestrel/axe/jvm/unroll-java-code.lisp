; A tool to unroll Java code
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
(include-book "../make-term-into-dag-basic")
(include-book "../rewriter") ; for simp-dag (todo: use something better?)
(include-book "../prune") ;brings in rewriter-basic
(include-book "../dag-info")

(local (in-theory (enable symbolp-of-lookup-equal-when-param-slot-to-name-alistp)))

(local (in-theory (disable acl2-count ;for speed
                           )))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; Returns a boolean
(defun dag-ok-after-symbolic-execution (dag assumptions error-on-incomplete-runsp wrld)
  (declare (xargs :mode :program)) ; because this calls untranslate
  (let ((dag-fns (dag-fns dag)))
    (if (or (member-eq 'run-until-return-from-stack-height dag-fns) ;todo: pass in a set of functions to look for?
            (member-eq 'jvm::run-n-steps dag-fns)
            (member-eq 'jvm::do-inst dag-fns)
            (member-eq 'jvm::error-state dag-fns))
        (progn$ (if (dag-or-quotep-size-less-thanp dag 10000)
                    (progn$ (cw "(Result Term:~%")
                            (cw "~X01" (untranslate (dag-to-term dag) nil wrld) nil)
                            (cw ")~%"))
                  (cw "(Result DAG: ~x0)~%" dag))
                (cw "(Assumptions were: ~x0)~%" assumptions)
                (and error-on-incomplete-runsp
                     (hard-error 'unroll-java-code-fn "ERROR: Symbolic simulation did not seem to finish (see DAG and assumptions above)." nil)))
      t)))

;; Repeatedly rewrite DAG to perform symbolic execution.  Perform
;; STEP-INCREMENT steps at a time, until the run finishes, STEPS-LEFT is
;; reduced to 0, or a loop or unsupported instruction is detected.  Returns (mv
;; erp result-dag state).
;; TODO: Consider adding an option to prune between chunks.
(defun repeatedly-run (dag
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
                       total-steps
                       state)
  (declare (xargs :guard (and (natp steps-left)
                              (step-incrementp step-increment)
                              (true-listp rule-alists)
                              (all-rule-alistp rule-alists)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules-to-monitor)
;                              (booleanp use-internal-contextsp)
                              ;; print
                              (booleanp memoizep)
                              (natp total-steps)
                              (booleanp normalize-xors))
                  :mode :program ;; because we call simp-dag-fn and untranslate
                  :stobjs (state)
                  ))
  (if (zp steps-left)
      (mv (erp-nil) dag state)
    (b* ((this-step-increment (this-step-increment step-increment total-steps))
         (steps-for-this-iteration (min steps-left this-step-increment))
         (old-dag dag)
         ((mv erp dag state)
          (simp-dag dag
                    :assumptions assumptions
                    :rule-alists rule-alists
                    :use-internal-contextsp t ;new!
                    :print print              ;(if monitored-rules t nil)
                    :print-interval print-interval
                    :monitor rules-to-monitor
                    :normalize-xors normalize-xors
                    :memoizep memoizep
                    ;;:exhaustivep (if chunkedp t nil)
                    :limits `((step-state-with-pc-and-call-stack-height-becomes-step-axe . ,steps-for-this-iteration))
                    :check-inputs nil))
         ((when erp) (mv erp nil state))
         (dag-fns (dag-fns dag)))
      (if (not (or (member-eq 'run-until-return-from-stack-height dag-fns)
                   (member-eq 'jvm::run-n-steps dag-fns)
                   (member-eq 'jvm::do-inst dag-fns))) ;; stop if the run is done
          (prog2$ (cw "Note: The run has completed.~%")
                  (mv (erp-nil) dag state))
        (if nil ;todo: (member-eq 'x86isa::x86-step-unimplemented dag-fns) ;; stop if we hit an unimplemented instruction
            (prog2$ (cw "WARNING: UNIMPLEMENTED INSTRUCTION.~%")
                    (mv (erp-nil) dag state))
          (if (equivalent-dags dag old-dag)
              (progn$ (cw "Note: Stopping the run because nothing changed.~%")
                      (and print
                           (prog2$ (cw "(DAG:~%")
                                   (cw "~X01)" dag nil)))
                      (mv (erp-nil) dag state))
            (b* ((total-steps (+ steps-for-this-iteration total-steps))
                 (- (and print
                         (if (eq :brief print)
                             (cw "(~x0 steps done.):~%" total-steps)
                           ;; Print as a term unless it would be huge:
                           (if (dag-or-quotep-size-less-thanp dag 1000)
                               (progn$ (cw "(Term after ~x0 steps:~%" total-steps)
                                       (cw "~X01" (untranslate (dag-to-term dag) nil (w state)) nil)
                                       (cw ")~%"))
                             (progn$ (cw "(DAG after ~x0 steps:~%" total-steps)
                                     (cw "~X01)" dag nil)))))))
              (repeatedly-run dag
                              (- steps-left steps-for-this-iteration)
                              step-increment rule-alists assumptions normalize-xors rules-to-monitor ; use-internal-contextsp
                              print
                              print-interval
                              memoizep
                              total-steps
                              state))))))))

;; Chunked execution can be necessary to make use of overarching if-conditions.
;; For example, we may have a test that ensures that a later loop terminates.

;; Returns (mv erp dag all-assumptions term-to-run-with-output-extractor dag-fns parameter-names state).
;; This uses all classes currently in the global-class-table.
;; Why does this return the dag-fns?
(defun unroll-java-code-fn-aux (method-designator-string
                                maybe-nice-output-indicator
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
                                prune-branches
                                call-stp ;t, nil, or a max-conflicts
                                steps
                                branches
                                param-names ; may be :auto
                                chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                                error-on-incomplete-runsp ;whether to throw a hard error (may be nil if further pruning can be done in the caller)
                                state)
  (declare (xargs :guard (and (or (eq :auto maybe-nice-output-indicator)
                                  (nice-output-indicatorp maybe-nice-output-indicator))
                              (or (eq :all classes-to-assume-initialized)
                                  (jvm::all-class-namesp classes-to-assume-initialized))
                              (symbol-listp extra-rules)
                              (symbol-listp remove-rules)
                              (all-rule-alistp rule-alists)
                              (symbol-listp monitored-rules)
                              (array-length-alistp array-length-alist)
                              (member-eq vars-for-array-elements '(t nil :bits))
                              (booleanp prune-branches)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))
                              (or (eq :auto steps)
                                  (natp steps))
                              (or (eq :smart branches)
                                  (eq :split branches))
                              (or (eq :auto param-names)
                                  (symbol-listp param-names)) ;todo: check for dups and keywords and case clashes
                              (booleanp chunkedp)
                              (booleanp error-on-incomplete-runsp)
                              (booleanp normalize-xors))
                  :stobjs (state)
                  :mode :program ;because of FRESH-NAME-IN-WORLD-WITH-$S, SIMP-TERM-FN and TRANSLATE-TERMS
                  ))
  (b* ((method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string)) ;todo: should this be called a descriptor?
       ;; TODO: If only one method with that name, just put in its descriptor
       ((when (equal method-descriptor ""))
        (mv t
            (er hard? 'unroll-java-code-fn "Method descriptor is missing in ~x0." method-designator-string)
            nil nil nil nil
            state))
       (class-alist (jvm::global-class-alist state))
       (all-class-names (strip-cars class-alist))
       ((when (not (assoc-equal method-class class-alist)))
        (mv t
            (hard-error 'unroll-java-code-fn "Class ~x0 not found." (acons #\0 method-class nil))
            nil nil nil nil
            state))
       (class-info (lookup-equal method-class class-alist))
       (method-info-alist (jvm::class-decl-methods class-info))
       (method-id (cons method-name method-descriptor))
       ((when (not (assoc-equal method-id method-info-alist)))
        (mv t
            (hard-error 'unroll-java-code-fn "Method ~x0 not found." (acons #\0 method-id nil))
            nil nil nil nil
            state))
       (method-info (lookup-equal method-id method-info-alist))
       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info param-names))
       (parameter-names (strip-cdrs param-slot-to-name-alist)) ; the actual names used
       (class-table-term (make-class-table-term-compact class-alist 'initial-class-table))
       (locals-term 'locals)
       (initial-heap-term 'initial-heap)
       (initial-intern-table-term 'initial-intern-table)
       (user-assumptions (translate-terms user-assumptions 'unroll-java-code-fn (w state))) ;throws an error on bad input
       ;; TODO: Not quite right.  Need to allow the byte- or bit-blasted array var names (todo: what about clashes between those and the other param names?):
       ;; (assumption-vars (free-vars-in-terms user-assumptions))
       ;; (allowed-assumption-vars (append parameter-names
       ;;                                  '(locals initial-heap initial-static-field-map and initial-intern-table)))
       ;; ((when (not (subsetp-eq assumption-vars allowed-assumption-vars)))
       ;;  (er hard? 'unroll-java-code-fn-aux "Disallowed variables in assumptions, ~x0.  The only allowed vars are ~x1." user-assumptions allowed-assumption-vars)
       ;;  (mv :bad-assumption-vars nil nil nil nil nil state))
       (user-assumptions (desugar-calls-of-contents-in-terms user-assumptions initial-heap-term))
       ;; todo: have this return all the var names creates for array components/bits:
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
       (classes-to-assume-initialized (if (eq :all classes-to-assume-initialized)
                                          all-class-names
                                        classes-to-assume-initialized))
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
       (parameter-types (lookup-eq :parameter-types method-info))
       ;; Handle an output-indicator of :auto:
       (output-indicator (if (eq :auto maybe-nice-output-indicator)
                             (resolve-auto-output-indicator return-type)
                           (desugar-nice-output-indicatorp maybe-nice-output-indicator param-slot-to-name-alist parameter-types return-type)))
       (term-to-run-with-output-extractor (wrap-term-with-output-extractor output-indicator ;return-type
                                                                           locals-term term-to-run class-alist))
       (symbolic-execution-rules (if (eq :auto steps)
                                     (if (eq branches :smart)
                                         (run-until-return-from-stack-height-rules-smart)
                                       (if (eq branches :split)
                                           (run-until-return-from-stack-height-rules-split)
                                         (er hard 'unroll-java-code-fn "Illegal value for :branches: ~x0.  Must be :smart or :split." branches)))
                                   (symbolic-execution-rules-for-run-n-steps) ;todo: add a :smart analogue of this rule set
                                   ))
       ((mv erp default-rule-alist)
        (make-rule-alist (append (unroll-java-code-rules)
                                 symbolic-execution-rules)
                         (w state)))
       ((when erp) (mv erp nil nil nil nil nil state))
       (rule-alists (or rule-alists ;use user-supplied rule-alists, if any
                        ;; by default, we use 1 rule-alist:
                        (list default-rule-alist)))
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

       ;; Convert the term into a dag for passing to repeatedly-run:
       ((mv erp dag-to-simulate) (make-term-into-dag-basic term-to-run-with-output-extractor nil))
       ((when erp) (mv erp nil nil nil nil nil state))
       (step-limit 1000000)
       (step-increment (if chunkedp 100 1000000))
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
                        0
                        state))
       ;;todo: check for a quotep returned
       ((when erp)
        (er hard? 'unroll-java-code-fn "Error in unrolling.")
        (mv erp nil nil nil nil nil state))
       ((mv erp dag state)
        (if prune-branches
            (prune-dag-with-rule-alist-new dag
                                           all-assumptions ;are they all needed?
                                           (first rule-alists) ;what should we use here?
                                           nil ; interpreted-function-alist
                                           monitored-rules
                                           call-stp
                                           state)
          (mv nil dag state)))
       ((when erp) (mv erp nil nil nil nil nil state))
       ;; Check whether symbolic execution failed:
       (dag-okp (dag-ok-after-symbolic-execution dag all-assumptions error-on-incomplete-runsp (w state))))
    (mv (if (and (not dag-okp)
                 error-on-incomplete-runsp)
            (erp-t)
          (erp-nil))
        dag all-assumptions term-to-run-with-output-extractor (dag-fns dag) parameter-names state)))

;; Returns (mv erp event state).
(defun unroll-java-code-fn (defconst-name
                             method-indicator
                             maybe-nice-output-indicator
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
                             prune-branches
                             call-stp ;t, nil, or a max-conflicts
                             produce-theorem
                             steps
                             branches
                             param-names
                             produce-function
                             chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                             whole-form
                             state)
  (declare (xargs :guard (and (or (eq :auto maybe-nice-output-indicator)
                                  (nice-output-indicatorp maybe-nice-output-indicator))
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
                              (booleanp prune-branches)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))
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
                  :stobjs (state)
                  :mode :program ;because of FRESH-NAME-IN-WORLD-WITH-$S, SIMP-TERM-FN and TRANSLATE-TERMS
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
       ;; Adds the descriptor if omitted and unambiguous:
       (method-designator-string (jvm::elaborate-method-indicator method-indicator (jvm::global-class-alist state)))
       ;; Printed even if print is nil (seems ok):
       (- (cw "(Unrolling ~x0.~%"  method-designator-string))
       ((mv erp dag all-assumptions term-to-run-with-output-extractor dag-fns parameter-names state)
        (unroll-java-code-fn-aux method-designator-string maybe-nice-output-indicator array-length-alist
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
                                 prune-branches
                                 call-stp ;t, nil, or a max-conflicts
                                 steps
                                 branches
                                 param-names
                                 chunkedp ;whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code?)
                                 t ;error on incomplete runs
                                 state))
       ((when erp) (mv erp nil state))
       ;; build the function:
       (function-name (intern-in-package-of-symbol
                       ;;todo: why is the re-interning needed here?
                       (symbol-name (FRESH-NAME-IN-WORLD-WITH-$S (strip-stars-from-name defconst-name) nil (w state)))
                       defconst-name))
       (dag-vars (dag-vars dag)) ;todo: check these (what should be allowed)?
       (dag-vars (sort-vars-with-guidance dag-vars parameter-names))
       (function-body (if (dag-or-quotep-size-less-thanp dag 1000)
                          (dag-to-term dag)
                        `(dag-val-with-axe-evaluator ,defconst-name
                                                     ,(make-acons-nest dag-vars)
                                                     ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns (w state)) (w state))
                                                     '0 ;array depth (not very important)
                                                     )))
       (theorem-name (pack$ function-name '-correct)) ;not always used
       (event `(progn (defconst ,defconst-name ',dag)
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
       (- (cw "Unrolling finished.~%"))
       ;; (- (cw "Info on unrolled DAG:~%"))
       (- (print-dag-info dag defconst-name nil)) ; maybe suppress with print arg?
       (- (cw ")~%")))
    (mv (erp-nil)
        (extend-progn (extend-progn event `(with-output :off :all (table unroll-java-code-table ',whole-form ',event)))
                      `(value-triple ',items-created) ;todo: use cw-event and then return :invisible here?
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
                                      (output ':auto)
                                      (steps ':auto) ; todo: can this ever be less than the whole run, other than to debug a failed run?
                                      ;; Options affecting how the lifting goes:
                                      (rule-alists 'nil) ;to completely replace the usual sets of rules
                                      (extra-rules 'nil) ; to add to the usual set of rules
                                      (remove-rules 'nil)
                                      (normalize-xors 'nil) ; defaults to nil, since it's better to normalize the xors of the spec and code dags together
                                      (prune-branches 'nil) ;todo: make t the default
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
                                     ',prune-branches
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
  :parents (lifters)
  :short "Lift a Java method to create a DAG, unrolling loops as needed."
  :args ((defconst-name
           "The name of the constant to create.  This constant will represent the computation in DAG form.  A function may also created (its name is obtained by stripping the stars from the defconst name).")
         (method-indicator
          "The Java method to unroll (a string like \"java.lang.Object.foo(IB)V\").  The descriptor (input and output type) can be omitted if only one method in the given class has the given name.")
         (assumptions             "Terms to assume true when unrolling.  These assumptions can mention the method's parameter names (symbols), the byte-variables and/or bit-variables in the contents of array parameters, and the special variables @('locals'), @('initial-heap'), @('initial-static-field-map'), and @('initial-intern-table').")
         (array-length-alist      "An alist pairing array parameter names (symbols) with their lengths.")
         (classes-to-assume-initialized "Classes to assume the JVM has already initialized (or :all)")
         (ignore-exceptions       "Whether to assume exceptions do not happen (e.g., out-of-bounds array accesses)")
         (ignore-errors           "Whether to assume JVM errors do not happen")
         (rule-alists             "If non-nil, rule-alists to use (these completely replace the usual rule sets)")
         (extra-rules             "Rules to add to the usual set of rules")
         (remove-rules            "Rules to remove from the usual set of rules")
         (vars-for-array-elements "whether to introduce vars for individual array elements (nil, t, or :bits)")
         (param-names "Names to use for the parameters (e.g., if no debugging information is available), or :auto.")
         (output                  "An indication of which state component to extract")
         (steps "A number of steps to run, or :auto, meaning run until the method returns. (Consider using :output :all when using :steps, especially if the computation may not complete after that many steps.)")
         (normalize-xors           "Whether to normalize xor nests (t or nil)")
         (prune-branches          "whether to aggressively prune unreachable branches in the result")
         (call-stp                "whether to call STP when pruning (t, nil, or a number of conflicts before giving up)")
         (memoizep "Whether to memoize rewrites during unrolling (a boolean).")
         (branches "How to handle branches in the execution. Either :smart (try to merge at join points) or :split (split the execution and don't re-merge).")
         (chunkedp "whether to divide the execution into chunks of steps (can help use early tests as assumptions when lifting later code)")
         (monitor                 "Rules to monitor (to help debug failures)")
         (print                   "How much to print (t or nil or :brief, etc.)")
         (print-interval "How often to print (number of nodes)")
         (produce-theorem "Whether to produce a theorem about the result of the lifting (currently has to be trusted).")
         (produce-function "Whether to produce a defun in addition to a DAG, a boolean.")
         (local "Whether to make the result of @('unroll-java-code') local to the enclosing book (or @('encapsulate')).  This prevents a large DAG from being stored in the @(tsee certificate) of the book, but it means that the result of @('unroll-java-code') is not accessible from other books.  Usually, the default value of @('t') is appropriate, because the book that calls @('unroll-java-code') is not included by other books."))
  :description ("Given a Java method, extract an equivalent term in DAG form, by symbolic execution including unrolling all loops."
                "This event creates a @(see defconst) whose name is @('defconst-name')."
                "To inspect the resulting DAG, you can simply enter its name at the prompt to print it."))

;; Ensure all the rules needed by the unroller are included:
(assert-event (ensure-all-theoremsp (unroll-java-code-rules) (w state)))
