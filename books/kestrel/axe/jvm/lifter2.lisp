; A compositional version of the JVM loop lifter
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

;; STATUS: ROUGH DRAFT

;; TODO: Abstract state components of the result (e.g., the return value) into functions.

;; Differences from the non-compositional lifter in lifter.lisp: The only input
;; variable is s0.  The tool does not put in vars for inputs (locals, contents
;; of arrays, etc.).  All assumptions should be over the single variable
;; s0. The tool always assumes that all classes are initialized.  If the class
;; initializers establish some condition that is needed (e.g., that some array
;; has certain contents), add it as an assumption.

;; TODO: Check vars in user assumptions.

(include-book "lifter")
(include-book "lifter-utilities2")

;TODO: How to remove this skip-proofs?
;todo: think about this
(skip-proofs
 (defthm run-until-exit-segment-or-hit-loop-header-lemma-for-invoke
   (implies (and (<= sh (stack-height s)) ;todo: prevent loops
                 (member-equal (jvm::op-code (jvm::current-inst (th) s)) *invoke-opcodes*)
                 (natp sh)
                 )
            (equal (run-until-exit-segment-or-hit-loop-header sh segment-pcs loop-headers (jvm::step (th) s))
                   ;; todo: consider using run-until-return here
                   ;; This needs to match the theorem proved for the called method when we (previously) lifted it:
                   (run-until-exit-segment-or-hit-loop-header sh segment-pcs loop-headers (run-until-return-from-stack-height (+ 1 (stack-height s)) (jvm::step (th) s)))))))

;; The core function of the lifter
;Returns (mv erp event state)
(defun lift-java-code2-fn (method-designator-string
                          program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                          param-names ; usually not used
                          array-length-alist
                          ;output-indicator
                          user-assumptions ;must be about the state s0
;                          classes-to-assume-initialized ;recommend using :all
                          print
                          ignore-exceptions ; unsound!
                          ignore-errors ; unsound!
                          invariants
                          guard ;guard to use for the top-level function
                          loop-guards ;a list of non-dotted pais that associate loop-ids to guards for the corresponding loop functions
                          measures ;a list of non-dotted pairs of loop-designators and expressions (special case: if a key is a natural number, it is taken to be a PC in the main method being lifted)
                          measure-hints ;a list of non-dotted pairs
                          max-term-size
                          assume-invariants-initially ;unsound?!
                          check-guards-in-functions
                          excluded-locals
                          inline
                          extra-rules
                          remove-rules
                          monitor
                          postludes
                          extra-invars
                          ;other-input-vars ;todo: just harvest these from the assumptions?
                          prune-branches
                          loops-to-unroll
                          use-prover-for-invars
                          branches
                          call-stp
                          use-lets-in-terms
                          disable-loop-openers
                          whole-form
                          state)
  (declare (xargs :stobjs (state)
                  :guard (and ;;(pseudo-term-listp user-assumptions) ;now these can be untranslated terms, so we translate them below
                          (booleanp ignore-exceptions)
                          (booleanp ignore-errors)
                          (booleanp inline)
                          (booleanp extra-invars)
                          ;; (or (string-listp classes-to-assume-initialized)
                          ;;     (eq :all classes-to-assume-initialized))
;                          (symbol-listp other-input-vars)
                          (all-loop-designatorp loops-to-unroll)
                          (or (member-eq call-stp '(t nil))
                              (natp call-stp))
                          (booleanp use-prover-for-invars)
                          (or (eq branches :smart)
                              (eq branches :split))
                          (symbol-listp param-names) ;; todo: what else to check here?
                          (booleanp disable-loop-openers)
                          )
                  :mode :program))
  (b* ( ;; Check whether an identical call to the lifter has already been done:
       ((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ;; Check inputs (TODO: What other checks should we do here?):
       ;; ((when (not (input-source-alistp input-source-alist)))
       ;;  (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed input-source-alist!") state))
       ;; ((when (not (output-indicatorp output-indicator)))
       ;;  (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed output-indicator!") state))
       ((when (not (invariantsp invariants)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed invariants!") state))
       ((when (not (excluded-localsp excluded-locals)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed excluded-locals!") state))
       ((when (not (measuresp measures state)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed measures!") state))
       ((when (not (measure-hintsp measure-hints)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed measure-hints!") state))
       ((when (not (loop-guardsp loop-guards)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed guards!") state))
       ((when (not (postludesp postludes)))
        (mv t (er hard 'lift-java-code2 "ERROR: Ill-formed postludes!") state))
       ;; Gather info about the main method to be lifted:
       (method-class (extract-method-class method-designator-string))
       (method-name (extract-method-name method-designator-string))
       (method-descriptor (extract-method-descriptor method-designator-string))
       (class-alist (global-class-alist state))
       (class-table-map (alist-to-map class-alist))
       (all-class-names (strip-cars class-alist))
;TODO: Combine with similar code in unroll-java-code
       (class-info (lookup-equal method-class class-alist))
       ((when (not class-info))
        (prog2$ (cw "ERROR: Error getting the class info for ~x0" method-class)
                (mv t nil state)))
       (method-info (lookup-equal (cons method-name method-descriptor) (jvm::class-decl-methods class-info)))
       ((when (not method-info))
        (prog2$ (cw "ERROR: Couldn't find info for method ~x0 with descriptor ~x1 in class ~x2" method-name method-descriptor method-class)
                (mv t nil state)))
       (code (lookup-eq :program method-info))
       ((when (not code))
        (prog2$ (cw "ERROR: Couldn't find code for method ~x0 with descriptor ~x1 in class ~x2" method-name method-descriptor method-class)
                (mv t nil state)))
       (local-variable-table (lookup-eq :local-variable-table method-info)) ;may be nil
       ((when (not (jvm::local-variable-tablep local-variable-table)))
        (prog2$ (er hard 'lift-java-code2-fn "Ill-formed local variable table: ~x0." local-variable-table)
                (mv t nil state)))
       (staticp (jvm::method-staticp method-info))
       (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method

       (param-slot-to-name-alist (make-param-slot-to-name-alist method-info param-names))
       (param-name-to-slot-alist (reflect-alist param-slot-to-name-alist))
       ;; ((when (and (not input-source-alist)
       ;;             (not local-variable-tablep)))
       ;;  (prog2$ (hard-error 'lift-java-code2-fn "We don't know the names of the inputs because no input-source-alist was supplied and no local-variable-table is present (consider recompiling the code with the -g flag to create the local variable table)." nil)
       ;;          (mv t nil state)))
       (parameter-types (lookup-eq :parameter-types method-info))
       ;; (input-source-alist (or input-source-alist
       ;;                         ;(make-input-source-alist parameter-types local-variable-table static-flag)
       ;;                         ))
;       (locals-term `(jvm::locals (jvm::thread-top-frame (th) s0)))
       (heap-term `(jvm::heap s0))
       ;; The thread:
       (th '(th)) ;(th ''0)
       (state-var 's0)
       (parameter-assumptions (assumptions-about-parameters-on-stack parameter-types first-param-slot param-slot-to-name-alist array-length-alist th state-var))
       (poised-assumptions (make-poised-assumptions staticp method-class method-name method-descriptor parameter-types state-var))
       (- (cw "(Parameter assumptions: ~x0)~%" parameter-assumptions))

       ;; ((mv param-assumptions param-input-vars)
       ;;  (param-assumptions-and-vars method-info array-length-alist locals-term heap-term param-slot-to-name-alist))
       ;; Translate and desugar user-supplied assumptions:
       (user-assumptions (translate-terms user-assumptions 'lift-java-code2-fn (w state))) ;throws an error on bad input
;       (local-vars-at-pc-0 (merge-sort-local-vars-for-pc (local-vars-for-pc 0 local-variable-table))) ;may be nil if there is no local-variable-table
;       (- (cw " (Locals at PC 0: ~x0)~%" local-vars-at-pc-0)) ;todo: might there be locals that are not params?
       (param-slot-to-stack-item-alist (param-slot-to-stack-item-alist parameter-types first-param-slot th state-var))
       (user-assumptions (desugar-params-in-assumption-terms-to-stack-items user-assumptions param-name-to-slot-alist param-slot-to-stack-item-alist))
       (user-assumptions (desugar-calls-of-contents-in-terms user-assumptions heap-term))
       ;; Check that the :assumptions don't call var (a common mistake).  ;TODO: or should we allow this?
       ((when (intersection-eq (all-ffn-symbs-lst user-assumptions nil)
                               '(var)))
        (mv t
            (er hard 'lift-java-code2 "Assumptions should not call VAR (just mention the var as a symbol)")
            state))
       (assumptions-about-this (if staticp
                                   nil ;no assumptions about "this" for a static method
                                 `((addressp ,(lookup-eq 0 param-slot-to-stack-item-alist))
                                   (not (null-refp ,(lookup-eq 0 param-slot-to-stack-item-alist))) ;might be implied by addressp?
                                   ;;todo: add assumption about the class of "this" (what can we say)?
                                   )))
       (measures-option       (elaborate-measures-option               measures        method-class method-name method-descriptor)) ;special treatment to support a single keyword
       (measure-hints-alist   (elaborate-loop-function-ids-in-doublets measure-hints   method-class method-name method-descriptor :measure-hints))
       (invariant-alist       (elaborate-loop-function-ids-in-doublets invariants      method-class method-name method-descriptor :invariants))
       (excluded-locals-alist (elaborate-loop-function-ids-in-doublets excluded-locals method-class method-name method-descriptor :excluded-locals))
       (loop-guard-alist      (elaborate-loop-function-ids-in-doublets loop-guards     method-class method-name method-descriptor :loop-guards))
       (postlude-alist        (elaborate-loop-function-ids-in-doublets postludes       method-class method-name method-descriptor :postludes))

       (all-lifted-methods (get-all-lifted-methods-from-table (w state)))
       (all-lifted-method-designator-strings (lookup-eq-in-all :method-designator-string all-lifted-methods))
       (all-lifted-method-functions (lookup-eq-in-all :function-name all-lifted-methods))
       (all-lifted-method-theorems (lookup-eq-in-all :theorem-name all-lifted-methods))
       ;; Build a rule to inline methods not already lifted:
       (inlining-theorem (make-step-opener-for-non-already-lifted-methods all-lifted-method-designator-strings))
       ;; This gets rolled back after the make-event:
       (state (submit-event inlining-theorem state))
       (remove-rules (append '(jvm::step-opener ;since we trigger the theorems for subroutines off of step
                               )
                             remove-rules))
       (extra-rules (append '(run-until-exit-segment-or-hit-loop-header-lemma-for-invoke)
                            (compositional-lifter-rules)
                            all-lifted-method-functions
                            all-lifted-method-theorems
                            extra-rules))
       (symbolic-execution-rules (if (eq branches :split)
                                     (run-until-exit-segment-or-hit-loop-header-rules-split)
                                   (run-until-exit-segment-or-hit-loop-header-rules-smart)))
       ;;a map (TODO: why not an alist?) including options other than the ones passed here explicitly:
       (options (s :measures-option measures-option
                   (s :measure-hints-alist measure-hints-alist
                      (s :invariant-alist invariant-alist
                         (s :excluded-locals-alist excluded-locals-alist
                            (s :loop-guard-alist loop-guard-alist
                               (s :postlude-alist postlude-alist
                                  (s :max-term-size max-term-size
                                     (s :ignore-exceptions ignore-exceptions
                                        (s :ignore-errors ignore-errors
                                           (s :call-stp call-stp
                                              (s :loops-to-unroll loops-to-unroll
                                                 (s :prune-branches prune-branches
                                                    (s :extra-rules extra-rules
                                                       (s :remove-rules remove-rules
                                                          (s :check-guards-in-functions check-guards-in-functions
                                                             (s :assume-invariants-initially assume-invariants-initially
                                                                (s :inline inline
                                                                   (s :monitor monitor
                                                                      (s :use-prover-for-invars use-prover-for-invars
                                                                         (s :symbolic-execution-rules symbolic-execution-rules
                                                                            (s :use-lets-in-terms use-lets-in-terms
                                                                               (s :disable-loop-openers disable-loop-openers
                                                                                  nil)))))))))))))))))))))))
;       (input-vars (append param-input-vars other-input-vars)) ;input variables (assumptions can be about these, and they become params of the generated function) , a symbol-listp
       ;;((mv erp event state)
;todo: clean up here:
       (extra-invarsp extra-invars) ;add to options?
       (loop-alist (get-loops-from-classes class-alist))
       ;; ;; Do the decompilation:
       ;; ((mv final-state-dag generated-events generated-rules
       ;;      & ;interpreted-function-alist-alist  ;fixme think about this.
       ;;      interpreted-function-alist state)
       ;;  (decompile-program
       ;;   (append (code-hyps 0 method-info method-class method-name method-descriptor 's0)
       ;;           assumptions)
       ;;   (jvm::get-pcs-from-program code)
       ;;   program-name
       ;;   nil ;input-vars
       ;;   nil ;don't unroll nested loops
       ;;   extra-invarsp
       ;;   print ;t   ;:brief
       ;;   classes-to-assume-initialized
       ;;   options
       ;;   state))
       (initialized-class-names all-class-names)

       ;; For every class currently loaded, we make an assumption about looking up that class in the class table:
       (class-table-assumptions (class-table-hyps2 state-var class-alist))
       (class-table-assumptions-translated (translate-terms class-table-assumptions 'lift-java-code2-fn (w state)))
       (assumptions (append (assumptions-that-classes-are-initialized initialized-class-names 's0) ;;  `((equal (jvm::initialized-classes s0) ',initialized-class-names)) ;we also pass around the list of initialized classes in the main mut rec...i guess we now also pass in the heap and thread table above..
                            (standard-hyps-basic-before-invoke 's0) ;todo: think about this. don't need the sync flag one?
                            class-table-assumptions-translated
                            ;(list `(jvm::jvm-statep ,state-var))
                            poised-assumptions
                            parameter-assumptions user-assumptions assumptions-about-this))
       (nicer-assumptions (union-equal class-table-assumptions
                                       (set-difference-equal assumptions
                                                             class-table-assumptions-translated)))
       (assumption-vars (all-vars1-lst assumptions nil))
       ((when (not (subsetp-eq assumption-vars (list state-var))))
        (mv t (er hard 'lift-java-code2 "ERROR: Bad vars in assumptions: ~x0!" (set-difference-eq assumption-vars (list state-var))) state))
       (- (cw "Will lift with these assumptions: ~x0." nicer-assumptions))
       ((mv erp state-var-dag) (dagify-term2 state-var))
       ((when erp) (mv erp nil state))
       ((mv erp
            final-state-dag generated-events generated-rules
            &  ;next-loop-number
            & ;interpreted-function-alist-alist
            interpreted-function-alist
            state)
        (decompile-code-segment-aux
         state-var-dag
         (remove-duplicates-equal ;drop?
          assumptions)
         '(binary-+ '1
                   (JVM::CALL-STACK-SIZE
                    (JVM::BINDING (th) (JVM::THREAD-TABLE S0))))
         (jvm::get-pcs-from-program code) ;segment-pcs
         program-name ;tag
         0              ;loop depth
         t ;nil            ;step-once-to-startp
         loop-alist     ;all loops in the program
         1              ;next-loop-number
         nil    ;generated-rules-acc
         initialized-class-names
         nil ;other-input-vars
;fffixme what other fns might appear in the dag for a loop update function?
;initial interpreted-function-alist-alist:
         nil ;;(acons 'dag-val-with-axe-evaluator (make-interpreted-function-alist '(dag-val-with-axe-evaluator eval-dag-with-axe-evaluator) (w state)) nil)
         nil ;initial interpreted-function-alist
         class-table-map
         nil ;unroll-nested-loopsp
         extra-invarsp
         print options
         nil ;;generated-events-acc
         state))
       ((when erp)
        (mv erp nil state))
       (- (and print (progn$ (cw "(Result Dag:~%")
                             (print-list final-state-dag)
                             (cw ")~%"))))
       ;; ;; Extract the term representing the output:
       ;; (return-type (lookup-eq :return-type method-info))
       ;; ((mv output-dag state)
       ;;  (extract-output-dag output-indicator final-state-dag
       ;;                      (append assumptions)
       ;;                      '(jvm::locals (JVM::thread-top-frame (th) s0))
       ;;                      return-type
       ;;                      class-alist
       ;;                      state))
       ;; ;; TODO: This seemed necessary, but why?!:  maybe because for :array-return-value, we have multiple occs of the IF nest in the output term and then the getfield-of-myif rules fire
       ;; ;; handle better since the two if nests are in sync...
       ;; ((mv output-dag state)
       ;;  (maybe-prune-dag (g :prune-branches options)
       ;;                   output-dag
       ;;                   assumptions ;todo think about this
       ;;                   (set-difference-eq
       ;;                     ;todo: improve?:
       ;;                    (append (amazing-rules-spec-and-dag)
       ;;                            (jvm-rules-jvm)
       ;;                            (g :extra-rules options))
       ;;                    (g :remove-rules options))
       ;;                   (g :monitor options)
       ;;                   (g :call-stp options)
       ;;                   state))
       ;; (- (and print (progn$ (cw "(Output DAG:~%")
       ;;                       (print-list output-dag)
       ;;                       (cw ")~%"))))
       ;todo: should just be s0:
       (dag-vars (dag-vars final-state-dag))
       ((when (not (equal dag-vars '(s0))))
        (mv t (er hard 'lift-java-code2 "ERROR: Bad vars: ~x0!" dag-vars) state))
       ;; ;; TODO: Shouldn't we just add inputs automatically for this new stuff?
       ;; (- (and (not (subsetp-eq dag-vars input-vars))
       ;;         (cw "WARNING: Unexpected variables, ~x0, appear in the DAG.  At this point only input vars should remain.  If state vars such as S0 remain, consider identifying additional state components that should be considered inputs (using input-vars plus assumptions that equate the state components with the new input vars).~%"  (set-difference-eq dag-vars input-vars))))
;       (dag-vars (sort-vars-with-guidance dag-vars input-vars))
       ;; Maybe sure s0, etc do not appear (does this happen when locals need to be excluded?):
       ;;(- (check-dag-vars input-vars output-dag)) ;;check that the vars of this DAG only include the vars in INPUT-VARS ! TODO: better error message here
       (top-fn-body (dag-to-term-limited final-state-dag ;output-dag
                                         max-term-size use-lets-in-terms interpreted-function-alist))
       (theorem-name (pack$ program-name '-correct))
       (new-all-lifted-methods (cons (acons :method-designator-string method-designator-string
                                            (acons :function-name program-name
                                                   (acons :theorem-name theorem-name
                                                          nil)))
                                     all-lifted-methods))
       (event
        `(progn
           (cw-event "(Processing generated events...~%")
           ,@generated-events
           (cw-event "Done Processing generated events.)~%")
           (defun ,(pack$ program-name '-generated-rules) ()
             (declare (xargs :normalize nil))
             ',generated-rules)
           (defun ,program-name ,dag-vars
             (declare (xargs :normalize nil
                             ,@(if guard `(:guard ,guard) nil)
                             :verify-guards nil))
             ,top-fn-body)
           (skip-proofs
            ;; Introduce the SH var for better matching in the LHS:
            (defthm ,theorem-name
               (implies (and (equal sh (binary-+ '1 (stack-height ,state-var))) ;TODO: Think about this
                             ,@nicer-assumptions)
                        ;; this calls step (not the variant) and uses run-until-return-from-stack-height instead of run-until-return (why not run-until-return? must match run-until-return-from-stack-height-lemma-for-invoke)
                        (equal (run-until-return-from-stack-height sh (jvm::step (th) ,state-var))
                               (,program-name ,state-var)))))
           ;; Add this method to the list that will be stored in the table:
           (table compositional-lifter-table
                  :all-lifted-methods
                  ',new-all-lifted-methods)
           (cw-event "~x0~%" '(,program-name ,theorem-name))
           (value-triple :invisible))))
    (mv nil ; no error
        (extend-progn event `(table lift-java-code2-table ',whole-form ',event)) ;todo: move this
        state
       )))

;; The main way to call the lifter.
;; The actual code should have been already stored in the GLOBAL-CLASS-TABLE (in the books generated by build-book-for-class).
;; NOTE: Keep this in sync with SHOW-LIFT-JAVA-CODE2 below.
;; TODO: Consider re-playing with :print t if the lift attempt fails.
;; TODO: Suppress more printing if :print is nil.
(defmacro lift-java-code2 (&whole whole-form
                                 method-designator-string
                                 program-name ; the name of the program to generate, a symbol which will be added onto the front of generated function names.
                                 &key
                                 (param-names 'nil)
;                                 (output ':auto) ;an output-indicatorp
                                 (array-length-alist 'nil)
                                 (assumptions 'nil)
;                                 (classes-to-assume-initialized 'nil)
                                 (print 'nil)
                                 (ignore-exceptions 'nil)
                                 (ignore-errors 'nil)
                                 (invariants 'nil)
                                 (guard 'nil)
                                 (loop-guards 'nil)
                                 (max-term-size '*max-term-size*)
                                 (measures 'nil) ;; (measures ':auto)  ;FFIXME put this back once it works (either need to flatten params in the lifter or have with-auto-termination handle params that are tuples better)
                                 (measure-hints 'nil)
                                 (assume-invariants-initially 'nil) ;;Assume invariants hold at the top of each loop; dangerous!
                                 (check-guards-in-functions 'nil)
                                 (excluded-locals 'nil)
                                 (inline 't) ;whether to inline the loop termination test and exit test
                                 (extra-rules 'nil)
                                 (remove-rules 'nil)
                                 (monitor 'nil)
                                 (postludes 'nil)
                                 (extra-invars 'nil)
;                                 (other-input-vars 'nil) ;TODO: Document!
                                 (show-only 'nil) ;todo: how does this interact with the need to submit functions before proving their postludes?
                                 (prune-branches 'nil) ;TODO: Document!  TODO: Change the defaut to something like 10000?
                                 (loops-to-unroll 'nil) ;todo: document
                                 (call-stp 'nil)
                                 (use-lets-in-terms 'nil)
                                 (use-prover-for-invars 'nil) ;todo: consider T
                                 (branches ':split) ;; either :smart (try to merge at join points) or :split (split the execution and don't re-merge) -- TODO: Switch the default to :smart
                                 (disable-loop-openers 'nil) ;todo: consider T
                                 )
  (let ((form `(lift-java-code2-fn ,method-designator-string
                                  ,program-name
                                  ',param-names
                                  ,array-length-alist
;                                  ,output
                                  ,assumptions
;                                  ,classes-to-assume-initialized
                                  ,print
                                  ,ignore-exceptions
                                  ,ignore-errors
                                  ,invariants
                                  ,guard
                                  ,loop-guards
                                  ,measures
                                  ,measure-hints
                                  ,max-term-size
                                  ,assume-invariants-initially
                                  ,check-guards-in-functions
                                  ,excluded-locals
                                  ',inline
                                  ,extra-rules
                                  ,remove-rules
                                  ,monitor
                                  ,postludes
                                  ',extra-invars
;                                  ',other-input-vars
                                  ',prune-branches
                                  ',loops-to-unroll
                                  ,use-prover-for-invars
                                  ,branches
                                  ',call-stp
                                  ',use-lets-in-terms
                                  ',disable-loop-openers
                                  ',whole-form
                                  state)))
    (if show-only
        `(mv-let (erp res state)
           ,form
           (declare (ignore erp)) ;todo
           (progn$ (cw "~x0" res)
                   state))
      (if print
          `(make-event ,form)
        `(with-output
           :off :all
           :on error
           :gag-mode nil
           (make-event ,form))))))

;; Show but do not submit the lifted code.
;; NOTE: Keep this in sync with LIFT-JAVA-CODE2 above.
(defmacro show-lift-java-code2 (&rest args)
  `(lift-java-code2 ,@args :show-only t))
