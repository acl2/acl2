(declaim (optimize (safety 3) (speed 0) (space 0) (debug 3)))

(load "package.lsp")
(load "acl2s-high-level-interface.lsp")
(load "structs.lsp")
(load "util.lsp")
(load "print.lsp")
(load "conditions.lsp")
(load "prop-equiv.lsp")

(in-package :prover)

(import 'acl2s-high-level-interface::(acl2s-query acl2s-event acl2s-compute))
;;(import '(cl-ansi-text:green cl-ansi-text:yellow cl-ansi-text:red))
;;(import 'trivia::match)
;;(import 'trivia::<>)
(import 'tp::(prop-equiv prop-equiv-pairwise prop-equiv-bijection bijection-error))

(defvar *MESSAGES* nil)
(defvar *CURRENT-PROOF* nil)

(declaim (ftype (function (optional-TaggedSExpr) boolean) missingp))
(defun missingp (x)
  (or (not x) (equal x :missing)))

(defun recursive-ts-expr (val)
  (cond ((typep val 'TaggedSExpr) (recursive-ts-expr (TaggedSExpr-expr val)))
        ((consp val) (cons (recursive-ts-expr (car val))
                           (recursive-ts-expr (cdr val))))
        (t val)))

(declaim (ftype (function (optional-TaggedSExpr) t) ts-expr))
(defun ts-expr (tsexpr)
  (unless (missingp tsexpr)
    (recursive-ts-expr tsexpr)))

(declaim (ftype (function (optional-TaggedSExpr) t) ts-id))
(defun ts-id (tsexpr)
  (unless (missingp tsexpr)
    (TaggedSExpr-id tsexpr)))

(defun status-is-pass (status)
  (or (eq status :ok)
      (eq status :warn)))

(defun status-is-fail (status)
  (eq status :fail))

(defun passing-completed-proofs (completed-proofs)
  (remove-if-not #'(lambda (proof-datum) (status-is-pass (CompletedProofDatum-status proof-datum))) completed-proofs))

(defun failing-completed-proofs (completed-proofs)
  (remove-if #'(lambda (proof-datum) (status-is-pass (CompletedProofDatum-status proof-datum))) completed-proofs))

;; Error conditions

;; This condition should be signalled if a top-level check-proof-struct function
;; wants to immediately fail a proof before all checks are completed.
(define-condition checker-stop-error (error)
  ())

;; Each defcond condition has 3 reporters:
;; - The "normal" reporter, e.g the second defcond argument. This is
;;   used by default when CL is printing the condition (e.g. with ~a).
;;   This may contain extra debug information.
;; - the long-reporter, used when printing output in the proof checker
;;   side panel. This defaults to the normal reporter.
;; - the short-reporter, used when generating messages to be shown in
;;   the editor on hover.

;; This is a condition that any error on a context item should inherit
;; from. This is because we implement get-target-id on this condition
;; to point to the context item for XText underlining purposes.
(defcond ctx-item-error checker-error
  (ctx-item) ())

(defmethod get-target-id ((condition ctx-item-error))
  (CtxItem-id (ctx-item-error/ctx-item condition)))

(defcond goal-error checker-error
  ((goal :type TaggedSExpr)) ())

(defmethod get-target-id ((condition goal-error))
  (TaggedSExpr-id (goal-error/goal condition)))

(defcond could-not-find-function-error checker-error 
  (fun)
  ("Could not find a function named ~S" fun))

;; Exportation errors
(defcond exportation-missing-error checker-error
  ()
  ("Missing exportation section when exportation is needed!")
  :category "BAD_EXPORTATION"
  :kind "EXPORTATION_MISSING")

(defcond exportation-not-equiv-ctrex-error checker-error
  (cxs original exported)
  ("Counterexample found when testing that original statement and statement after exportation are equivalent: ~% counterexample(s): ~a ~% original: ~a ~% exported: ~a" cxs original exported)
  :short-reporter
  ("Exported statement not equivalent to original: counterexamples ~%~a" cxs)
   :category "BAD_EXPORTATION"
   :kind "EXPORTATION_NOT_EQUIV_CTREX")

(defcond exportation-not-equiv-proof-error checker-error
  (original exported)
  ("Failed to prove that original statement is equivalent to statement after exportation: ~% original: ~a ~% exported: ~a" original exported)
  :short-reporter
  ("Could not prove exported statement equivalent to original")
  :category "BAD_EXPORTATION"
  :kind "EXPORTATION_NOT_EQUIV_PROOF_FAIL")

(defcond goal-not-equiv-completed-conclusion-cx-error goal-error
  (completed-conc cxs)
  ("Counterexample found when testing that goal is equivalent to the conclusion of the contract completed statement:~% counterexample(s) ~a ~% goal: ~a ~% conclusion ~a" cxs goal completed-conc)
  :short-reporter ("Goal is not equivalent to conclusion of contract completed statement: counterexamples ~%~a" cxs))

(defcond goal-not-equiv-completed-conclusion-proof-error goal-error
  (completed-conc)
  ("Failed to prove that goal is equivalent to the conclusion of the contract completed statement: ~% goal: ~a ~% conclusion ~a" goal completed-conc)
  :short-reporter ("Failed to prove goal is not equivalent to conclusion of contract completed statement"))

(defcond exported-completed-different-error checker-error
  (exported completed cxs)
  ("Contract completed statement and statement after exportation are different: ~%~a ~%vs ~%~a" exported completed)
  :category "EXPORTED_COMPLETED_DIFFERENT"
  :kind "EXPORTED_COMPLETED_DIFFERENT")

(defcond exported-completed-different-hyps-error checker-error
  (exported completed cxs)
  ("Counterexample found when testing that exported and completed statements have equivalent hypotheses after completion: ~% counterexample(s): ~a ~% exported stmt ~a ~% completed stmt ~a" cxs exported completed)
  :short-reporter ("Exported and completed statements do not have equivalent hypotheses: counterexamples ~%~a" cxs)
  :category "EXPORTED_COMPLETED_DIFFERENT"
  :kind "EXPORTED_COMPLETED_DIFFERENT")

(defcond exported-completed-different-concs-error checker-error
  (exported-conc completed-conc)
  ("Conclusions of exported statement and completed statement are different: ~%~a ~%vs ~%~a" exported-conc completed-conc))

(defcond exported-hyps-not-subset-of-completed-hyps-error checker-error
  (exported-hyps completed-hyps)
  ("Exported statement's hypotheses are not a subset of those of the completed statement: ~%~a ~%vs ~%~a" exported-hyps completed-hyps))

(defcond not-fully-exported checker-error
  (stmt)
  ("Statement is not fully exported:~%~a" stmt))

(defcond step-rel-contract-error checker-error
  (side rel before? expected-type)
  ("Since you are using the relation ~a, the ~a side of this step must be a ~a, but it is not!" rel (if before? "left-hand" "right-hand") expected-type))

(defcond contract-completion-test-error checker-error
  (step cxs)
  ("Counterexample found when checking step's contract obligations are met: ~% step ~a ~% counterexample(s): ~a" step cxs)
  :short-reporter
  ("Contracts for this step were not satisfied by the context: counterexamples ~%~a" cxs)
  :category "PROOF_STEP_ERROR"
  :kind "CONTRACT_CTREX")

(defcond contract-completion-proof-error checker-error
  (step context query)
  ("Contract completion check failed for step: ~% ~a ~% with context: ~% ~a ~% (query: ~a) ~%"
   step context query)
   :category "PROOF_STEP_ERROR"
   :kind "CONTRACT_PROOF_FAIL")

;; Context item errors
(defcond ctx-not-equivalent checker-error
  (cxs?)
  ("We weren't able to show that the context is equivalent to the hypotheses of the exported statement! ~:[~;~%Here are some counterexamples:~%~a~]" cxs? cxs?))

(defcond duplicate-ctx-item-error ctx-item-error
  (other-ctx-item)
  ("Multiple context items with name ~a: ~a~%~a" (CtxItem-name ctx-item) ctx-item other-ctx-item)
  :short-reporter
  ("Multiple context items with name ~a" (CtxItem-name ctx-item)))

(defcond ctx-wrong-order-error ctx-item-error
  (should-be-hyp)
  ("Context items are in the wrong order! ~a should be ~S" (CtxItem-name ctx-item) should-be-hyp)
  :short-reporter
  ("Wrong order: ~a should be ~S" (CtxItem-name ctx-item) should-be-hyp))

(defcond ctx-item-wrong-number-error ctx-item-error
  (correct-name ctx)
  ("Incorrectly named context item: ~a should be named ~a~%~S" ctx-item correct-name ctx)
  :short-reporter
  ("Context item should be named ~a" correct-name))

(defcond derived-context-test-error ctx-item-error
  (cxs)
  ("Counterexample found when testing derived context item ~a: ~a" ctx-item cxs)
  :short-reporter
  ("Derived context item is not valid: counterexamples ~%~a" cxs)
  :category "DERIVED_CTX_ERROR"
  :kind "DERIVED_CTX_CTREX")

(defcond derived-context-missing-hints-error ctx-item-error
  (hints query)
  ("Couldn't prove a derived context item with provided hints:~%~a~%Try providing additional hints - common missing hints include the definition of function and relevant context items" ctx-item)
;;  ("Failed to prove step correctness in min theory + hints for derived ctx item: ~% ~a ~% with hints: ~% ~S ~% (query: ~S) ~%" ctxitem hints query)
  :short-reporter
  ("Couldn't prove valid with provided hints. Try providing additional hints - common missing hints include the definition of function and relevant context items")
  :category "DERIVED_CTX_ERROR"
  :kind "DERIVED_CTX_MISSING_HINTS_ERROR")

(defcond derived-context-contract-test-error ctx-item-error
  (ctx cxs)
  ("Counterexample found when checking contract obligations for derived context item~%~a in context ~a :~%~a" ctx-item ctx cxs)
  :short-reporter
  ("Contracts for derived context item were not satisfied by the context: counterexamples ~%~a" cxs))

(defcond derived-context-contract-proof-error ctx-item-error
  (ctx)
  ("Couldn't prove that contracts for derived context item ~a are satisfied by context ~a." ctx-item ctx)
  :short-reporter
  ("Couldn't prove that contracts for derived context item are satisfied by the context."))

(defcond hyps-maybe-unsat-warning checker-warning
  (hyps)
  ("Hypotheses may be unsat: ~a" hyps)
  :short-reporter
  ("Hypotheses may be unsatisfiable - double check that they are OK!")
  :category "BAD_COMPLETION"
  :kind "COMPLETION_HYPS_MAYBE_UNSAT")

(defcond statement-not-boolean-ctrex-error checker-error
  (query cxs)
  ("Counterexample found when testing that ~a is boolean: ~%~a" query cxs)
  :short-reporter
  ("Statement isn't boolean - counterexamples ~%~a" cxs))

(defcond steps-imply-goal-ctrex-error checker-error
  (cxs)
  ("Counterexample found when checking that steps imply goal:~%~a" cxs)
  :short-reporter
  ("Steps don't imply goal: ~a" cxs)
  :category "STEPS_IMPLY_GOAL_ERROR"
  :kind "STEPS_IMPLY_GOAL_CTREX")

(defcond steps-imply-goal-proof-error checker-error
  ()
  ("Unable to prove that steps imply goal")
  :category "STEPS_IMPLY_GOAL_ERROR"
  :kind "STEPS_IMPLY_GOAL_PROOF_FAIL")

;; Errors involving hints
(defcond ctxitem-not-found-error checker-error
  (name)
  ("Could not find context item with name ~S" name))

(defcond hint-error checker-error
  (message user-message hint)
  ("Hint error: ~a~a" message hint)
  :short-reporter
  ((if user-message user-message message))
  :category "HINT_ERROR"
  :kind "HINT_ERROR")

(defmethod get-target-id ((condition hint-error))
  (TaggedSExpr-id (hint-error/hint condition)))

(defcond unknown-axiom-error checker-error
  (axiom-name)
  ("Unknown axiom ~S" axiom-name)
  :short-reporter
  ("Unknown axiom"))

;; Errors involving step checking
(defcond check-step-test-error checker-error
  (step cxs)
  ("Counterexample found when testing step ~a: ~%~a" step cxs)
  :short-reporter
  ("Bad proof step: found counterexamples ~%~a" cxs)
  :category "PROOF_STEP_ERROR"
  :kind "PROOF_STEP_CTREX")

(defcond check-step-missing-hints-error checker-error
  (step hints query)
  ("Couldn't prove a step with provided hints:~%~a~%Try providing additional hints - common missing hints include the definition of function and relevant context items" step)
  ;;("Failed to prove step correctness in min theory + hints for step: ~% ~a ~% with hints: ~% ~S ~% (query: ~S) ~%"
  ;; step hints query)
  :short-reporter
  ("Couldn't prove step with provided hints. Try providing additional hints - common missing hints include the definition of function and relevant context items")
  :category "PROOF_STEP_ERROR"
  :kind "PROOF_STEP_MISSING_HINTS")

(defcond check-step-missing-hints-missing-instantiation-error checker-error
  (step hints query)
  ("Couldn't prove a step with provided hints:~%~a~%Try providing additional hints - common missing hints include the definition of function and relevant context items" step)
  ;;("Failed to prove step correctness in min theory + hints for step: ~% ~a ~% with hints: ~% ~S ~% (query: ~S) ~%"
  ;; step hints query)
  :short-reporter
  ("Couldn't prove step with provided hints. You've provided a lemma without  Try providing additional hints - common missing hints include the definition of function and relevant context items")
  :category "PROOF_STEP_ERROR"
  :kind "PROOF_STEP_MISSING_HINTS_EMPTY_INSTANTIATION")

;; Errors involving induction
(defcond induction-cases-duplicate-name-error checker-error
  (name)
  ("Two or more induction lemmas have the name ~S" name))

(defcond induction-cases-bijection-too-many checker-error
  (unused-cases)
  ("You provided too many cases. The following aren't needed based on the proof obligations we generated: ~a" (mapcar #'get-proof-printable-name unused-cases))
  :short-reporter ("This case is not needed.")
  :category "BAD_IND_LEMMAS"
  :kind "EXTRA_INDUCTION_CASE")

(defcond induction-cases-bijection-too-few checker-error
  (missing-obligations)
  ("You provided too few cases. You're missing the following induction obligations:~%~S" missing-obligations)
  :category "BAD_IND_LEMMAS"
  :kind "MISSING_INDUCTION_CASES")

(defcond induction-cases-bijection-unmatched checker-error
  (missing-obligations)
  ("Some cases don't match up with any of the proof obligations we generated. You need to match the following:~%~S" missing-obligations)
  :short-reporter
  ("This case doesn't match up with any of the proof obligations we generated.")
  :category "BAD_IND_LEMMAS"
  :kind "UNMATCHED_INDUCTION_CASES")

(defcond ind-term-error checker-error
  (message user-message hint)
  ("Error in the induction term: ~a" message)
  :category "BAD_TERM"
  :kind "INDUCTION_TERM_INCORRECT")

(defcond induction-term-not-call-error checker-error
  ()
  ("The induction term should be a call to a function. You provided only a name.")
  :category "BAD_TERM"
  :kind "INVALID_INDUCTION")

(defcond induction-term-no-proof-obligations checker-error
  ()
  ("The induction term gives rise to 0 proof obligations. Ensure that you've provided a call to a recursive function.")
  :category "BAD_TERM"
  :kind "NO_OBLIGATIONS")

(defcond induction-term-nested-calls checker-error
  ()
  ("The induction term should not contain any nested function calls!")
  :category "BAD_TERM"
  :kind "NESTED_CALLS")

(defcond missing-goal-error checker-error
  ()
  ("Missing Goal section."))

(defcond invalid-term-error checker-error
  (sexpr source extra-info)
  ("The term you provided for ~a is not a valid ACL2s term.~%The following might help: ~a" source extra-info))

(defcond missing-term-error checker-error
  (source)
  ("You did not provide a term for ~a, but one is required!" source))

(defcond guard-obligation-ctrex-error checker-error
  (obligation cxs)
  ("Counterexample found when testing guard obligation:~%~a~%~a"
   obligation cxs))

(defcond guard-obligation-proof-failed-warning checker-warning
  (obligation debug-info)
  ("Failed to prove obligation:~%  ~a~% Debug: ~a" obligation debug-info))

(defcond unknown-relation-error checker-error
  (rel)
  ("Unknown relation ~S" rel))

(defcond proof-exportation-fail checker-error
  (name thm-stmt)
  ("The proof of the equivalence of the exportation and original statement for ~S failed!~%~S" name thm-stmt))

(defcond proof-builder-proof-fail checker-error
  (name thm-stmt instructions)
  ("The proof-builder proof for proof ~S failed!~%~S~%~S" name thm-stmt instructions))

(defcond proof-builder-induction-proof-bijection-fail checker-error
  (proof bij-cond)
  ("The proof-builder proof for proof ~a ~a failed!~%~a" (Proof-kind proof) (Proof-name proof) bij-cond))

(defcond proof-builder-induction-missing-gen-thm checker-error
  (case data)
  ("Missing a gen-thm when constructing proof-builder proof for case ~a!~%~a" case data))

(defcond theorem-already-exists-error checker-error
  (name)
  ("A theorem already exists with the name ~a" name))

(defcond used-contract-completion-warning checker-warning
  (proof proof-stack)
  ("A nontrivial contract completion was provided for a proof: ~a" (get-full-proofname-in-stack proof proof-stack)))

(defcond skip-proofs-failed-error checker-error
  (name)
  ("Failed to perform a skip-proofs proof for ~a" name))

(defmacro add-message-and-error-out (error-name &rest args)
  (let ((varname (gensym "ERROR-CONDITION-")))
    `(let ((,varname (make-condition ',error-name ,@args)))
       (add-message (get-target-id ,varname)
                          (short-report ,varname)
                          :category (get-condition-category ,varname)
                          :kind (get-condition-kind ,varname))
       (signal ,varname)
       :fail)))

(defmacro msg-and-error (&key category kind id message)
  `(lambda (condition)
     (add-message ,(or id '(get-target-id condition))
                        ,(or message '(short-report condition))
                        :category ,(or category '(get-condition-category condition))
                        :kind ,(or kind '(get-condition-kind condition)))
     (signal condition)))

(defmacro message-wrap (expr &rest args &key &allow-other-keys)
  `(handler-bind
       ((checker-error (msg-and-error ,@args)))
     ,expr))

;; some utils

(defun replace-all-in (x to-replaces replace-with)
  (cond ((member x to-replaces :test #'equal) replace-with)
        ((consp x)
         (cons (replace-all-in (car x) to-replaces replace-with)
               (replace-all-in (cdr x) to-replaces replace-with)))
        (t x)))

(defun replace-implies-impliez (x)
  (acl2::sublis-fn-simple '((implies . acl2::impliez) (=> . acl2::impliez) (-> . acl2::impliez)) x))

;; Exportation
(declaim (ftype (function ((not TaggedSExpr)) boolean) exportation-possible?))
(defun exportation-possible? (term)
  (match term
    ((list (is-op? implies) hyps conc)
     (or
      ;; conc is an implication
      (match conc ((list* (is-op? implies) _) t))
      ;; exportation is possible within one of the hyps
      (match hyps
        ((list* (is-op? and) args) (some #'exportation-possible? args)))
      ;; exportation is possible within a subterm of the conclusion
      (match conc ((list* _ args) (some #'exportation-possible? args)))))
    ((list* _ args) (some #'exportation-possible? args))))

(defun exportation-simplify-step (term)
  (match term
         ((list (is-op? implies) hyps conc)
          (let ((new-hyps (if (consp hyps) (mapcar #'exportation-simplify hyps) hyps))
                (new-conc (exportation-simplify-step conc)))
            (match new-conc
                   ((list (is-op? implies) inner-hyps inner-conc)
                    (list (car new-conc)
                          (conjunction-terms new-hyps inner-hyps)
                          inner-conc))
                   (otherwise (list (car term) new-hyps new-conc)))))
         (otherwise term)))

(declaim (ftype (function ((not TaggedSExpr)) t) exportation-simplify))
;; Perform exportation to simplify the given term
(defun exportation-simplify (term)
  (let ((new-term (exportation-simplify-step term)))
    (if (equal term new-term)
        term
      (exportation-simplify new-term))))

;;finds contract lemma from base cases
(defun find-contract-lemma (base-cases)
  (if (endp base-cases)
      nil
    (let ((cur (car base-cases)))
      (if (test-then-thm-min-fails? `acl2s::(equal ,prover::cur t) :fail-ok t)
          (find-contract-lemma (cdr base-cases))
        cur))))

(declaim (ftype (function ((not TaggedSExpr) (not TaggedSExpr)) boolean) check-exportation-equiv))
(defun check-exportation-equiv (stmt-exprt stmt-orig)
  ;; Generate the propositional skeleton for the two statements modulo
  ;; type predicates
  (multiple-value-bind
    (equiv-skel amap)
    (tp::p-skeleton `(acl2::iff ,stmt-exprt ,stmt-orig)
                    ;; We want to abstract all function calls that are
                    ;; not type predicate applications
                    :abstract-termp #'(lambda (term) (not (and (consp term) (is-type-predicate (car term))))))
    (let* ((bvars (tp::pvars equiv-skel))
           (query (tp::to-acl2-no-pskel `(acl2::implies ,(tp::boolean-hyps (mapcar #'cdr amap)) ,equiv-skel))))
      (v:debug :status "Skeleton ~S~%Term map ~S" equiv-skel amap)
      (handler-case (test-thm-min query)
        (test-found-ctrex-error (condition)
                                (error 'exportation-not-equiv-ctrex-error
                                       :cxs (test-found-ctrex-error/cxs condition)
                                       :original stmt-orig
                                       :exported stmt-exprt))
        (min-thm-failed-error (_) (error 'exportation-not-equiv-proof-error
                                         :original stmt-orig
                                         :exported stmt-exprt))))))

;; Check that the given list of statements is SAT by attempting to find
;; a counterexample to the statement that the list of statements is
;; UNSAT
(defun check-hyps-sat (hyps)
  (let* ((query `acl2s::(equal (and ,@prover::hyps) nil))
         (res (test? query :fail-ok t)))
    ;; res wil be nil if no counterexamples are found.
    (if res
        t
      (warn 'hyps-maybe-unsat-warning :hyps hyps))))

;; Check that the given RHS is a boolean under the given hypotheses
(declaim (ftype (function ((not TaggedSExpr) (not TaggedSExpr)) boolean) check-is-boolean))
(defun check-is-boolean (hyps rhs)
  (let ((query `acl2s::(implies (and ,@prover::hyps) (booleanp ,prover::rhs))))
    (handler-case (test-thm-min-then-full query)
      (test-found-ctrex-error (condition)
                              (error 'statement-not-boolean-ctrex-error
                                     `(implies (and ,@prover::hyps) ,prover::rhs)
                                     (test-found-ctrex-error/cxs condition)))
      (full-thm-failed-error (_) nil)
      (used-full-theory (_) t))
    t))


(declaim (ftype (function (list) boolean) check-each-obligation))
(defun check-each-obligation (obligations)
  (if (endp obligations)
      t
    (let* ((debug-info (car (car obligations)))
           (obligation (second (car obligations)))
           (res (handler-case (test-thm-full obligation)
                  (test-found-ctrex-error (condition)
                                          (error 'guard-obligation-ctrex-error
                                                 :obligation (acl2s-untranslate obligation)
                                                 :cxs (test-found-ctrex-error/cxs condition)))
                  (full-thm-failed-error (_) (signal 'guard-obligation-proof-failed-warning
                                                    :obligation (acl2s-untranslate obligation)
                                                    :debug-info debug-info)))))
      (check-each-obligation (cdr obligations)))))

(declaim (ftype (function ((not TaggedSExpr)) boolean) check-contract))
(defun check-contract (stmt-completed)
  (let* ((impliez-stmt (replace-implies-impliez stmt-completed))
         (obligations (rguard-obligations-debug impliez-stmt)))
    (check-each-obligation obligations)))

(declaim (ftype (function ((not TaggedSExpr) (not TaggedSExpr) (not TaggedSExpr) (not TaggedSExpr)) Status) check-completion-hyps-equiv))
(defun check-completion-hyps-equiv (stmt-exported stmt-completed exported-hyps completed-hyps)
  ;; TODO: this is unsafe. use acl2s utilities code/properties.lisp
  ;; TODO: make sure that the hyps are in the right order. Can check this by checking that the guard obligations for the completed statement = t
  (let* ((stmt-exported (replace-implies-impliez stmt-exported))
         (stmt-completed (replace-implies-impliez stmt-completed))
         (exported-hyps (mapcar #'replace-implies-impliez exported-hyps))
         (completed-hyps (mapcar #'replace-implies-impliez completed-hyps))
         (obligations (mapcar #'replace-implies-impliez (rguard-obligations stmt-exported)))
         (query `acl2s::(equal (and ,@prover::completed-hyps)
                               (and ,@prover::obligations ,@prover::exported-hyps))))
    (handler-case (test-thm-min-then-full query)
      (test-found-ctrex-error
       (condition)
       ;; TODO: what should we do if the user provides stmt-completed but not stmt-exported?
       (error 'exported-completed-different-hyps-error
              :exported stmt-exported
              :completed stmt-completed
              :cxs (test-found-ctrex-error/cxs condition)))
      (full-thm-failed-error (_) nil))
    :ok))

(declaim (ftype (function (optional-TaggedSExpr t) boolean) check-goal-equiv-completed-conc))
(defun check-goal-equiv-completed-conc (goal completed-conc)
  (when (missingp goal) (error 'missing-goal-error))
  (let ((goal-stmt (ts-expr goal)))
    (handler-case (test-thm-min `acl2s::(equal ,prover::goal-stmt ,prover::completed-conc))
      (test-found-ctrex-error (condition)
                              (error 'goal-not-equiv-completed-conclusion-cx-error
                                     :goal goal
                                     :completed-conc completed-conc
                                     :cxs (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error (_)
                            (error 'goal-not-equiv-completed-conclusion-proof-error
                                   :goal goal
                                   :completed-conc completed-conc)))
    t))

(declaim (ftype (function (TaggedSExpr optional-TaggedSExpr optional-TaggedSExpr) Status) check-completion-equiv))
(defun check-completion-equiv (stmt-original stmt-exported stmt-completed)
  (let ((completed-hyps (get-hyps (ts-expr stmt-completed)))
        (completed-conc (get-conc (ts-expr stmt-completed)))
        (exported-hyps (get-hyps (ts-expr stmt-exported)))
        (exported-conc (get-conc (ts-expr stmt-exported))))
    (cond ((or
            ;; neither were provided or both were provided and are equivalent
            (equal (ts-expr stmt-exported) (ts-expr stmt-completed))
            ;; exactly one of the two was provided
            (not (equal (missingp stmt-exported) (missingp stmt-completed))))
           :ok)
          ;; TODO why do we need the below null check??
          ((null completed-hyps) ;; sanity check:
           (error 'exported-completed-different-error :exported stmt-exported :completed stmt-completed))
          (t
           ;; first run some cheap checks
           (cond ((equal completed-conc (TaggedSExpr-expr stmt-original)) t)
                 ((not (equal exported-conc completed-conc))
                  (error 'exported-completed-different-concs-error :exported-conc exported-conc :completed-conc completed-conc))
                 ((not (subsetp exported-hyps completed-hyps :test #'equal))
                  (error 'exported-hyps-not-subset-of-completed-hyps-error :exported-hyps exported-hyps :completed-hyps completed-hyps)))
           ;; then check that the contract completion's hyps are
           ;; exactly equal to the exportation's plus guard
           ;; obligations.
           (check-completion-hyps-equiv (ts-expr stmt-exported) (ts-expr stmt-completed) exported-hyps completed-hyps)))))

;; Context functions

(deftype CtxItem-list () '(or null (cons CtxItem list)))

(defun get-context-bodies (context)
  (mapcar (lambda (c) (TaggedSExpr-expr (CtxItem-stmt c))) context))

;; Check that the statement we're trying to prove is equivalent to (implies (C1 ... Cn) goal)
;; To check that the context is sane given the statement we're trying to prove,
;; check that (iff stmt (implies (and C1 C2 ... Cn) goal))
(declaim (ftype (function (TaggedSExpr CtxItem-list optional-TaggedSExpr) boolean) check-context-sane))
(defun check-context-sane (stmt ctx goal)
  (when (equal goal :missing) (error 'missing-goal-error :target-id (Proof-id *CURRENT-PROOF*)))
  (let* ((stmt-expr (TaggedSExpr-expr stmt))
         (goal-expr (ts-expr goal))
         (context-bodies (get-context-bodies ctx))
         (to-check `acl2s::(iff ,prover::stmt-expr (implies (and ,@prover::context-bodies) ,prover::goal-expr))))
    (handler-case (test-thm-min to-check)
      (test-found-ctrex-error (condition)
                              (error 'ctx-not-equivalent :cxs? (test-found-ctrex-error/cxs condition)
                                     :target-id (mapcar #'CtxItem-id ctx)))
      (min-thm-failed-error (_)
                            (error 'ctx-not-equivalent
                                   :target-id (mapcar #'CtxItem-id ctx))))))

(declaim (ftype (function (CtxItem-list &key (:name-prefix string)) t) check-context-numbering))
(defun check-context-numbering (ctx &key (name-prefix "C"))
  (loop for i from 1 to (length ctx)
        for ctx-item in ctx
        ;; note that string-equal is case insensitive, which is nice here
        do (when (not (string-equal (symbol-name (CtxItem-name ctx-item))
                                    (concatenate 'string name-prefix (write-to-string i))))
             (error 'ctx-item-wrong-number-error
                    :ctx ctx
                    :ctx-item ctx-item
                    :correct-name (concatenate 'string name-prefix (write-to-string i))))))

(declaim (ftype (function (symbol CtxItem-list) boolean) in-context))
(defun in-context (name context)
  (some #'(lambda (ctx-item) (equal name (CtxItem-name ctx-item))) context))

(declaim (ftype (function (symbol CtxItem-list) CtxItem) get-context-item))
(defun get-context-item (name context)
  (let ((item (find-if #'(lambda (ctx-item) (equal name (CtxItem-name ctx-item))) context)))
    (if (equal item nil)
        (error 'ctxitem-not-found-error :name name)
      item)))

(defvar *hint-axioms*
  '((proof::car-cdr
     ((:REWRITE ACL2::CAR-CONS)
      (:REWRITE ACL2::CDR-CONS)
      acl2::car-cdr-elim
      acl2::cons-equal
      acl2::default-car
      acl2::default-cdr
      acl2::cons-car-cdr))
    (proof::cons
     ((:REWRITE ACL2::CAR-CONS)
      (:REWRITE ACL2::CDR-CONS)
      acl2::car-cdr-elim
      acl2::cons-equal
      acl2::default-car
      acl2::default-cdr
      acl2::cons-car-cdr))
    (proof::equal ())
    (proof::equality ())
    (proof::if ())
    (proof::consp ())))

(defun axiom-rules (axiom-name)
  (let ((axioms (assoc axiom-name *hint-axioms*)))
    (if axioms
        (second axioms)
      (error 'unknown-axiom-error :axiom-name axiom-name))))

(declaim (ftype (function (string CompletedProofData) optional-Proof) find-proof-with-name))
(defun find-proof-with-name (name proofs)
  (cond ((endp proofs) nil)
        ((equal (string-upcase name) (string-upcase (Proof-name (CompletedProofDatum-proof (car proofs))))) (CompletedProofDatum-proof (car proofs)))
        (t (find-proof-with-name name (cdr proofs)))))

;; Get the "final sexpr" of the proof as well the name of the proof
;; section it came from.
(defun get-proof-final-sexpr (proof)
  (let ((contract-completion (Proof-contract-completion proof))
        (exportation (Proof-exportation proof))
        (stmt (Proof-stmt proof)))
    (cond ((not (missingp contract-completion)) (values contract-completion "Contract Completion"))
          ((not (missingp exportation)) (values exportation "Exportation"))
          (t (values stmt "Proof Statement")))))

(defun check-is-rule-name-designator (name hint)
  (unless (is-rule-name-designator name)
    (error 'hint-error
           :hint hint
           :message (if (is-acl2-macro name)
                        (format nil "~a is a macro, not a function, so you can't use its definition in a hint!"
                                name)
                      (format nil "~a doesn't seem to be a defined function!" name)))))

(defun check-is-function-name (name hint)
  (unless (is-function name)
    (error 'hint-error
           :hint hint
           :message (format nil "~a is not the name of a defined function!" name))))

(defun check-hint-substitution (substitution-list hint)
  (if (not (listp substitution-list))
      (error 'hint-error
             :hint hint
             :message (format nil "~a is not a valid substitution, as a substitution must be a list" substitution-list))
    (loop for substitution in substitution-list
          do (match substitution
               ((list var term)
                (unless (is-var var)
                  (error 'hint-error
                         :hint hint
                         :message (format nil "~a is not a valid substitution term because ~a is not a variable." substitution var)))
                (unless (is-acl2s-term term)
                  (error 'hint-error
                         :hint hint
                         :message (format nil "In the substitution term ~a, ~a is not a valid ACL2s term." substitution term))))
               (otherwise (error 'hint-error
                                 :hint hint
                                 :message (format nil "~a is not valid as a substitution term, as it doesn't have exactly two elements." substitution)))))))

(declaim (ftype (function (TaggedSExpr) boolean) hint-is-lemma-without-substitution))
(defun hint-is-lemma-without-substitution (hint)
  (match (ts-expr hint)
    ((list :lemma nil) t)
    (otherwise nil)))

;; Convert a hint into the appropriate ACL2s data
;; return value is a list (hypotheses rules use)
(declaim (ftype (function (TaggedSExpr t CompletedProofData &key (:handle-ctx-hints? boolean)) t) hint-to-acl2s))
(defun hint-to-acl2s (hint context completed-proofs &key (handle-ctx-hints? t))
  (match (ts-expr hint)
    (:prop-logic '(nil nil nil))
    (:arith '(nil (acl2::arith-5-theory acl2s::arith-theory) nil))
    (:modus-ponens '(nil nil nil))
    (:eval (list nil '(acl2s::executable-theory) nil))
    (:noop '(nil nil nil))
    ((list :debug-rules rules) (list nil rules nil))
    ((list :axiom axiom-name) (list nil
                                    (handler-case
                                        (axiom-rules axiom-name)
                                      (unknown-axiom-error (condition)
                                                           (error 'hint-error
                                                                  :hint hint
                                                                  :message "Unknown axiom name")))
                                    nil))
    ((list :context ctx-id) (list (when handle-ctx-hints?
                                    (list (TaggedSExpr-expr
                                           (CtxItem-stmt
                                            (handler-case (get-context-item ctx-id context)
                                              (ctxitem-not-found-error (condition)
                                                                       (error 'hint-error
                                                                              :hint hint
                                                                              :message (format nil "Unknown context item ~a" ctx-id))))))))
                                  nil
                                  nil))
    ((list :fun fun-name)
     (check-is-function-name fun-name hint)
     (check-is-rule-name-designator fun-name hint)
     (list nil (list fun-name) nil))
    ;; Step checking operates in a theory containing all of the
    ;; function contracts. So this hint doesn't do anything.
    ;; TODO: we should deprecate this hint.
    ((list :fun-contract fun-name)
     (check-is-rule-name-designator fun-name hint)
     (list nil nil nil))
    ((or (list :lemma lemma-name instantiation)
         (and (list :lemma lemma-name)
              (<> instantiation nil)))
     (let ((pass-proof-with-name (find-proof-with-name (symbol-name lemma-name) (passing-completed-proofs completed-proofs)))
           (fail-proof-with-name (find-proof-with-name (symbol-name lemma-name) (failing-completed-proofs completed-proofs)))
           (is-thm (is-theorem? lemma-name)))
       (cond ((not (or pass-proof-with-name fail-proof-with-name is-thm))
              (error 'hint-error
                     :hint hint
                     :message (format nil "No lemma with the name ~S exists" lemma-name)
                     :user-message "No lemma with this name exists"))
             (fail-proof-with-name
              (error 'hint-error
                     :hint hint
                     :message (format nil "Attempting to use a lemma that failed: ~a" lemma-name)
                     :user-message "Attempting to use a failed lemma"))
             ((not instantiation)
              ;; Add an identity instantiation if one wasn't provided and we're
              ;; using a previously proven hand-proof lemma
              (list nil nil `((:instance ,lemma-name ))))
             ;; TODO we can do more input validation here
             (instantiation
              (check-hint-substitution instantiation hint)
              (list nil nil (list (append (list :instance lemma-name) instantiation)))))))
    (otherwise (error 'hint-error
                      :hint hint
                      :message "Unknown hint"))))

(defun step-rel-guard (rel)
  (match rel
    ((or '< '> '= '>= '<=) '(acl2s::rationalp "rational number"))
    (otherwise nil)))

;; Check that the expression (rel before after) holds, using the given hints and context
(declaim (ftype (function ((not TaggedSExpr) (not TaggedSExpr) (not TaggedSExpr) (not TaggedSExpr) (not TaggedSExpr) CompletedProofData &key (:id t)) boolean) check-step))
(defun check-step (rel before after hints context completed-proofs &key (id nil))
  (let* ((hint-lists (mapcar (lambda (hint)
                               (hint-to-acl2s hint context completed-proofs)) hints))
         (hyps (append-all (mapcar #'car hint-lists)))
         (rules (append-all (mapcar #'second hint-lists)))
         (uses (append-all (mapcar #'third hint-lists)))
         (predicate-context-bodies (get-context-bodies (remove-if-not #'CtxItem-type-predicatep context)))
         (contracts (rguard-obligations `acl2s::(implies (and ,@prover::predicate-context-bodies ,@prover::hyps)
                                                         (,prover::rel ,prover::before ,prover::after))))
         (context-bodies (get-context-bodies context))
         (step-query `acl2s::(acl2::implies
                              (and ,@prover::contracts ,@prover::predicate-context-bodies ,@prover::hyps)
                              (,prover::rel ,prover::before ,prover::after)))
         (contract-completion-check-query
          `acl2s::(implies (and ,@prover::context-bodies)
                           (and ,@prover::contracts)))
         (rel-guard (step-rel-guard rel)))
    (when rel-guard
      (handler-case (test-thm-full `acl2s::(implies (and ,@prover::context-bodies)
                                                    (,(car prover::rel-guard) ,prover::before)))
        (test-found-ctrex-error ()
                                (error 'step-rel-contract-error
                                       :target-id id
                                       :side before
                                       :before? t
                                       :rel rel
                                       :expected-type (second rel-guard)))
        (full-thm-failed-error ()
                               (error 'step-rel-contract-error
                                      :target-id id
                                      :side before
                                      :before? t
                                      :rel rel
                                      :expected-type (second rel-guard))))
      (handler-case (test-thm-full `acl2s::(implies (and ,@prover::context-bodies)
                                                    (,(car prover::rel-guard) ,prover::after)))
        (test-found-ctrex-error ()
                                (error 'step-rel-contract-error
                                       :target-id id
                                       :side after
                                       :before? nil
                                       :rel rel
                                       :expected-type (second rel-guard)))
        (full-thm-failed-error ()
                               (error 'step-rel-contract-error
                                      :target-id id
                                      :side after
                                      :before? nil
                                      :rel rel
                                      :expected-type (second rel-guard)))))
    (handler-case (test-thm-min-with-contracts step-query :rules rules :goal-hints `acl2s::(:do-not-induct t :use ,prover::uses))
      ;; TODO: check that this ctrex is consistent with query hyps
      (test-found-ctrex-error (condition)
                              (error 'check-step-test-error
                                     :target-id id
                                     :step (list rel before after)
                                     :cxs (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error (_)
                            (if (some #'hint-is-lemma-without-substitution hints)
                                (error 'check-step-missing-hints-error
                                       :target-id id
                                       :step (list rel before after)
                                       :hints hints
                                       :query step-query)
                              (error 'check-step-missing-hints-error
                                     :target-id id
                                     :step (list rel before after)
                                     :hints hints
                                     :query step-query))))
    (handler-case (test-thm-full contract-completion-check-query)
      (test-found-ctrex-error (condition)
                              (error 'contract-completion-test-error
                                     :target-id id
                                     :step (list rel before after)
                                     :cxs (test-found-ctrex-error/cxs condition)))
      (full-thm-failed-error (_) (error 'contract-completion-proof-error
                                        :target-id id
                                        :step (list rel before after)
                                        :hints hints
                                        :query contract-completion-check-query)))
    t))


(declaim (ftype (function (CtxItem list CompletedProofData) boolean) check-derived-context-item))
(defun check-derived-context-item (item context completed-proofs)
  (v:debug :status "Checking derived context item: ~S" item)
  (let ((id (CtxItem-id item)))
    (handler-case (check-step 'acl2s::equal (TaggedSExpr-expr (CtxItem-stmt item)) 't (CtxItem-hints item) context completed-proofs)
      (check-step-test-error (condition)
                             (error 'derived-context-test-error
                                    :ctx-item item
                                    :cxs (check-step-test-error/cxs condition)))
      (check-step-missing-hints-error (condition)
                                      (error 'derived-context-missing-hints-error
                                             :ctx-item item
                                             :hints (check-step-missing-hints-error/hints condition)
                                             :query (check-step-missing-hints-error/query condition)))
      (contract-completion-test-error (condition)
                                      (error 'derived-context-contract-test-error
                                             :ctx-item item
                                             :cxs (contract-completion-test-error/cxs condition)))
      (contract-completion-proof-error (condition)
                                       (error 'derived-context-contract-proof-error
                                              :ctx-item item))
      (:no-error (res)
                 (calculate-context-type-predicate item)
                 res))))

(declaim (ftype (function (list list CompletedProofData) list) check-derived-context-all))
(defun check-derived-context-all (derived-ctx context completed-proofs)
  (if (endp derived-ctx)
      context
    (let ((ctx-item (car derived-ctx)))
      (if (equal :discard
                 (restart-case
                  (check-derived-context-item ctx-item
                                              context
                                              completed-proofs)
                  (ignore-context-item-failure ()
                                               :report (lambda (stream) (format stream "Ignore the failure in checking derived context item ~S and include it in the context" (CtxItem-name ctx-item)))
                                               (warn (format nil "Ignored derived context item ~S" (CtxItem-name ctx-item)))
                                               :ignore)
                  (discard-context-item ()
                                        :report (lambda (stream) (format stream "Discard derived context item ~S" (CtxItem-name ctx-item)))
                                        :discard)))
          (check-derived-context-all (cdr derived-ctx)
                                     context
                                     completed-proofs)
        (check-derived-context-all (cdr derived-ctx)
                                   (cons (car derived-ctx) context)
                                   completed-proofs)))))

(declaim (ftype (function ((or symbol string)) symbol) get-relation-function))
(defun get-relation-function (rel)
  (match rel
    ((type symbol) rel)
    (otherwise (error 'unknown-relation-error :rel rel))))

(defun check-proof-steps (steps context completed-proofs)
  (if (endp steps)
      t
    (let ((step (car steps)))
      (progn
        (restart-case
         (check-step (get-relation-function (ProofStep-rel step))
                     (ts-expr (ProofStep-before step))
                     (ts-expr (ProofStep-after step))
                     (ProofStep-hints step)
                     context
                     completed-proofs
                     :id (ProofStep-id step))
         (skip-step () (warn "Skipped step")))
        (check-proof-steps (cdr steps) context completed-proofs)))))

;; TODO make this more efficient
;; this function screws with the order of the elements.
;; For this reason we sort the context items later.
(declaim (ftype (function (CtxItem-list CtxItem-list) CtxItem-list) merge-contexts))
(defun merge-contexts (ctx1 ctx2)
  (if (endp ctx1)
      (reverse ctx2)
    (let ((name (CtxItem-name (car ctx1))))
      (if (in-context name ctx2)
          (error 'duplicate-ctx-item-error
                 :ctx-item (car ctx1)
                 :other-ctx-item (get-context-item name ctx2))
        (merge-contexts (cdr ctx1) (cons (car ctx1) ctx2))))))

(deftype Proof-list () '(or null (cons Proof list)))

(defun calculate-context-type-predicate (ctx-item)
  (when (not (CtxItem-type-predicatep ctx-item))
    (let ((stmt (ts-expr (CtxItem-stmt ctx-item))))
      (setf (CtxItem-type-predicatep ctx-item)
            (and (consp stmt)
                 (is-type-predicate (car stmt)))))))

(defun calculate-context-type-predicates (context)
  (loop for ctx-item in context
        do (calculate-context-type-predicate ctx-item))
  context)

(declaim (ftype (function (CtxItem CtxItem) boolean) context-item-comparator))
(defun context-item-comparator (c1 c2)
  (let ((c1-name (symbol-name (CtxItem-name c1)))
        (c2-name (symbol-name (CtxItem-name c2))))
    (match (list (char c1-name 0) (char c2-name 0))
      ((list #\C #\D) t)
      ((list #\D #\C) nil)
      (otherwise
       (< (parse-integer c1-name :start 1)
          (parse-integer c2-name :start 1))))))
    

;; Combine the current context with the contexts of the items in the proof stack
(declaim (ftype (function (list Proof-list) list) get-full-context))
(defun get-full-context (context proof-stack)
  (loop for proof in proof-stack
        do (setf context (merge-contexts context
                                         (merge-contexts (Proof-ctx proof)
                                                         (Proof-derived-ctx proof)))))
  (let ((context (copy-seq context)))
    (sort context #'context-item-comparator)))

(declaim (ftype (function (ProofStep) list) step-to-expression))
(defun step-to-expression (step)
  (list (get-relation-function (ProofStep-rel step))
        (ts-expr (ProofStep-before step))
        (ts-expr (ProofStep-after step))))

(declaim (ftype (function (list list optional-TaggedSExpr) boolean) check-steps-imply-goal))
(defun check-steps-imply-goal (steps context goal)
  (when (missingp goal) (error 'missing-goal-error :target-id (Proof-id *CURRENT-PROOF*)))
  (let* ((goal-expr (ts-expr goal))
         (step-exprs (mapcar #'step-to-expression steps))
         (context-bodies (get-context-bodies context))
         (correctness-expr `(acl2::implies (acl2::and ,@step-exprs ,@context-bodies) ,goal-expr)))
    (progn (print correctness-expr)
    (let* (
         (obligations (rguard-obligations correctness-expr))
         (query `(acl2::implies (acl2::and ,@obligations) ,correctness-expr)))
    (handler-case (test-thm-min query)
      (test-found-ctrex-error (condition)
                              (error 'steps-imply-goal-ctrex-error
                                     :target-id (TaggedSExpr-id goal)
                                     :cxs (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error (_) (error 'steps-imply-goal-proof-error
                                       :target-id (TaggedSExpr-id goal))))
    t))))

;; These functions deal with generating a (def)thm form at the end of
;; a successfully checked proof.
;; In some situations we do a skip-proofs (if a nontrivial contract
;; completion was provided), but we normally generate proof-builder
;; instructions.
(defun generate-thm-skip-proofs (name thm-stmt)
  `(acl2::skip-proofs (acl2::defthm ,name ,thm-stmt :rule-classes nil)))

(declaim (ftype (function (symbol (not TaggedSExpr)) Status) define-thm-skip-proofs))
(defun define-thm-skip-proofs (name thm-stmt)
  (when (is-theorem-namep name)
    (error 'theorem-already-exists-error :name name))
  (let ((res (acl2s-event (generate-thm-skip-proofs name thm-stmt))))
    (if (car res)
        (error 'skip-proofs-failed-error :name name)
      :ok)))

(defun generate-thm-proof-builder (proof-name thm-stmt instructions define-thm?)
  (when (and define-thm? (is-theorem-namep proof-name))
    (error 'theorem-already-exists-error
           :name proof-name))
  (if define-thm?
      `(acl2::defthm ,proof-name ,thm-stmt :rule-classes nil :hints (("Goal" :instructions ,instructions)))
    `(acl2::thm ,thm-stmt :hints (("Goal" :instructions ,instructions)))))

(defun define-thm-proof-builder (thm-stmt proof context completed-proofs proof-stack define-thm? &key (proof-name (get-full-proofname proof)) (exportation-proof-name (calculate-exportation-proof-name proof-name)))
  (let* ((printable-name (get-proof-printable-name proof))
         (instructions (proof-to-proof-builder-instructions proof context completed-proofs proof-stack))
         (thm-form (handler-case
                       (generate-thm-proof-builder proof-name thm-stmt instructions define-thm?)
                     ;; gotta add the Proof-id here
                     (theorem-already-exists-error (c)
                                                   (error 'theorem-already-exists-error
                                                          :name proof-name
                                                          :target-id (Proof-id proof))))))
      (v:debug :status "Proving theorem ~S using the proof builder..." printable-name)
      (if define-thm?
          (progn
            (when (not (missingp (Proof-exportation proof)))
              (let* ((proof-expr `(equal ,(ts-expr (Proof-stmt proof))
                                         ,(ts-expr (Proof-exportation proof))))
                     (res (acl2s-event `(acl2::defthm ,exportation-proof-name ,proof-expr))))
                (when (car res)
                  (error 'proof-exportation-fail :name proof-name :thm-stmt proof-expr))))
            (let ((res (acl2s-event thm-form)))
              (when (car res)
                (error 'proof-builder-proof-fail :name proof-name :thm-stmt thm-stmt :instructions instructions))))
        (let ((res (acl2s-query thm-form)))
          (when (car res)
            (error 'proof-builder-proof-fail :name printable-name :thm-stmt thm-stmt :instructions instructions)))))
  :ok)

;; These functions and macros support error-handling
(defmacro eval-with-status (q &key fail-val)
  `(let ((did-warn nil))
     (handler-case
         (handler-bind
             ;; Note the difference between handler-case and handler-bind: handler-case
             ;; immediately unwinds to the handler code, whereas handler-bind pauses
             ;; execution, runs the handler code, and then resumes execution.
             ;; We handle this here because we don't want to unwind on a prover warning, since
             ;; it is possible that an error could be emitted later in the code, and we would
             ;; rather report that error than a warning.
             ((prover-warning #'(lambda (condition) (setq did-warn condition))))
           ,q)
       (:no-error (ret &rest args)
                  (declare (ignore args))
                  (values (if (not did-warn) :ok :warn) ret did-warn))
       (checker-error (condition)
       ;;(error (condition)
              (values :fail ,fail-val condition)))))

(defmacro print-result (q &key fail-val)
  `(multiple-value-bind
     (eval-status ret condition)
     (eval-with-status ,q :fail-val ,fail-val)
     (progn (print eval-status)
            (v:debug :status "~a" eval-status)
     (case eval-status
       (:ok
        (v:debug :status "OK")
        (print2 (green "OK"))
        (cons :ok ret))
       (:warn
        (v:debug :status "WARN ~a" condition)
        (print2 (yellow "WARN"))
        (print2 (long-report condition))
        (cons :warn ret))
       (:fail
        (v:debug :status "FAIL ~a" condition)
        (print2 (red "FAIL"))
        (print2 (long-report condition))
        (cons :fail ret))))))

(declaim (ftype (function (Status Status) Status) merge-statuses))
(defun merge-statuses (stat1 stat2)
  (cond ((or (status-is-fail stat1) (status-is-fail stat2)) :fail)
        ((or (equal :warn stat1) (equal :warn stat2)) :warn)
        ((and (equal :ok stat1) (equal :ok stat2)) :ok)
        (t (error "unknown args ~s ~s" stat1 stat2))))

(defun reduce-statuses (statuses)
  (reduce #'merge-statuses statuses :initial-value :ok))

(defmacro update-status (x)
  `(setf status (merge-statuses ,x status)))

(defmacro print-result-and-update-status (x &rest r)
  `(let ((res (print-result ,x ,@r)))
     (setf status (merge-statuses (car res) status))
     (cdr res)))

(declaim (ftype (function (list) boolean) any-context-item-nil))
(defun any-context-item-nil (ctx)
  (some #'(lambda (item) (equal (TaggedSExpr-expr (CtxItem-stmt item)) 'acl2s::nil)) ctx))

(declaim (ftype (function (list optional-TaggedSExpr) boolean) derived-nil-or-goal))
(defun derived-nil-or-goal (ctx goal)
  ;; TODO: if goal is not provided then just use conclusion of contract completed stmt
  (if (any-context-item-nil ctx)
      (progn (v:debug :status "derived nil in context") t)
    (unless (missingp goal)
      (let ((goal-expr (ts-expr goal)))
        (handler-case
            (when (car (find-equiv-term goal-expr
                                        (mapcar #'(lambda (item) (TaggedSExpr-expr (CtxItem-stmt item))) ctx)))
              (progn (v:debug :status "derived goal in context") t))
          (error (_) (v:debug :status "error when checking whether derived nil or goal")))))))

(declaim (ftype (function ((not TaggedSExpr)) boolean) fully-exported))
(defun fully-exported (stmt)
  (equal (exportation-simplify stmt) stmt))

(declaim (ftype (function (TaggedSExpr) boolean) check-fully-exported))
(defun check-fully-exported (exportation)
  (if (fully-exported (TaggedSExpr-expr exportation))
      t
    (error 'not-fully-exported :stmt exportation :target-id (TaggedSExpr-id exportation))))

(declaim (ftype (function ((not TaggedSExpr)) boolean) antecedents-contain-nested-conjunction?))
(defun antecedents-contain-nested-conjunction? (term)
  (match term
    ((list (is-op? implies) (list* (is-op? and) args) _)
     (some #'(lambda (x)
               (match x
                 ((list* (is-op? and) _) t)
                 (otherwise nil))) args))
    (otherwise nil)))

(defun check-distinct-lemma-names (proof-cases)
  (let ((proof-lemma-names (mapcar #'Proof-name proof-cases)))
    (multiple-value-bind
      (has-dupes? dupe-name)
      (has-duplicates? proof-lemma-names)
      (if has-dupes?
          (error 'induction-cases-duplicate-name-error
                 :name dupe-name
                 :target-id (Proof-id (car (remove-if-not #'(lambda (proof) (equal (Proof-name proof) dupe-name)) proof-cases))))
          t))))

;; TODO: unify these functions
(declaim (ftype (function (Proof) symbol) get-full-proofname))
(defun get-full-proofname (proof)
  (let ((*package* (find-package :acl2s)))
    (let ((res (read-from-string (Proof-name proof))))
      (if (numberp res)
          (intern (write-to-string res) *package*)
        res))))

(declaim (ftype (function (Proof list) symbol) get-full-proofname-in-stack))
(defun get-full-proofname-in-stack (proof proof-stack)
  (let ((prefix (loop for stacked-proof in (reverse proof-stack)
                      append `(,(Proof-name stacked-proof) "-")))
        (proof-name (get-full-proofname proof)))
    (intern (apply #'concatenate 'string (append prefix (list (string-upcase (Proof-kind proof)) (symbol-name proof-name))))
            (symbol-package proof-name))))

(declaim (ftype (function (Proof) string) get-proof-printable-name))
(defun get-proof-printable-name (proof)
  (concatenate 'string (Proof-kind proof) " " (Proof-name proof)))

(defmacro print2 (val &rest args &key &allow-other-keys)
  `(progn
     (v:debug :status "~S" ,val)
     (print::print2 ,val ,@args)))

(defmacro print2-nonl (val)
  `(progn
     (v:debug :status "~S" ,val)
     (print::print2 ,val :nl "")))

(defmacro print2-nonl-with-prefix (val prefix)
  `(progn
     (v:debug :status "~S" ,val)
     (print::print2 ,val :nl "" :prefix ,prefix)))

(defun check-valid-induction-term (proof)
  (let* ((induct-form (ProofStrategy-params (Proof-strategy proof)))
         (status :ok))
    (update-status (check-valid-acl2s-term induct-form t "the induction term"))
    (update-status (if (consp (ts-expr induct-form))
                       :ok
                     (add-message-and-error-out
                      induction-term-not-call-error
                      :target-id (TaggedSExpr-id induct-form))))
    (update-status (if (acl2s::symbol-listp (ts-expr induct-form))
                       :ok
                     (add-message-and-error-out
                      induction-term-nested-calls
                      :target-id (TaggedSExpr-id induct-form))))
    status))

(defun check-proof-struct-inductive (proof completed-proofs proof-stack &key (prefix "") (define-thm? nil))
  (let* ((name (Proof-name proof))
         (induct-form (ProofStrategy-params (Proof-strategy proof)))
         (stmt (Proof-stmt proof))
         (stmt-expr (ts-expr stmt))
         (status :ok)
         (proof-cases (Proof-cases proof))
         (extra-data nil))
    (print2-nonl-with-prefix "--- Checking that provided proof terms are OK... " prefix)
    (print-result-and-update-status (check-proof-expressions-ok proof proof-stack))
    (when (status-is-fail status)
      (print2 "Proof failed." :prefix prefix)
      (return-from check-proof-struct-inductive status))
    (print2-nonl-with-prefix "--- Checking that the induction term is OK... " prefix)
    (print-result-and-update-status (check-valid-induction-term proof))
    (when (status-is-fail status)
      (print2 "Induction term is invalid. Proof failed." :prefix prefix)
      (return-from check-proof-struct-inductive status))
    (print2-nonl-with-prefix "--- Generating induction proof obligations... " prefix)
    (let* ((logic-ind-obligations (acl2s-query `acl2s::(induction-proof-obligations
                                                        ',prover::(ts-expr stmt)
                                                        ',prover::(ts-expr induct-form)
                                                        state)))
	   (proof-obligations (print-result-and-update-status
                               (message-wrap
                                 (if (car logic-ind-obligations)
				     (error 'ind-term-error :message (cadr logic-ind-obligations) :target-id (TaggedSExpr-id induct-form))
				   (cadr logic-ind-obligations)))))
           (proof-stmts (mapcar #'ts-expr (mapcar #'Proof-stmt proof-cases)))
           (user-lemma-stmts (mapcar #'acl2s-untranslate
                                     (mapcar #'exportation-simplify
                                             proof-stmts))))
      (when (status-is-fail status)
        (print2 "Failed to generate proof obligations using your induction term. Proof failed." :prefix prefix)
        (return-from check-proof-struct-inductive :fail))
      (unless proof-obligations
        (add-message (TaggedSExpr-id induct-form)
                           "The induction term gives rise to 0 proof obligations. Ensure that you've provided a call to a recursive function."
                           :category "BAD_TERM"
                           :kind "NO_OBLIGATIONS")
        (print2 "No induction proof obligations were generated using your induction term. Proof failed." :prefix prefix)
        (return-from check-proof-struct-inductive :fail))
      (print2-nonl "--- Checking lemma bijection... ")
      (print-result-and-update-status
       (handler-case
           (prop-equiv-bijection user-lemma-stmts proof-obligations)
         (bijection-error
          (condition)
          (let* ((unused-proof-cases (mapcar #'(lambda (i) (nth i proof-cases))
                                             (tp::bijection-error/unused-f-idxs condition)))
                 (unused-proof-obligations (mapcar #'(lambda (i) (nth i proof-obligations))
                                                   (tp::bijection-error/unused-g-idxs condition))))
            ;; TODO: what order do we want to do these checks in?
            ;; i.e. what should take precedence?
            ;; TODO: maybe we want to raise different conditions in each of these cases?
            (cond ((and (endp unused-proof-cases)
                        (consp unused-proof-obligations))
                   ;; user provided too few cases
                   ;; highlight the induction term?
                   (add-message-and-error-out induction-cases-bijection-too-few
                                              :target-id (TaggedSExpr-id induct-form)
                                              :missing-obligations unused-proof-obligations))
                  ((and (consp unused-proof-cases)
                        (endp unused-proof-obligations))
                   ;; user provided too many cases
                   ;; highlight all extra ones
                   (add-message-and-error-out induction-cases-bijection-too-many
                                              :target-id (cons :each (mapcar #'Proof-id unused-proof-cases))
                                              :unused-cases unused-proof-cases))
                  ((consp unused-proof-cases)
                   ;; user provided cases that don't match up with proof obligations
                   ;; highlight all user cases that don't match up
                   (add-message-and-error-out induction-cases-bijection-unmatched
                                              :target-id (cons :each (mapcar #'Proof-id unused-proof-cases))
                                              :missing-obligations unused-proof-obligations))
                  (t ;; should never get here
                   (error "Bijection error where none was expected: ~a" condition)))))
         (:no-error (&rest vals) (declare (ignore vals)) :ok)))
      (let* ((case-results (loop for case in proof-cases collect
                                 (progn
                                   (print2 (format nil "--- Checking ~a" (get-proof-printable-name case)) :prefix prefix)
                                   (multiple-value-bind
                                     (res extra-data)
                                     (check-proof-struct case completed-proofs (cons proof proof-stack)
                                                         :prefix (concatenate 'string prefix "---")
                                                         :define-thm? nil)
                                     (print2 (format nil "--- ~a ~a"
                                                     (get-proof-printable-name case)
                                                     (case res
                                                       (:ok (green "OK"))
                                                       (:warn (yellow "Warn"))
                                                       (:fail (red "Fail"))))
                                             :prefix prefix)
                                     `(,res ,case . ,extra-data)))))
             (res (reduce-statuses (cons status (mapcar #'car case-results)))))
        (update-status res)
        (when (status-is-pass status)
          (let ((proof-stack (copy-list proof-stack))
                (contract-completion (Proof-contract-completion proof))
                (computed-exportation (if (missingp (Proof-exportation proof)) (Proof-stmt proof) (Proof-exportation proof)))
                (defthm-name (get-full-proofname proof)))
            (print2-nonl-with-prefix "--- Running proof through the proof builder... " prefix)
            (cond ((and (not (missingp contract-completion))
                        (not (equal (ts-expr contract-completion) (ts-expr computed-exportation))))
                   (update-status :warn)
                   (v:debug :status "Defining thm ~S with skip-proofs since a contract completion was provided" (get-proof-printable-name proof))
                   (print2 (format nil "~%~a provided a nontrivial contract completion" (yellow "== WARNING ==")))
                   (signal 'used-contract-completion-warning :proof proof :proof-stack proof-stack)
                   (setf extra-data
                         #'(lambda (desired-name)
                             (generate-thm-skip-proofs (or desired-name defthm-name) (ts-expr contract-completion))))
                   (when define-thm?
                     (print-result-and-update-status (define-thm-skip-proofs defthm-name (ts-expr contract-completion)))))
                  (t
                   (print-result-and-update-status
                    (let ((instructions (induction-proof-to-encapsulated-defthm (ts-expr computed-exportation) proof completed-proofs proof-stack (mapcar #'cdr case-results) define-thm?)))
                      (v:debug :status "Instructions: ~S" instructions)
                      (let ((res (acl2s-event instructions)))
                        (if (car res)
                            (error 'proof-builder-proof-fail :name defthm-name :thm-stmt stmt-expr :instructions instructions)
                          :ok))))
                   (setf extra-data #'(lambda (desired-name)
                                        (induction-proof-to-encapsulated-defthm (ts-expr computed-exportation) proof completed-proofs proof-stack (mapcar #'cdr case-results) t :proof-name desired-name)))))))
      (values status extra-data)))))

(defun check-exportation-and-completion (proof &key (prefix ""))
  (let* ((name (Proof-name proof))
         (stmt (Proof-stmt proof))
         (stmt-expr (ts-expr stmt))
         (exportation (Proof-exportation proof))
         (exportation-expr (ts-expr exportation))
         (contract-completion (Proof-contract-completion proof))
         (contract-completion-expr (ts-expr contract-completion))
         (final-sexpr-res (multiple-value-list (get-proof-final-sexpr proof)))
         (final-sexpr (first final-sexpr-res))
         (final-sexpr-source (second final-sexpr-res))
         (goal (Proof-goal proof))
         (context (Proof-ctx proof))
         (derived-context (Proof-derived-ctx proof))
         (status :ok))
    ;; check exportation
    (print2-nonl-with-prefix "--- Checking that no more exportation is possible... " prefix)
    (cond ((and (exportation-possible? stmt-expr) (not (missingp exportation)))
           (print-result-and-update-status (check-fully-exported exportation))
           (print2-nonl-with-prefix "--- Checking validity of exportation... " prefix)
           (print-result-and-update-status
            (message-wrap (check-exportation-equiv exportation-expr stmt-expr) :id (TaggedSExpr-id exportation))))
          ((exportation-possible? stmt-expr)
           (print-result-and-update-status
            (message-wrap (error 'exportation-missing-error :target-id (TaggedSExpr-id stmt)))))
          (t
           (if (or (missingp exportation) (equal stmt-expr exportation-expr))
               (print-result-and-update-status :ok)
             (print-result-and-update-status
              (message-wrap (check-exportation-equiv exportation-expr stmt-expr) :id (TaggedSExpr-id exportation))))))
    (let* ((contract-completion-expr (ts-expr final-sexpr))
           (contract-completion-id (TaggedSExpr-id final-sexpr))
           (hyps (get-hyps contract-completion-expr))
           (conc (get-conc contract-completion-expr)))
        ;; check completed's hyps sat
      (when (and (not (any-context-item-nil derived-context))
                 (acl2s::acl2s-defaults :get testing-enabled))
        (print2-nonl-with-prefix "--- Checking satisfiability of completed statement's hypotheses... " prefix)
        (print-result-and-update-status (message-wrap (check-hyps-sat hyps))))
      ;; check completed is boolean
      (print2-nonl-with-prefix "--- Checking that completed statement returns a boolean... " prefix)
      (print-result-and-update-status (handler-bind
                                          ((statement-not-boolean-ctrex-error
                                            #'(lambda (condition)
                                                (add-message contract-completion-id
                                                             (short-report condition)
                                                             :category "BAD_COMPLETION"
                                                             :kind "COMPLETION_NOT_BOOLEAN"))))
                                        (check-is-boolean hyps conc)))
      ;; check completed passes contract checking
      (print2-nonl-with-prefix "--- Checking that completed statement passes contract checking... " prefix)
      (print-result-and-update-status (check-contract contract-completion-expr))
      ;; check contract completed and exportation are equiv
      (print2-nonl-with-prefix "--- Checking that exportation and completed statements are equivalent... " prefix)
      (print-result-and-update-status
       (handler-bind
           ;; TODO: what should we do if the user provides completion but not exportation and the generated exportation is not equivalent ot the provided completion?
           ;; probably makes the most sense to show the user the generated exportation somehow?
           ;; Similarly, what if we somehow generate a completion and an exportation which are not equivalent
           ((checker-error
             #'(lambda (condition)
                 (let ((id (or (ts-id exportation) (ts-id contract-completion))))
                   (if id
                       (add-condition-message condition :id id :category "EXPORTED_COMPLETED_DIFFERENT")
                       (add-message (Proof-id proof)
                                        "Automatically generated exportation and completion are not equivalent - internal error has occurred."
                                        :kind "INTERNAL_CHECKER_ERROR")))

                 (signal condition))))
         (check-completion-equiv stmt exportation contract-completion)))
      (unless (missingp goal)
        (print2-nonl-with-prefix "--- Checking that the goal and completed statement match... " prefix)
        (print-result-and-update-status (check-goal-equiv-completed-conc goal conc)))
      ;; check if nested conjunction in 
      (when (antecedents-contain-nested-conjunction? contract-completion-expr)
        (let ((msg-text (format nil "At least one of the hypotheses of the provided ~a is a conjunction. This may cause issues with proof-builder instruction generation. If you run into an issue here, you should eliminate the nested conjunction during the exportation step." final-sexpr-source)))
          (add-message contract-completion-id
                       msg-text
                       :severity :warn)
          (print2 msg-text)
          (update-status :warn)))
      )
    status))

(declaim (ftype (function (optional-TaggedSExpr) boolean) is-valid-acl2s-term?))
(defun is-valid-acl2s-term? (expr)
  (or (missingp expr)
      (is-acl2s-term (TaggedSExpr-expr expr))))

(declaim (ftype (function (optional-TaggedSExpr boolean string) Status) check-valid-acl2s-term))
(defun check-valid-acl2s-term (expr required source)
  (cond ((and required (missingp expr))
         (add-message -1
                            (format nil "You did not provide a term for ~a, but one is required!" source)
                            :category "BAD_TERM"
                            :kind "MISSING")
         (error 'missing-term-error :source source))
        ((is-valid-acl2s-term? expr) :ok)
        (t
         (let ((extra-error-info (is-acl2s-term-capture-error (TaggedSExpr-expr expr))))
           (add-message (TaggedSExpr-id expr)
                        (format nil "The term you provided for ~a is not a valid ACL2s term.~%The following might help: ~a" source extra-error-info)
                        :category "BAD_TERM"
                        :kind "INVALID")
           (error 'invalid-term-error :sexpr expr :source source :extra-info extra-error-info)))))

(defun check-steps-are-valid-terms (steps)
  ;; TODO: ideally we'd check all steps and show any errors, as
  ;; opposed to stopping after the first error like we do below.
  (let ((status :ok))
    (update-status (check-valid-acl2s-term (ProofStep-before (car steps)) t "a proof step"))
    (loop for step in steps
          do (update-status (check-valid-acl2s-term (ProofStep-after step) t "a proof step")))
    status))

(defun check-context-items-are-valid-terms (ctx kind)
  (let ((status :ok))
    (loop for ctx-item in ctx
          do (update-status (check-valid-acl2s-term (CtxItem-stmt ctx-item) t (format nil "~a: ~a" kind ctx-item))))
    status))

(defun check-proof-expressions-ok (proof proof-stack)
  (let ((stmt (Proof-stmt proof))
        (exportation (Proof-exportation proof))
        (contract-completion (Proof-contract-completion proof))
        (goal (Proof-goal proof))
        (steps (Proof-steps proof))
        (context (get-full-context (Proof-ctx proof) proof-stack))
        (derived-context (Proof-derived-ctx proof))
        (cases (Proof-cases proof))
        (status :ok))
    (update-status (check-valid-acl2s-term stmt t "the proof statement"))
    (update-status (check-valid-acl2s-term exportation nil "the exportation"))
    (update-status (check-valid-acl2s-term contract-completion nil "the contract completion"))
    (update-status (check-context-items-are-valid-terms context "context item"))
    (update-status (check-context-items-are-valid-terms derived-context "derived context item"))
    (update-status (check-valid-acl2s-term goal nil "the goal"))
    (when steps
      (update-status (check-steps-are-valid-terms steps)))
    (loop for case in cases
          do (update-status (check-valid-acl2s-term (Proof-stmt case) t
                                                    (format nil "the proof statement for ~a" (Proof-name case)))))
    ;; TODO add more checks
    status))

(defun check-context-order (contract-completion context)
  (v:debug :status "~S" context)
  ;; TODO give more useful error when lengths of lists are different
  (loop for cc-hyp in (get-hyps (ts-expr contract-completion))
        for ctx-item in context
        do (progn
             (v:debug :status "~S~%~S" cc-hyp (ts-expr (CtxItem-stmt ctx-item)))
             (when (and (not (equal cc-hyp (ts-expr (CtxItem-stmt ctx-item))))
                        ;; The below check helps avoid some false positives with !=
                        ;; not sure if that's from get-hyps or not.
                        (not (equal (tp::normalize-expr cc-hyp)
                                    (tp::normalize-expr (ts-expr (CtxItem-stmt ctx-item))))))
               (error 'ctx-wrong-order-error
                      :ctx-item ctx-item
                      :should-be-hyp cc-hyp)))))

(defun check-context (proof context)
  (let ((final-sexp (get-proof-final-sexpr proof)))
;;    (handler-case
        (check-context-sane final-sexp context (Proof-goal proof))
;;      (missing-goal-error (_)
;;                          (error 'missing-goal-error :target-id (Proof-id proof))))
    (check-context-order final-sexp context)
    (check-context-numbering context)
    (check-context-numbering (Proof-derived-ctx proof) :name-prefix "D")))

(defun check-proof-struct-normal (proof completed-proofs proof-stack &key (prefix "") (define-thm? t))
  (let ((name (Proof-name proof))
        (stmt (Proof-stmt proof))
        (exportation (Proof-exportation proof))
        (contract-completion (Proof-contract-completion proof))
        (goal (Proof-goal proof))
        (steps (Proof-steps proof))
        (context (get-full-context (Proof-ctx proof) proof-stack))
        (derived-context (Proof-derived-ctx proof))
        (status :ok)
        ;; this will be returned as a second value
        (extra-data nil))
    (when (and (null steps) (null context) (null derived-context))
      ;; proof's probably not attempted
      (add-message (Proof-id proof) "Skipped because no context, derived context, or proof were provided.")
      (print2 "Skipping because no context, derived context, or proof were provided.")
      (return-from check-proof-struct-normal :fail))
    (print2-nonl-with-prefix "--- Checking that provided proof terms are OK... " prefix)
    (print-result-and-update-status (check-proof-expressions-ok proof proof-stack))
    (when (status-is-fail status)
      (print2 "Proof failed." :prefix prefix)
      (return-from check-proof-struct-normal status))
    (update-status (check-exportation-and-completion proof :prefix prefix))
    (unless (any-context-item-nil derived-context)
      (print2-nonl-with-prefix "--- Checking that context makes sense... " prefix)
      (print-result-and-update-status (message-wrap (check-context proof context))))
    (calculate-context-type-predicates context)
    (print2-nonl-with-prefix "--- Checking derived context... " prefix)
    (let ((new-ctx (print-result-and-update-status
                    (handler-bind
                        ((contract-completion-test-error
                          (msg-and-error :category "DERIVED_CTX_ERROR"))
                         (contract-completion-proof-error
                          (msg-and-error :category "DERIVED_CTX_ERROR"))
                         (checker-error (msg-and-error)))
                      (check-derived-context-all derived-context context completed-proofs))
                    :fail-val context)))
      (unless (derived-nil-or-goal derived-context goal)
        (print2-nonl-with-prefix "--- Checking steps... " prefix)
        (cond ((endp steps)
               (print2 (red "FAIL: no steps provided!"))
               (update-status :fail))
              (t
               (print-result-and-update-status
                (message-wrap (check-proof-steps steps new-ctx completed-proofs)))
               (print2-nonl-with-prefix "--- Checking steps imply goal... " prefix)
               (print-result-and-update-status
                (message-wrap (check-steps-imply-goal steps new-ctx goal))))))
      (when (status-is-pass status)
        (print2-nonl-with-prefix "--- Running proof through the proof builder... " prefix)
        (let ((proof-stack (copy-list proof-stack))
              (computed-exportation (if (missingp exportation) stmt exportation))
              (defthm-name (get-full-proofname proof)))
          (cond ((and (not (missingp contract-completion))
                      (not (equal (ts-expr contract-completion) (ts-expr computed-exportation))))
                 (update-status :warn)
                 (v:debug :status "Defining thm ~S with skip-proofs since a contract completion was provided" (get-proof-printable-name proof))
                 (print2 (format nil "~%~a provided a nontrivial contract completion" (yellow "== WARNING ==")))
                 (signal 'used-contract-completion-warning :proof proof :proof-stack proof-stack)
                 (setf extra-data
                       #'(lambda (desired-name)
                           (generate-thm-skip-proofs (or desired-name defthm-name) (ts-expr contract-completion))))
                 (when define-thm?
                   (print-result-and-update-status (define-thm-skip-proofs defthm-name (ts-expr contract-completion)))))
                (t
                 (calculate-context-type-predicates new-ctx)
                 (print-result-and-update-status
                  (define-thm-proof-builder (ts-expr computed-exportation)
                    proof new-ctx completed-proofs proof-stack define-thm?))
                 (setf extra-data
                       #'(lambda (desired-name)
                           (generate-thm-proof-builder (or desired-name defthm-name)
                                                       (ts-expr computed-exportation)
                                                       (proof-to-proof-builder-instructions proof new-ctx completed-proofs proof-stack)
                                                       t))))))))
    (values status extra-data)))

(defun check-conditions-boolean (conditions)
  (if (endp conditions)
      nil
    ;; TODO Are there any cases we want to consider where
    ;; minimal theory + tau + booleanp-compound-recognizer is insufficient?
    (progn (handler-case (test-thm-min
                          `(acl2s::booleanp ,(car conditions))
                          :rules 'acl2s::((:compound-recognizer booleanp-compound-recognizer)))
             (test-found-ctrex-error (condition)
                                     (error "Counterexample found when testing that case is boolean:~%  Case: ~a~%  Counterexamples: ~a"
                                            (car conditions)
                                            (test-found-ctrex-error/cxs condition)))
             (min-thm-failed-error (_) (error "Failed to prove that case is boolean:~%  Case: ~a"
                                             (car conditions))))
           (check-conditions-boolean (cdr conditions)))))

(defun check-conditions-exhaustive (conditions)
  (handler-case (test-thm-min `(acl2s::or ,@conditions))
    (test-found-ctrex-error (condition)
                            (error "Counterexample found when testing that cases are exhaustive:~%  Cases: ~a~%  Counterexamples: ~a"
                                   conditions
                                   (test-found-ctrex-error/cxs condition)))
    (min-thm-failed-error (_)
                          (error "Failed to prove that cases are exhaustive:~%  Cases: ~a"
                                 conditions))))

(defun check-lemmas-prove-cases (cases stmt used completed-proofs)
  (if (endp cases)
      nil
    (let* ((lemma-name (first (car cases)))
           (case (second (car cases)))
           ;; Note (cdr nil) = nil
           (lemma (find lemma-name (passing-completed-proofs completed-proofs)
                        :key #'structs::Proof-name
                        :test #'string-equal))) ;; Case-insensitive string equality
      (if (not lemma)
          (progn (break) (error "Unknown lemma ~a" lemma-name))
        (let* ((lemma-stmt (ts-expr (Proof-contract-completion lemma)))
               (query `acl2s::(implies ,prover::lemma-stmt
                                       (implies (and ,@prover::used ,prover::case)
                                                ,prover::stmt))))
          (handler-case (test-thm-min query)
            (test-found-ctrex-error (condition)
                                    (error "Counterexample found when testing that lemma proves theorem under condition:~%  Case: ~a~%  Lemma: ~a~% Counterexamples: ~a"
                                           case lemma-name
                                           (test-found-ctrex-error/cxs condition)))
            (min-thm-failed-error (_)
                                  (error "Failed to prove that lemma proves theorem under condition:~% Case: ~a~% Lemma ~a: ~a~%"
                                         case lemma-name lemma-stmt)))
          (check-lemmas-prove-cases (cdr cases) stmt (cons `(acl2s::not ,case) used) completed-proofs))))))

(defun check-case-analysis-proof (proof cases completed-proofs proof-stack &key (prefix "") (define-thm? t))
  (let* ((name (Proof-name proof))
         (fullname (get-full-proofname proof))
         (contract-completion (Proof-contract-completion proof))
         (conditions (mapcar #'cadr cases))
         (status :ok))
    (print2-nonl-with-prefix "--- Checking that case statement looks OK..." prefix)
    (print2 "")
    (print-result-and-update-status (check-exportation-and-completion proof :prefix (concatenate 'string prefix "--- ")))
    (print2-nonl-with-prefix "--- Checking that cases are booleans... " prefix)
    (print-result-and-update-status (check-conditions-boolean conditions))
    (print2-nonl-with-prefix "--- Checking that cases are exhaustive... " prefix)
    (print-result-and-update-status (check-conditions-exhaustive conditions))
    (print2-nonl-with-prefix "--- Checking that lemmas prove cases... " prefix)
    (print-result-and-update-status (check-lemmas-prove-cases cases (ts-expr contract-completion) nil completed-proofs))
    (if (and (or (equal status :ok) (equal status :warn)) define-thm?)
        (define-thm-skip-proofs fullname (ts-expr contract-completion))
      nil)
    status))


;; TERMINATION PROOF FUNCTIONS

(defun check-functions-not-defined (names defined-names)
  (if (endp names)
      nil
    (if (or (member (car names) defined-names)
            (acl2::definedp (car names) (acl2::w acl2::state)))
        (error "Function is already defined: ~a" (car names))
      (check-functions-not-defined (cdr names) (cons (car names) defined-names)))))

;; defs is guaranteed by parsing to be a true list of lists, each containing
;; 'acl2s::defunc or 'acl2s::definec as their first element
;; Check:
;;   - Function names are distinct
;;   - Function names are not already defined
;;   - No function name is not fn or measure
;;   Define functions
;;   - fn and measure are defined in the current world
;;   Undo the function definition (but keep the measure)
;; Returns a list of:
;;   - The function definition
;;   - The measure definition
;;   - The function formals
;;   - The function guard
;;   - The function recursive calls
(defun check-function-defs (fn measure defs)
  (let ((def-names (loop for def in defs collect
                         (if (and (>= (length def) 2) (symbolp (second def)))
                             (second def)
                           (error "Malformed function definition:~%~a" def)))))
    (check-functions-not-defined def-names nil)
    (loop for name in def-names do
          (if (not (or (equal name fn) (equal name measure)))
              (error "Expected definition for ~a or ~a but got ~a" fn measure name)))
    (let ((fn-def (find-if (lambda (def) (equal (second def) fn)) defs))
          (measure-def (find-if (lambda (def) (equal (second def) measure)) defs)))
                                        ; Submit the measure function if defined
      (if measure-def (acl2s-event measure-def))
                                        ; Set a checkpoint, then submit the function with skip-proofs
      (acl2s-event 'acl2s::(defun TERMINATION-DEF-START () t))
      (if fn-def (acl2s-event `(acl2::skip-proofs ,fn-def)))
      (let ((state (acl2::w acl2::state)))
                                        ; Check that both functions went through (or were already defined)
        (if (not (acl2::definedp measure state)) (error "Measure function is not defined: ~a" measure))
        (if (not (acl2::definedp fn state)) (error "Function is not defined: ~a" fn))
                                        ; Get the info we need out of the function, then undo and stub it
        (let ((formals (acl2::formals fn state))
              (guard (acl2::uguard fn state))
              (recursive-calls (acl2::recursive-calls fn state)))
          (acl2::ld 'acl2s::(:ubt TERMINATION-DEF-START))
          (acl2s-event 'acl2s::(defun TERMINATION-DEF-START () t))
          (if fn-def
              (acl2s-event `acl2s::(defstub ,prover::fn
                                     ,prover::(loop for formal in formals collect '*) => *)))
          (list fn-def measure-def formals guard recursive-calls))))))

;; Undo the stubbed function, then submit the actual function using the measure
(defun resubmit-def (fn measure fn-def measure-def formals)
  (acl2s-event (inject-declare fn-def
                               `acl2s::(declare (xargs :termination-method :measure
                                                       :well-founded-relation n<
                                                       :measure (,prover::measure ,@prover::formals)))))
  (if (not (acl2::definedp fn (acl2::w acl2::state)))
      (signal 'prover-warning :msg (format nil "Couldn't admit ~a using ~a as a measure" fn measure))))

(defun check-measure-arity (measure fn fn-arity)
  (let* ((state (acl2::w acl2::state))
         (measure-arity (acl2::arity measure state)))
    (if (not (equal fn-arity measure-arity))
        (error "Measure function ~a does not have the same arity as ~a: expected ~d but got ~d"
               (symbol-name measure) (symbol-name fn) fn-arity measure-arity))))

;; TODO This assumes the same argument names in both functions. We could get around this if we needed to
(defun check-measure-guard (measure fn fn-guard)
  (let* ((state (acl2::w acl2::state))
         (measure-guard (acl2::uguard measure state))
         (query `(acl2::equal ,fn-guard ,measure-guard)))
    (handler-case (test-thm-min query)
      (test-found-ctrex-error
       (condition)
       (error "Counterexample found when testing input contract for measure function ~a matches ~a~%  ~a input contract: ~a~%  ~a input contract: ~a~%  Counterexamples: ~a"
              (symbol-name measure) (symbol-name fn)
              (symbol-name fn) fn-guard
              (symbol-name measure) measure-guard
              (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error (_)
       (error "Couldn't prove input contract for measure function ~S matches ~S~%  ~S input contract: ~a~%  ~a input contract: ~a"
              (symbol-name measure) (symbol-name fn)
              (symbol-name fn) fn-guard
              (symbol-name measure) measure-guard)))))

;; TODO This only checks whether ACL2 can prove measure returns a nat. Can we say anything about the output contract?
(defun check-measure-output-contract (measure)
  (let* ((state (acl2::w acl2::state))
         (measure-guard (acl2::uguard measure state))
         (params (acl2::formals measure state))
         (query `(acl2::implies ,measure-guard
                                (acl2::natp (,measure ,@params)))))
    (handler-case (test-thm-min-with-contracts query)
      (test-found-ctrex-error
       (condition)
       (error "Counterexample found when testing ~S returns a natural:~%  ~a"
              (symbol-name measure) (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error
       (_)
       (error "Couldn't prove that ~S returns a natural" (symbol-name measure))))))

                                        ; TODO This is a weak check:
                                        ; 1. The measure function can call other recursive functions
                                        ;    - Anything we can do about this? Maybe whitelist functions they're allowed to call...
                                        ; 2. Recursive measure functions should be allowed, if they can be proved terminating
                                        ;    - If a proof of termination of measure has been provided, allow this
(defun check-measure-non-recursive (measure)
  (let ((state (acl2::w acl2::state)))
    (if (acl2::recursivep measure nil state)
        (error "Measure function ~S is recursive" (symbol-name measure)))))

(defun check-measure-thm (measure proof label rcall)
  (let* ((state (acl2::w acl2::state))
         (params (acl2::formals measure state))
         (conditions (second rcall))
         (recursive-args (cdr (third rcall)))
         (measure-thm `(acl2::implies (acl2::and ,@conditions)
                                      (acl2::< (,measure ,@recursive-args) (,measure ,@params))))
                                        ; TODO Should we be more stringent about the format of their measure theorem?
         (query `(acl2::iff ,measure-thm ,(Proof-stmt proof))))
    (handler-case (test-thm-min query)
                                        ; TODO could have more descriptive error messages
      (test-found-ctrex-error
       (condition)
       (error "Counterexample found when testing correctness of proof obligation for recursive call ~a:~%  Counterexamples: ~a"
              label (test-found-ctrex-error/cxs condition)))
      (min-thm-failed-error
       (_)
       (error "Couldn't prove correctness of proof obligation for recursive call ~a"
              label)))))

                                        ; TODO This currently requires that the recursive calls be written in the order
                                        ; in which recursive-calls returns them (i.e. the order they appear in the
                                        ; function definition, left to right, outside in) and just errors if they're in
                                        ; the wrong order.
(defun check-recursive-calls (recursive-calls measure subproofs)
  (if (not (equal (length subproofs) (length recursive-calls)))
      (error "Wrong number of recursive cases: expected ~D, got ~D" (length recursive-calls) (length subproofs))
    (loop for labeled-subproof in subproofs
          for rcall in recursive-calls do
          (let ((label (car labeled-subproof))
                (subproof (cdr labeled-subproof)))
            (check-measure-thm measure subproof label rcall)))))

(defun prove-recursive-call (label subproof completed-proofs proof-stack &key (prefix ""))
  (print2 (format nil "Recursive call ~a" label) :prefix prefix)
  (let ((res (check-proof-struct subproof completed-proofs proof-stack
                                 :prefix (concatenate 'string prefix "  ")
                                 :define-thm? nil)))
    (cond ((equal res :ok)
           (print2 (format nil "Recursive call ~a ~a" label (green "OK")) :prefix prefix))
          ((equal res :warn)
           (print2 (format nil "Recursive call ~a ~a" label (yellow "WARN")) :prefix prefix))
          (t
           (print2 (red (format nil "*** Recursive call ~a failed ***" label)) :prefix prefix)))
    res))

;; TODO This is very reliant on the syntax and will fail if the function
;; definition already contains a declare. Is there a more robust way of
;; doing this?
(defun inject-declare (def declare-form)
  (if (endp (cdr def))
      (cons declare-form def)
    (cons (car def) (inject-declare (cdr def) declare-form))))

(defun check-termination-proof (proof fn measure defs subproofs completed-proofs proof-stack &key (prefix ""))
  (let ((status :ok))
    (progn
      (print2-nonl-with-prefix "--- Checking that functions are properly defined... " prefix)
      (let* ((res (print-result-and-update-status (check-function-defs fn measure defs)))
             (fn-def (first res))
             (measure-def (second res))
             (fn-formals (third res))
             (fn-guard (fourth res))
             (fn-recursive-calls (fifth res)))
        (print2-nonl-with-prefix "--- Checking that function and measure function have the same arity... " prefix)
        (print-result-and-update-status (check-measure-arity measure fn (length fn-formals)))
        (print2-nonl-with-prefix "--- Checking that function and measure function have the same input contract... " prefix)
        (print-result-and-update-status (check-measure-guard measure fn fn-guard))
        (print2-nonl-with-prefix "--- Checking that measure function returns a natural... " prefix)
        (print-result-and-update-status (check-measure-output-contract measure))
        (print2-nonl-with-prefix "--- Checking that measure function is non-recursive... " prefix)
        (print-result-and-update-status (check-measure-non-recursive measure))
        (print2-nonl-with-prefix "--- Checking that recursive cases satisfy proof obligation... " prefix)
        (print-result-and-update-status (check-recursive-calls fn-recursive-calls measure subproofs))
        (loop for labeled-subproof in subproofs do
              (let* ((label (car labeled-subproof))
                     (subproof (cdr labeled-subproof))
                     ;; TODO: confirm that we want to add the current proof to the proof stack
                     (res (prove-recursive-call label subproof completed-proofs (cons proof proof-stack) :prefix prefix)))
                (setf status (merge-statuses res status))))
        (acl2::ld 'acl2s::(:ubt TERMINATION-DEF-START))
        (if (and (or (equal status :ok) (equal status :warn))
                 fn-def)
            (progn (print2-nonl-with-prefix "--- Cleaning up and running sanity checks... " prefix)
                   (print-result-and-update-status (resubmit-def fn measure fn-def measure-def fn-formals))))
        status))))

(defun check-proof-struct (proof completed-proofs proof-stack &key (prefix "") (define-thm? t))
  (v:debug :status "Checking proof ~S" (Proof-name proof))
  (setq *CURRENT-PROOF* proof)
  (let* ((strat (Proof-strategy proof))
         (strat-kind (ProofStrategy-kind strat))
         (strat-params (ProofStrategy-params strat)))
    (match strat-kind
           (:equational-reasoning (check-proof-struct-normal proof completed-proofs proof-stack :prefix prefix :define-thm? define-thm?))
           (:case-analysis (check-case-analysis-proof proof strat-params completed-proofs proof-stack :prefix prefix :define-thm? define-thm?))
           (:decomposition (error "Decomposition proof strategy not yet implemented"))
           (:induction (check-proof-struct-inductive proof completed-proofs proof-stack :prefix prefix :define-thm? define-thm?))
           (:induction-case (check-proof-struct-normal proof completed-proofs proof-stack :prefix prefix :define-thm? nil))
           (:termination
            (destructuring-bind
                (fn measure defs subproofs)
                strat-params
              (check-termination-proof proof fn measure defs subproofs completed-proofs proof-stack :prefix prefix)))
           (otherwise
            (add-message (ProofStrategy-id strat) "Unknown proof strategy" :proof (Proof-name proof))
            (print2 (format nil "~S" strat))
            (error "Unknown proof strategy ~S" strat)))))

(defmacro string-is-ctx-item-name (val)
  `(case
     (elt ,val 0)
     ((#\C #\c) t)
     (otherwise nil)))

(defmacro string-is-derived-ctx-item-name (val)
  `(case
     (elt ,val 0)
     ((#\D #\d) t)
     (otherwise nil)))

(defun step-to-proof-builder-instructions (step step-num context completed-proofs &key (prefix ""))
  (let* ((rel (get-relation-function (ProofStep-rel step)))
         (before (ts-expr (ProofStep-before step)))
         (after (ts-expr (ProofStep-after step)))
         (hints (ProofStep-hints step))
         (hint-lists (mapcar (lambda (hint)
                               (hint-to-acl2s hint context completed-proofs)) hints))
         (hyps (append-all (mapcar #'car hint-lists)))
         (rules (append-all (mapcar #'second hint-lists)))
         (uses (append-all (mapcar #'third hint-lists)))
         (predicate-context-bodies (get-context-bodies (remove-if-not #'CtxItem-type-predicatep context)))
         (contracts (rguard-obligations `acl2s::(implies (and ,@prover::predicate-context-bodies ,@prover::hyps)
                                                         (,prover::rel ,prover::before ,prover::after))))
         (context-bodies (get-context-bodies context))
         (num-regular-ctx-items (loop for ctx-item in context
                                      count (string-is-ctx-item-name (symbol-name (CtxItem-name ctx-item)))))
         (num-derived-ctx-items (loop for ctx-item in context
                                      count (string-is-derived-ctx-item-name (symbol-name (CtxItem-name ctx-item))))))
    `(;; manually prove this
      (:claim-simple (,rel ,before ,after)
                     :hints (("Goal" :instructions
                              (
                               :pro-or-skip
                               ;; contract complete
                               ;; try to prove this automatically.
                               ,@(when (consp contracts)
                                   `((:claim (acl2s::and ,@contracts) :do-not-flatten t)))
                               ;; prove step holds
                               ;; TODO
                               ,@(hints-to-proof-builder-instructions hints context completed-proofs
                                                                      ;; we want to retain the contract completion hyp we just added with the above claim
                                                                      :hyps-to-retain (when (consp contracts)
                                                                                        ;; why this math?
                                                                                        ;; we know we have a hyp for each context item
                                                                                        ;; we also have a hyp for each step we've completed to this point.
                                                                                        ;; so, the contract claim will be the next hyp after all of the above.
                                                                                        (list (+ 1 num-regular-ctx-items num-derived-ctx-items step-num))))
                               )))))))

(defun derived-ctx-to-proof-builder-instructions (ctx-item dctx-num context completed-proofs &key (prefix ""))
  (let* ((stmt (ts-expr (CtxItem-stmt ctx-item)))
         (hints (CtxItem-hints ctx-item))
         (hint-lists (mapcar (lambda (hint)
                               (hint-to-acl2s hint context completed-proofs)) hints))
         (hyps (append-all (mapcar #'car hint-lists)))
         (rules (append-all (mapcar #'second hint-lists)))
         (uses (append-all (mapcar #'third hint-lists)))
         (contracts (rguard-obligations `acl2s::(implies (and ,@prover::hyps)
                                                         (== ,prover::stmt t))))
         (context-bodies (get-context-bodies context))
         (num-regular-ctx-items (loop for ctx-item in context
                                      count (string-is-ctx-item-name (symbol-name (CtxItem-name ctx-item))))))
    `(;; manually prove this
      (:claim-simple ,stmt
                     :do-not-flatten t
                     :hints (("Goal" :instructions
                              (
                               :pro-or-skip
                               ;; contract complete
                               ;; try to prove this automatically.
                               ,@(when (consp contracts)
                                   `((:claim (acl2s::and ,@contracts) :do-not-flatten t)))
                               ;; prove ctxitem holds
                               ;; TODO
                               ,@(hints-to-proof-builder-instructions
                                  hints context completed-proofs
                                  ;; we want to retain the contract completion hyp we just added with the above claim
                                  ;; we also want to retain the
                                  :hyps-to-retain (when (consp contracts)
                                                    ;; why this math?
                                                    ;; we know we have a hyp for each context item
                                                    ;; we also have a hyp for each derived context item we've added at this point.
                                                    ;; so, the contract claim will be the next hyp after all of the above.
                                                    (list (+ 1 num-regular-ctx-items dctx-num)))
                                  :only-retain-prior-to (ctxitem-name-to-hyp-id (CtxItem-name ctx-item) num-regular-ctx-items))
                               )))))))

(declaim (ftype (function (symbol number) number) ctxitem-name-to-hyp-id))
(defun ctxitem-name-to-hyp-id (ctx-item-name num-regular-ctx-items)
  (let ((name-str (symbol-name ctx-item-name)))
    (+ (parse-integer name-str :start 1)
       (if (string-is-ctx-item-name name-str)
           0
         num-regular-ctx-items))))

(declaim (ftype (function (list list CompletedProofData &key (:prove-command t) (:hyps-to-retain list) (:only-retain-prior-to number)) list) hints-to-proof-builder-instructions))
(defun hints-to-proof-builder-instructions (hints context completed-proofs &key (prove-command :bash) (hyps-to-retain) (only-retain-prior-to))
  (let* ((hint-lists (mapcar (lambda (hint)
                               (hint-to-acl2s hint context completed-proofs :handle-ctx-hints? nil)) hints))
         (hyps (append-all (mapcar #'car hint-lists)))
         (rules (append-all (mapcar #'second hint-lists)))
         (uses (append-all (mapcar #'third hint-lists)))
         (predicate-ctx-items (remove-if-not #'CtxItem-type-predicatep context))
         (num-regular-ctx-items (loop for ctx-item in context
                                      count (string-is-ctx-item-name (symbol-name (CtxItem-name ctx-item)))))
         (num-derived-ctx-items (loop for ctx-item in context
                                      count (string-is-derived-ctx-item-name (symbol-name (CtxItem-name ctx-item)))))
         (predicate-hyps-to-retain (loop for predicate-ctx-item in predicate-ctx-items
                                         when (or (not only-retain-prior-to)
                                                  (< (ctxitem-name-to-hyp-id (CtxItem-name predicate-ctx-item) num-regular-ctx-items)
                                                     only-retain-prior-to))
                                         collect (ctxitem-name-to-hyp-id (CtxItem-name predicate-ctx-item) num-regular-ctx-items)))
         ;; reminder: hypothesis numbers are 1-indexed
         (hint-hyps-to-retain (loop for hint in hints
                                    for hint-expr = (ts-expr hint)
                                    ;; for each of the context item hints
                                    when (and (consp hint-expr) (equal (car hint-expr) :context))
                                    collect
                                    (ctxitem-name-to-hyp-id (second hint-expr) num-regular-ctx-items)))
         (all-hyps-to-retain (append hyps-to-retain hint-hyps-to-retain predicate-hyps-to-retain)))
    `(
      ;; drop the hyps that we didn't have in hints other than those
      ;; we've been told to retain by the caller
      ;; we need to use retain-or-skip and drop-or-skip because the regular retain and drop cause a soft error
      ;; if you retain all of the hyps or if you try to drop and there are no hyps.
      ,(if (consp all-hyps-to-retain)
           `(:retain-or-skip ,@(remove-duplicates all-hyps-to-retain))
         ':drop-or-skip)
      (:in-theory acl2::(union-theories
                         (theory 'acl2s::contract-theory)
                         '(,@prover::rules)))
      ;; add any theorem uses we have
      ,@(loop for use in uses
              ;; lop off the `:instance` at the beginning
              collect `(:instantiate ,@(cdr use)))
      (:finish ,prove-command)
      )))

(defun proof-to-proof-builder-instructions (proof context completed-proofs proof-stack)
  (assert (equal (ProofStrategy-kind (Proof-strategy proof))
                 :equational-reasoning))
  (let* ((derived-ctx-items (Proof-derived-ctx proof))
         ;; generate instructions for the derived context items
         (derived-ctx-instructions
          (loop for dctx-item in derived-ctx-items
                for i below (length derived-ctx-items)
                append (derived-ctx-to-proof-builder-instructions dctx-item i context completed-proofs)))
         ;; generate both the instructions to introduce the step and the instructions
         ;; to prove the step's goal
         (step-instructions
          (loop for step in (Proof-steps proof)
                for i below (length (Proof-steps proof))
                append (step-to-proof-builder-instructions step i context completed-proofs))))
    `(:pro-or-skip
      ,@derived-ctx-instructions
      ,@step-instructions
      :demote
      ;; May need to repeat if any backchaining occurs
      (:finish (:repeat-until-done (:split-in-theory acl2s::min-executable-theory))))))

(declaim (ftype (function (symbol) symbol) calculate-exportation-proof-name))
(defun calculate-exportation-proof-name (proof-name)
  (intern (concatenate 'string (symbol-name proof-name) "-EXPORTATION") (symbol-package proof-name)))

(defun induction-proof-to-encapsulated-defthm (stmt proof completed-proofs proof-stack subproof-data define-thm? &key (proof-name (get-full-proofname proof)) (exportation-proof-name (calculate-exportation-proof-name proof-name)))
  (let* ((induct-form (ts-expr (ProofStrategy-params (Proof-strategy proof))))
         ;;(stmt (ts-expr (Proof-stmt proof)))
         (proof-cases (Proof-cases proof))
         (proof-stmts (mapcar #'ts-expr (mapcar #'Proof-stmt proof-cases)))
         (user-lemma-stmts
          (loop for proof-stmt in proof-stmts
                collect (acl2s-untranslate (cons 'and (get-hyps (exportation-simplify proof-stmt))))))
         (ind-obs-with-names (get-induction-obligations stmt induct-form))
         ;; this will compute a list of pairs where the first element
         ;; is the index of a proof that the user wrote and the second
         ;; is the index of a generated induction obligation
         (ind-obs-mapping-idxs
          (multiple-value-bind (bij idxs)
            (handler-case (prop-equiv-bijection
                           user-lemma-stmts
                           (loop for elt in ind-obs-with-names
                                 collect (cons 'and (cddr elt))))
              (bijection-error (condition)
                               (let ((unused-proof-cases
                                      (mapcar #'(lambda (i) (nth i proof-cases))
                                              (tp::bijection-error/unused-f-idxs condition)))
                                     (unused-proof-obligations
                                      (mapcar #'(lambda (i) (nth i ind-obs-with-names))
                                              (tp::bijection-error/unused-g-idxs condition))))
                                 (if
                                     ;; user provided too many cases but all obligations are matched
                                     (and (consp unused-proof-cases)
                                          (endp unused-proof-obligations))
                                     (values nil (tp::bijection-error/partial-bijection-idxs condition))
                                   (error 'proof-builder-induction-proof-bijection-fail :proof proof :bij-cond condition)))))
            (declare (ignore bij))
            idxs))
         ;; Now we turn the above pairs of indices into mappings from
         ;; proof name to (<proof case> <proof conc> . <proof hyps>)
         (ind-obs-mapping
          (let ((indexed-ind-obs-with-names (tp::make-index-alist ind-obs-with-names))
                (indexed-proof-cases (tp::make-index-alist proof-cases)))
            (loop for (proof-case-idx . ind-obs-idx) in ind-obs-mapping-idxs
                  collect (cons (car (cdr (assoc ind-obs-idx indexed-ind-obs-with-names)))
                                (cons (cdr (assoc proof-case-idx indexed-proof-cases))
                                      (cdr (cdr (assoc ind-obs-idx indexed-ind-obs-with-names))))))))
         (instructions `(:pro-or-skip
                         (:induct ,induct-form)
                         ,@(loop for ind-obs-goal-name in (mapcar #'car ind-obs-mapping)
                                 for ind-obs-proof = (cadr (assoc ind-obs-goal-name ind-obs-mapping))
                                 for ind-obs-generated-hyps = (cdddr (assoc ind-obs-goal-name ind-obs-mapping))
                                 for ind-obs-generated-conc = (caddr (assoc ind-obs-goal-name ind-obs-mapping))
                                 append `((:cg-or-skip ,ind-obs-goal-name)
                                          (:finish
                                           :demote ;; TODO demote-or-skip
                                           ,@(when (and (not (missingp (Proof-exportation ind-obs-proof)))
                                                        (not (equal (ts-expr (Proof-exportation ind-obs-proof))
                                                                    (ts-expr (Proof-stmt ind-obs-proof)))))
                                               `(;; TODO enable the appropriate equivalence thm that we previously generated
                                                 ;; Replace the statement we're trying to prove with the exported version,
                                                 ;; since that's the one that was proved above.
                                                 (:=
                                                  ;;,(if ind-obs-generated-hyps
                                                  ;;     `(implies (and ,@ind-obs-generated-hyps)
                                                  ;;               ,ind-obs-generated-conc)
                                                  ;;   ind-obs-generated-conc)
                                                  ;;,(ts-expr (Proof-stmt ind-obs-proof))
                                                  ,(ts-expr (Proof-exportation ind-obs-proof))
                                                  ;; Shouldn't need to provide any hints, typically just prop logic.
                                                  ;; :hints (("Goal" :by ,(calculate-exportation-proof-name (get-full-proofname-in-stack ind-obs-proof (cons proof proof-stack))))))))
                                                  )))
                                           (:by ,(get-full-proofname-in-stack ind-obs-proof (cons proof proof-stack)))))))))
    `(acl2::encapsulate
      ()
      ,@(loop for proof-case in (mapcar #'cadr ind-obs-mapping)
              collect (let* ((proof-case-gen-thm (cdr (assoc-== proof-case subproof-data)))
                             (proof-case-name (get-full-proofname-in-stack proof-case (cons proof proof-stack))))
                        (when (not proof-case-gen-thm)
                          (error 'proof-builder-induction-missing-gen-thm
                                 :case proof-case
                                 :data subproof-data))
                        `(acl2::local ,(funcall proof-case-gen-thm proof-case-name))))
      ,@(when (not (missingp (Proof-exportation proof)))
          `((acl2::defthm ,exportation-proof-name
                          (equal ,(ts-expr (Proof-stmt proof))
                                 ,(ts-expr (Proof-exportation proof))))))
      (acl2::defthm ,proof-name
                    ,stmt
                    :rule-classes nil
                    :hints (("Goal" :instructions ,instructions))))))

;; Reset the ACL2 state back to before the definition of START-LOAD-FILE
(defun reset-file ()
  (acl2::ld 'acl2s::(:ubt START-LOAD-FILE)))

(defun create-reset-point ()
  ;; Create this function so that we can come back to this point in ACL2's history
  (acl2s-event 'acl2s::(defun START-LOAD-FILE () t)))

(declaim (ftype (function (Proof CompletedProofData &key (:prefix string) (:define-thm? boolean)) Status) check-single-proof))
(defun check-single-proof (proof completed-proofs &key (prefix "") (define-thm? t))
  (print2 (format nil "~a ~a" (Proof-kind proof) (Proof-name proof)))
  ;; TODO: is nil an appropriate default proof-stack?
  (multiple-value-bind
    (res extra-data)
    (handler-case
        (check-proof-struct proof completed-proofs nil :prefix prefix :define-thm? define-thm?)
      ;; If one of the higher level check-proof-struct-<kind>
      ;; functions wants to immediately fail a proof before
      ;; all of the checks are completed, it will raise this
      ;; error. We assume that the function already added
      ;; whatever specific error messages are appropriate, so
      ;; we just return :fail here.
      (checker-stop-error (_) :fail))
    (cond
     ((equal res :ok)
      (push-message (make-ProofMessage
                    ;; Note that these messages don't have IDs. This
                    ;; should signal to a UI that we don't want this
                    ;; message to also print out a relevant portion of
                    ;; the proof file.
                    :severity :info
                    :description (format nil "~a ~a OK" (Proof-kind proof) (Proof-name proof))
                    :proof (Proof-name proof)
                    :category "PROOF_STATUS"
                    :kind "PROOF_STATUS_OK"))
      (print2 (format nil "~a ~a ~a" (Proof-kind proof) (Proof-name proof) (green "OK"))))
     ((equal res :warn)
      (push-message (make-ProofMessage
                    :severity :info
                    :description (format nil "~a ~a WARN" (Proof-kind proof) (Proof-name proof))
                    :proof (Proof-name proof)
                    :category "PROOF_STATUS"
                    :kind "PROOF_STATUS_WARN"))
      (print2 (format nil "~a ~a ~a" (Proof-kind proof) (Proof-name proof) (yellow "WARN"))))
     (t
      (push-message (make-ProofMessage
                    :severity :info
                    :description (format nil "~a ~a FAIL" (Proof-kind proof) (Proof-name proof))
                    :proof (Proof-name proof)
                    :category "PROOF_STATUS"
                    :kind "PROOF_STATUS_FAIL"))
      (print2 (red (format nil "*** ~a ~a failed ***" (Proof-kind proof) (Proof-name proof))))))
    (values res extra-data)))

(defun check-proofs (proofs completed-proofs)
  (if (endp proofs)
      nil
    (multiple-value-bind
      (res extra-data)
      (check-single-proof (car proofs) completed-proofs)
      (cons res
            (check-proofs (cdr proofs)
                          (cons (make-CompletedProofDatum
                                 :status res
                                 :proof (car proofs)
                                 :gen-thm extra-data)
                                completed-proofs))))))

(defun run-sexpr (stmt)
  (let ((*package* (find-package "KEYWORD")))
    (v:debug :status "expr: ~S" (prover::ts-expr prover::stmt)))
  (handler-case
      (eval-in-acl2 (ts-expr stmt))
    (ld-internal-error (condition)
                       (progn (add-message (TaggedSExpr-id stmt)
                                           "This expression failed to run")
                              (print2 (red "FAIL") :nl " -- ")
                              (print2 (format nil "Failed to run the expression ~S" (ts-expr stmt)))
                              :fail))
    (ld-execution-error (condition)
                        (progn (add-message (TaggedSExpr-id stmt)
                                            "This expression failed to run")
                               (print2 (red "FAIL") :nl " -- ")
                               (print2 (format nil "Failed to run the expression ~S" (ts-expr stmt)))
                               :fail))
    (:no-error (_) :ok)))

(defun check-proof (proof completed-proofs)
  (redefine-theories)
  (multiple-value-bind
    (res extra-data)
    (check-single-proof proof completed-proofs)
    (values res (cons (make-CompletedProofDatum
                       :status res
                       :proof proof
                       :gen-thm extra-data)
                      completed-proofs))))

(defun check-proof-document-helper (proofs-and-stmts completed-proofs)
  (cond ((endp proofs-and-stmts) nil)
        ((proof-p (car proofs-and-stmts))
         (multiple-value-bind
           (res new-completed-proofs)
           (check-proof (car proofs-and-stmts) completed-proofs)
           (cons res (check-proof-document-helper (cdr proofs-and-stmts) new-completed-proofs))))
        (t (cons (run-sexpr (car proofs-and-stmts))
                 (check-proof-document-helper (cdr proofs-and-stmts) completed-proofs)))))

(defun add-message (id description &key (proof (if *CURRENT-PROOF* (Proof-name *CURRENT-PROOF*) "n.a.")) (severity :error) (kind (if (equal severity :warn) "MISC_WARNING" "MISC_ERROR")) (category kind))
  (push-message (make-ProofMessage :severity severity
                     :id id
                     :description description
                     :proof proof
                     :category category
                     :kind kind)))

(defun add-condition-message (condition &key (id (get-target-id condition))
                                        (severity (get-condition-severity condition))
                                        (description (short-report condition))
                                        (proof (if *CURRENT-PROOF* (Proof-name *CURRENT-PROOF*) "n.a."))
                                        (kind (or (get-condition-kind condition) (symbol-name (type-of condition))))
                                        (category (or (get-condition-category condition) (concatenate 'string "MISC_" (symbol-name severity)))))
  (push-message (make-ProofMessage :severity severity
                                  :id id
                                  :description description
                                  :proof proof
                                  :category category
                                  :kind kind)))

(defun push-message (message)
  (setf *MESSAGES* (cons message *MESSAGES*)))

(defun proof-id-to-string (id)
  (cond ((null id) nil)
        ((numberp id) (format nil "~D" id))
        (t (format nil "~{~D~^,~}" id))))

(defun message-to-xml-rep (message id)
  (xmls:make-node :name "message"
                  :attrs `(("id" ,(proof-id-to-string id))
                           ("severity" ,(ProofMessage-severity message))
                           ("proof" ,(ProofMessage-proof message))
                           ("category" ,(ProofMessage-category message))
                           ("kind" ,(ProofMessage-kind message)))
                  :children (list (ProofMessage-description message))))

(defun message-to-xml-reps (message)
  (let ((ids (ProofMessage-id message)))
    (if (not (and (consp ids) (equal (car ids) :each)))
        (list (message-to-xml-rep message ids))
      (loop for id in (cdr ids)
            collect (message-to-xml-rep message id)))))

(declaim (ftype (function (list) string) query-times-to-string))
(defun query-times-to-string (query-time-table)
  (let ((s (make-string-output-stream)))
    (loop for (time kind er query) in (sort query-time-table #'> :key #'car)
          do (format s "(~a ~a ~a ~a)~%" time kind er query))
    (get-output-stream-string s)))

(defun print-messages (print-timings?)
  (let ((messages (xmls:make-node :name "messages"
                                  :children (append
                                             (when print-timings?
                                               (list
                                                (xmls:make-node :name "message"
                                                                :attrs `(("id" nil)
                                                                         ("severity" :info)
                                                                         ("kind" "timing"))
                                                                :children (list (query-times-to-string acl2s-high-level-interface::*QUERY-TIME-TABLE*)))))
                                             (loop for message in *MESSAGES*
                                                   append (message-to-xml-reps message))))))
    (v:debug :status.messages "~a" (xmls:toxml messages))
    (v:debug :status.times "~a" (query-times-to-string acl2s-high-level-interface::*QUERY-TIME-TABLE*))
    (xmls:write-xml messages print::*FD-ERROR-STREAM*)))

(defun check-proof-document (proofs-and-stmts &key (print-timings? t))
  (setf *MESSAGES* nil)
  (create-reset-point)
  (let* ((proofs (remove-if-not #'proof-p proofs-and-stmts))
         (any-contract-completions nil))
    (if (endp proofs)
        (progn (print2 (yellow "WARN"))
               (print2 "File contained no proofs!"))
      t)
    (handler-bind
        ((used-contract-completion-warning #'(lambda (c)
                                              (push c any-contract-completions))))
      (reduce-statuses (check-proof-document-helper proofs-and-stmts nil)))
    (when any-contract-completions
      (print2-nonl (yellow "WARN: "))
      (print2 (format nil "A nontrivial contract completion was provided in ~{ ~a~}!~%In these ~
cases, the theorem proved is the contract completed version of the ~
original conjecture. Note that this is different from the original ~
conjecture. For each of these cases, we recommend that you update ~
the original conjecture so that contract completion is not required."
                      (mapcar #'(lambda (c) (get-full-proofname-in-stack
                                             (used-contract-completion-warning/proof c)
                                             (used-contract-completion-warning/proof-stack c)))
                              any-contract-completions)))
      (loop for any-contract-completion in any-contract-completions do
            (add-message nil (short-report any-contract-completion) :severity :warn)))
    (print-messages print-timings?)))

#|
;; induction obligations generation
(defun substitutions (fargs fcalls)
  (cond ((endp fcalls) '())
        (t (cons (pairlis fargs (cdar fcalls))
                 (substitutions fargs (cdr fcalls))))))

(defun make-ihs (subs st)
  (if (endp subs)
      ()
    (cons (sublis (car subs) st)
          (make-ihs (cdr subs) st))))


(defun induction-hypotheses (rcall args st)
  (if (endp rcall)
      ()
    (let ((subs (substitutions args rcall)))
      (make-ihs subs st))))

(defun appendif (l x)
  (if (endp (car x))
      l
    (append l x)))

(defun rec-remove-t (x)
  (if (atom x)
      x
    (remove 't (mapcar #'rec-remove-t x))))

(defun clean-tac (tac)
  (let* ((c (cadr tac))
         (c1 (car c))
         (c2 (cdr c)))
    (if (or (equal (car c1) 'if)
            (equal (car c1) 'not))
        (let ((r (replace-in* c1 '((if . and) ('nil . t)))))
          (rec-remove-t (remove 't (appendif r c2))))
      (cons 'and c))))


(defun alpha-subst-rcalls (rcalls subs)
  (if (endp rcalls)
      ()
    (let ((rcall (car rcalls)))
      (cons (cons (car rcall) (sublis subs (cdr rcall)))
            (alpha-subst-rcalls (cdr rcalls) subs)))))

(defun alpha-subst-ic (ic subs)
  (sublis subs ic))


(defun make-inductive-lemma (subs tac args st)
  (let* ((rcalls (cddr tac))
         (subs-rcalls (alpha-subst-rcalls rcalls subs))
         (ihs (induction-hypotheses subs-rcalls args st))
         (ic (clean-tac tac))
         (subs-ic    (alpha-subst-ic ic subs)))
    (if (endp ihs)
        (cons 'basic (list (append
                            (cons 'ACL2S::implies (list subs-ic))
                            (list st))))
      (cons 'inductive (list (append
                              (cons 'ACL2S::implies (list (append subs-ic ihs)))
                              (list st)))))))


(defun gen-induction-lemmas-help (subs tacs args st)
  (if (endp tacs)
      ()
    (cons (make-inductive-lemma subs (car tacs) args st)
          (gen-induction-lemmas-help subs (cdr tacs) args st))))

(defun get-induction-lemmas (trm1 st)
  (let* ((trm2 (cadr (acl2s-query `acl2s::(acl2::trans1 ',prover::trm1))))
         (trm  (if (equal trm2 nil) trm1 trm2))
         (fname (car trm))
         (trm-args (cdr trm))
         (args-varp (cadr (acl2s-query `acl2s::(mv nil (acl2s::all-varp ',prover::trm-args) state)))))
    (if args-varp
        (let* ((tacs (cadr (acl2s-query `acl2s::(mv nil (acl2::getpropc ',prover::fname 'acl2::induction-machine nil (w state)) state))))
               (func-args (cadr (acl2s-query `acl2s::(mv nil (acl2::formals
                                                              ',prover::fname
                                                              (w state))
                                                         state)))))
          (if tacs
              (if (equal (length (rem-dupes trm-args)) (length func-args))
                  (if (equal (length trm-args) (length func-args))
                      (let ((subs (car (substitutions func-args (list trm)))))
                        (gen-induction-lemmas-help subs tacs trm-args st))
                    (error "Argument count mismatch in induction term"))
                (error "Arguments can't be repeated in induction term"))
            (error "Undefined function in induction term")))
      (error "Not all induction arguments are variables"))))

(defun lemma-inductivep (lem)
  (equal (car lem) 'INDUCTIVE))

(defun lemma-basicp (lem)
  (equal (car lem) 'BASIC))

(defun induction-proof-obligations-old (trm st)
  (let* ((ihs (get-induction-lemmas trm st))
         (ind-lem (mapcar 'acl2s-untranslate (mapcar 'cadr (remove-if-not #'lemma-inductivep ihs))))
         (basic-lem (mapcar 'acl2s-untranslate (mapcar 'cadr (remove-if-not #'lemma-basicp ihs)))))
    (cons basic-lem ind-lem)))
|#
