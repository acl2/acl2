; An assistant to help find simple proofs
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "kestrel/utilities/world" :dir :system)
(include-book "kestrel/utilities/fresh-names" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/prove-dollar-plus" :dir :system)
(include-book "kestrel/utilities/checkpoints" :dir :system)
(include-book "kestrel/utilities/wrap-all" :dir :system)
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/theory-invariants" :dir :system)
(include-book "kestrel/terms-light/function-call-subterms" :dir :system)
(include-book "kestrel/terms-light/non-trivial-formals" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/negate-terms" :dir :system)
(include-book "kestrel/terms-light/replace-term-with-term" :dir :system)
(include-book "kestrel/terms-light/count-occurrences-in-term" :dir :system)
(include-book "kestrel/lists-light/true-list-fix" :dir :system)
(include-book "kestrel/typed-lists-light/append-all" :dir :system)
(include-book "std/util/defaggregate" :dir :system) ; reduce?
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/alists-light/rassoc-equal" :dir :system))

;; TODO: Add more proof techniques!
;; TODO: After a successful proof, try to combine steps/hints
;; TODO: Think about rule classes (watch for illegal rules!) and disablement of new theorems
;; TODO: How can we parallelize this?
;; TODO: Record both a safe proof (subgoal hints) and a nice proofs (rely on rules firing)?
;; TODO: Don't spawn a subproblem when the checkpoint is the same as the goal
;; TODO: add and use done-mapp
;; TODO: When we find a technique to prove a problem, remove all other open problems for the same formula
;; TODO: compare goals up to reordered hyps
;; TODO: subsumption when we finish a goal
;; TODO: Propagate failures back up
;; TODO: Handle obviously unprovable goals, like nil!
;; TODO: Try to reoreder hyps to make a nice rule
;; TODO: Untranslate to make the forms?
;; TODO: Assign better names to goals, based on their content

(local (in-theory (disable natp acons)))

;;;
;;; Library stuff
;;;

(defun filter-defined-fns (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (if (fn-definedp fn wrld)
          (cons fn (filter-defined-fns (rest fns) wrld))
        (filter-defined-fns (rest fns) wrld)))))

;dup?
;; Looks up all the KEYS in the ALIST, returning a list of the results (or nils, for absent keys).
(defun lookup-all (keys alist)
  (declare (xargs :guard (and (symbol-listp keys)
                              (alistp alist))))
  (if (endp keys)
      nil
    (cons (cdr (assoc-eq (first keys) alist))
          (lookup-all (rest keys) alist))))

;; Checks whether all the KEYS are bound in the ALIST
(defun all-keys-boundp (keys alist)
  (if (endp keys)
      t
    (and (assoc-eq (first keys) alist)
         (all-keys-boundp (rest keys) alist))))

;;;
;;; End of library stuff
;;;

;; A proof technique, such as (:direct), or (:induct f).
(defund techniquep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (case (car x)
         ;; (:induct <term>)
         (:induct (and (true-listp (fargs x))
                       (= 1 (len (fargs x)))
                       (pseudo-termp (farg1 x))))
         ;; (:generalize <term>)
         (:generalize (and (true-listp (fargs x))
                       (= 1 (len (fargs x)))
                       (pseudo-termp (farg1 x))))
         ;; (:enable ...fns-or-runes...)
         (:enable (and (true-listp (fargs x))
                       (true-listp (fargs x)) ; todo: strengthen?
                       ))
         (:direct (null (cdr x)))
         (otherwise nil))))

(defund technique-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (techniquep (first x))
         (technique-listp (rest x)))))

(defthm technique-listp-forward-to-true-listp
  (implies (technique-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable technique-listp))))

(defund problem-namep (name)
  (declare (xargs :guard t))
  (symbolp name))

(defthm problem-namep-of-fresh-symbol
  (implies (problem-namep desired-sym)
           (problem-namep (fresh-symbol desired-sym syms-to-avoid)))
  :hints (("Goal" :in-theory (enable problem-namep))))

(defund problem-name-listp (names)
  (declare (xargs :guard t))
  (if (atom names)
      (null names)
    (and (problem-namep (first names))
         (problem-name-listp (rest names)))))

(defthm problem-name-listp-to-true-listp
  (implies (problem-name-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable problem-name-listp))))

(defthm problem-name-listp-of-cons
  (equal (problem-name-listp (cons name names))
         (and (problem-namep name)
              (problem-name-listp names)))
  :hints (("Goal" :in-theory (enable problem-name-listp))))

(defund benefitp (x)
  (declare (xargs :guard t))
  (and (natp x)
       (<= x 1000)))

(defund chancep (x)
  (declare (xargs :guard t))
  (and (natp x)
       (<= x 1000)))

;dup
(defun maybe-step-limitp (lim)
  (declare (xargs :guard t))
  (or (null lim) ; no step limit
      (natp lim)))

;; A formula paired with a technique to try to prove it.
(std::defaggregate open-problem
                   ((name problem-namep) ; name for the formula being to be prove (not the problem = formula + technique)
                    (technique techniquep)
                    (formula pseudo-termp) ; or could store untranslated terms, or clauses
                    (benefit benefitp) ; benefit of solving this problem, from 0 to 1000 (with 1000 being as good as proving the top-level goal), todo: track benefits on behalf of each parent?
                    (parents problem-name-listp)
                    (chance chancep) ; estimated chance of success for this goal and technique
                    ;; todo: estimated cost of applying this technique to prove this goal (including proving and subgoals)
                    (last-step-limit maybe-step-limitp) ; either nil (not tried before) or a step-limit insufficient to handle the problem (e.g., to produce subgoals)
                    (old-techniques technique-listp) ; techniques to avoid trying again
                    )
                   :pred open-problemp
                   )

;; can the tool automate this?
(defthm rationalp-of-open-problem->last-step-limit
  (implies (and (open-problemp prob)
                (open-problem->last-step-limit prob))
           (rationalp (open-problem->last-step-limit prob)))
  :hints (("Goal" :use ((:instance return-type-of-open-problem->last-step-limit
                                   (x prob)))
           :in-theory (disable return-type-of-open-problem->last-step-limit))))

(defthm open-problem->benefit-linear
  (implies (and (open-problemp prob))
           (<= (open-problem->benefit prob) 1000))
  :rule-classes :linear)

(defthm open-problem->benefit-type
  (implies (open-problemp prob)
           (natp (open-problem->benefit prob)))
  :rule-classes :type-prescription)

(defthm open-problem->chance-linear
  (implies (and (open-problemp prob))
           (<= (open-problem->chance prob) 1000))
  :rule-classes :linear)

(defthm open-problem->chance-type
  (implies (open-problemp prob)
           (natp (open-problem->chance prob)))
  :rule-classes :type-prescription)

(local
 (defthm <=-of-floor-by-1-and-1000
   (implies (and (<= x 1000)
                 (rationalp x))
            (<= (floor x 1) 1000))))

(defund open-problem-listp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (open-problemp (first probs))
         (open-problem-listp (rest probs)))))

(defthm open-problem-listp-forward-to-true-listp
  (implies (open-problem-listp probs)
           (true-listp probs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable open-problem-listp))))

(defthm open-problemp-of-car
  (implies (and (open-problem-listp probs)
                (consp probs))
           (open-problemp (car probs)))
  :hints (("Goal" :in-theory (enable open-problem-listp))))

(defthm open-problem-listp-of-cdr
  (implies (and (open-problem-listp probs)
                (consp probs))
           (open-problem-listp (cdr probs)))
  :hints (("Goal" :in-theory (enable open-problem-listp))))

(defthm open-problem-listp-of-append
  (equal (open-problem-listp (append probs1 probs2))
         (and (open-problem-listp (true-list-fix probs1))
              (open-problem-listp probs2)))
  :hints (("Goal" :in-theory (enable open-problem-listp))))

(std::defaggregate pending-problem
  ((name problem-namep) ; name for the formula being to be prove (not the problem = formula + technique)
   (formula pseudo-termp) ; or could store untranslated terms, or clauses
   (subproblem-names problem-name-listp)
   (main-events t) ; a list of events to be submitted after the proofs of the named subproblems, todo: strengthen guard?
   )
  :pred pending-problemp)

(defund pending-problem-listp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (pending-problemp (first probs))
         (pending-problem-listp (rest probs)))))

;; A problem that we've not yet analyzed to determine which techniques may apply.
(std::defaggregate raw-problem
  ((name problem-namep) ; name for the formula being to be prove (not the problem = formula + technique)
   (formula pseudo-termp) ; or could store untranslated terms, or clauses
   (benefit benefitp) ; benefit of solving this problem, from 0 to 1000 (with 1000 being as good as proving the top-level goal), todo: track benefits on behalf of each parent?
   (parents problem-name-listp)
   ;; (chance chancep)   ; estimated chance of success for this goal and technique
   ;; todo: estimated cost of applying this technique to prove this goal (including proving and subgoals)
   (old-techniques technique-listp) ; techniques to avoid trying again
   )
  :pred raw-problemp)

(defund raw-problem-listp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (raw-problemp (first probs))
         (raw-problem-listp (rest probs)))))

(defthm raw-problem-listp-forward-to-true-listp
  (implies (raw-problem-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable raw-problem-listp))))

(defthm raw-problem-listp-of-cons
  (equal (raw-problem-listp (cons prob probs))
         (and (raw-problemp prob)
              (raw-problem-listp probs)))
  :hints (("Goal" :in-theory (enable raw-problem-listp))))

(defund name-mapp (map)
  (declare (xargs :guard t))
  (and (alistp map)
       (symbol-listp (strip-cars map))
       (pseudo-term-listp (strip-cdrs map))))

(defthm name-mapp-forward-alistp
  (implies (name-mapp name-map)
           (alistp name-map))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable name-mapp))))

(defthm symbol-listp-of-strip-cars-when-name-mapp
  (implies (name-mapp name-map)
           (symbol-listp (strip-cars name-map)))
  :hints (("Goal" :in-theory (enable name-mapp))))

(defthm name-mapp-of-acons
  (equal (name-mapp (acons name formula name-map))
         (and (problem-namep name)
              (pseudo-termp formula)
              (name-mapp name-map)))
  :hints (("Goal" :in-theory (enable name-mapp acons))))

(defthm problem-namep-of-car-of-rassoc-equal
  (implies (name-mapp name-map)
           (problem-namep (car (rassoc-equal formula name-map))))
  :hints (("Goal" :in-theory (enable name-mapp rassoc-equal))))

;; clause is: ((not <hyp1>) ... (not <hypn>) conc)
(defun clause-to-implication (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (endp clause)
      *nil* ; empty disjunction is false
    (if (endp (rest clause))
        (first clause)
      `(implies ,(conjoin (negate-terms (butlast clause 1))) ; todo: not very readable, but this has to be a translated term
                ,(car (last clause))))))

(defun clauses-to-implications (clauses)
  (declare (xargs :guard (pseudo-term-list-listp clauses)))
  (if (endp clauses)
      nil
    (cons (clause-to-implication (first clauses))
          (clauses-to-implications (rest clauses)))))

(defun filter-rec-fns (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (if (recursivep fn nil wrld)
          (cons fn (filter-rec-fns (rest fns) wrld))
        (filter-rec-fns (rest fns) wrld)))))

(defconst *fns-not-worth-enabling*
  (append '(implies not) ; don't bother trying to enable these simple functions
          ;; Can't enable these since they are primitives:
          (strip-cars *primitive-formals-and-guards*)))

;; Get the techniques from the PROBS
(defun map-open-problem->technique (probs)
  (declare (xargs :guard (open-problem-listp probs)))
  (if (endp probs)
      nil
    (cons (open-problem->technique (first probs))
          (map-open-problem->technique (rest probs)))))


;todo: allow benefit to differ for different subproblems
(defund make-raw-subproblems (names formulas benefit parents old-techniques)
  (declare (xargs :guard (and (problem-name-listp names)
                              (pseudo-term-listp formulas)
                              (benefitp benefit)
                              (problem-name-listp parents)
                              (technique-listp old-techniques))
                  :guard-hints (("Goal" :in-theory (enable problem-name-listp)))))
  (if (endp names)
      nil
    (cons (raw-problem (first names) (first formulas) benefit parents old-techniques)
          (make-raw-subproblems (rest names) (rest formulas) benefit parents old-techniques))))

;; Returns (mv raw-problems formula-names name-map).  The formula-names
;; returned may include the names of existing problems, in which case fewer raw-problems are returned.
(defun spawn-subproblems-for-formulas (formulas name-map benefit parent old-techniques
                                                base-name name-index
                                                raw-problems-acc formula-names-acc)
  (declare (xargs :guard (and (pseudo-term-listp formulas)
                              (name-mapp name-map)
                              (benefitp benefit)
                              (problem-namep parent)
                              (technique-listp old-techniques)
                              (symbolp base-name)
                              (natp name-index)
                              (raw-problem-listp raw-problems-acc)
                              (problem-name-listp formula-names-acc))))
  (if (endp formulas)
      (mv (reverse raw-problems-acc)  ; maybe skip the reverse
          (reverse formula-names-acc) ; maybe skip the reverse
          name-map)
    (let* ((formula (first formulas))
           ;; TODO: Handle problems that are equivalent but not identical (e.g., in the order of the hyps)?
           (res (rassoc-equal formula name-map))
           (name (fresh-symbol (pack$ base-name name-index)
                               (strip-cars name-map) ; todo: slow
                               )))
      (if res
          (let ((existing-name (car res)))
            ;; formula is already a goal in the system:
            ;; TODO: Up the benefit of the existing problem?
            (prog2$ (cw "(Note: The problem that would be called ~x0 is already present as ~x1.)~%" name existing-name)
                    (spawn-subproblems-for-formulas (rest formulas) name-map benefit parent old-techniques
                                                    base-name (+ 1 name-index)
                                                    raw-problems-acc ; nothing to add since problem already in the system
                                                    (cons existing-name formula-names-acc))))
        ;; formula not already a goal:
        (spawn-subproblems-for-formulas (rest formulas)
                                        (acons name formula name-map)
                                        benefit parent old-techniques
                                        base-name (+ 1 name-index)
                                        (cons (raw-problem name formula benefit (list parent) old-techniques)
                                              raw-problems-acc)
                                        (cons name formula-names-acc))))))

;; Same return type as attack-open-problem.
(defund attack-induct-problem (prob step-limit name-map state)
  (declare (xargs :guard (and (open-problemp prob)
                              (natp step-limit)
                              (name-mapp name-map))
                  :mode :program
                  :stobjs state))
  (b* ((name (open-problem->name prob))
       (formula (open-problem->formula prob))
       (benefit (open-problem->benefit prob))
       (technique (open-problem->technique prob)) ; (:induct <term>)
       (old-techniques (open-problem->old-techniques prob))
       (induct-term (farg1 technique))
       (induct-fn (ffn-symb induct-term))
       ;; We'll use the induction scheme specified by the technique:
       (hints `(("Goal" :induct ,induct-term ;; todo: mention macro-aliases instead when possible?
                 :in-theory (e/d ( ;; todo: mention macro-aliases instead when possible?
                                  ,induct-fn ; induction and definition rules (usually want both)
                                  )
                                 ;; Try to avoid obvious theory-invariant violations (does not handle all
                                 ;; theory-invariants, just those defined using incompatible):
                                 (,@(incompatible-runes `(:definition ,induct-fn) (w state))
                                  )))))
       (- (cw " ")) ; indent prove$+ output
       ((mv erp provedp failure-info state)
        (prove$+ formula
                 :hints hints
                 :step-limit step-limit
                 ;; todo: :otf-flg?
                 ))
       ((when erp) (mv erp nil nil nil nil nil name-map state))
       (form `(defthm ,name ,(untranslate formula nil (w state)) :hints ,hints)))
    (if provedp
        (progn$ (cw "Proved ~x0 by induction on ~x1.~%" name (farg1 technique))
                (mv nil :proved (list form) nil nil nil name-map state))
      (if (eq :step-limit-reached failure-info)
          ;; Step limit reached, so record the fact that we worked harder on it:
          (mv nil :updated nil (change-open-problem prob :last-step-limit step-limit) nil nil name-map state)
        ;; Didn't prove it but no limit reached, so we should have subgoals:
        (b* ((non-top-checkpoints (checkpoint-list nil state)) ; these are clauses
             (non-top-checkpoints (clauses-to-implications non-top-checkpoints))
             ((when (not non-top-checkpoints))
              ;; If this can happen legitimately, we could remove this:
              (er hard? 'attack-induct-problem "No checkpoints found for ~x0 but the proof was not step limited." name)
              (mv t nil nil nil nil nil name-map state))
             ((when (equal non-top-checkpoints (list formula)))
              (prog2$ (cw " No change.  Abandoning this technique.~%")
                      (mv nil :failed nil nil nil nil name-map state)))
             ((when (member-equal formula non-top-checkpoints))
              (prog2$ (cw " One checkpoint is the problem itself.  Abandoning this technique.~%")
                      (mv nil :failed nil nil nil nil name-map state)))
             ;; (- (cw "top-checkpoints: ~x0~%" top-checkpoints))
             (- (cw " non-top-checkpoints: ~x0~%" (untranslate-lst non-top-checkpoints t (w state))))
             ;; Spawn subproblems for each of the checkpoints under the induction:
             ((mv raw-subproblems subproblem-names name-map)
              (spawn-subproblems-for-formulas non-top-checkpoints
                                              name-map
                                              (+ -1 benefit) ; slightly less good than solving the original problem (todo: divide by number of subproblems?
                                              name
                                              (cons technique old-techniques) ; or don't since now we're in an induction?
                                              (pack$ name '-induct-)
                                              1
                                              nil nil))
             (- (cw "Spawned ~x0 new subproblems.~%" (len raw-subproblems))))
          (mv nil :split nil nil
              (pending-problem name formula subproblem-names
                               (list form) ; todo: put in use hints to prove the checkpoints using the subproblem defthms
                               )
              raw-subproblems
              name-map
              state))))))

;; Same return type as attack-open-problem.
(defund attack-enable-problem (prob step-limit name-map state)
  (declare (xargs :guard (and (open-problemp prob)
                              (natp step-limit)
                              (name-mapp name-map))
                  :mode :program
                  :stobjs state))
  (b* ((name (open-problem->name prob))
       (formula (open-problem->formula prob))
       (benefit (open-problem->benefit prob))
       (technique (open-problem->technique prob)) ; (:enable ....)
       (old-techniques (open-problem->old-techniques prob))
       (names-to-enable (fargs technique))
       (hints `(("Goal" :in-theory
                 (e/d (,@names-to-enable) ;; todo: mention macro-aliases instead when possible?
                      ;; Try to avoid obvious theory-invariant violations (does not handle all
                      ;; theory-invariants, just those defined using incompatible):
                      (,@(incompatible-runes-lst names-to-enable (w state))))
                 :do-not-induct t ; since we don't look at the non-top-checkpoints below anyway (the checkpoints exposed by the enabling may be proved by induction, of course)
                 )))
       (- (cw " ")) ; indent prove$+ output
       ((mv erp provedp failure-info state)
        (prove$+ formula
                 :hints hints
                 :step-limit step-limit
                 ;; todo: :otf-flg?
                 ))
       ((when erp) (mv erp nil nil nil nil nil name-map state))
       (form `(defthm ,name ,(untranslate formula nil (w state)) :hints ,hints))
       ((when provedp)
        (mv nil :proved (list form) nil nil nil name-map state))
       ;; Didn't prove it:
       ((when (eq :step-limit-reached failure-info))
        (mv nil :updated nil (change-open-problem prob :last-step-limit step-limit) nil nil name-map state))
       (top-checkpoints (checkpoint-list t state)) ; these are clauses
       (top-checkpoints (clauses-to-implications top-checkpoints))
       ((when (equal top-checkpoints (list formula)))
        (prog2$ (cw " No change.  Abandoning this technique.~%")
                (mv nil :failed nil nil nil nil name-map state)))
       ((when (member-equal formula top-checkpoints))
        (prog2$ (cw " One checkpoint is the problem itself.  Abandoning this technique.~%")
                (mv nil :failed nil nil nil nil name-map state)))
       ;; (non-top-checkpoints (checkpoint-list nil state))
       (- (cw " top-checkpoints: ~x0~%" (untranslate-lst top-checkpoints t (w state))))
       ;; Spawn subproblems for each of the checkpoints:
       ((mv raw-subproblems subproblem-names name-map)
        (spawn-subproblems-for-formulas top-checkpoints
                                        name-map
                                        (+ -1 benefit) ; slightly less good than solving the original problem (todo: divide by number of subproblems?
                                        name
                                        (cons technique old-techniques)
                                        (pack$ name '-enable-)
                                        1 nil nil))
       (- (cw "Spawned ~x0 new subproblems.~%" (len raw-subproblems))))
    (mv nil :split nil nil
        (pending-problem name formula subproblem-names
                         (list form) ; todo: put in use hints to prove the checkpoints using the subproblem defthms
                         )
        raw-subproblems
        name-map
        state)))

;; Same return type as attack-open-problem.
;; TODO: Since this doesn't call prove$, it should be quick and so could be done when we elaborate the problem
(defund attack-generalize-problem (prob step-limit name-map state)
  (declare (xargs :guard (and (open-problemp prob)
                              (natp step-limit)
                              (name-mapp name-map))
                  :mode :program
                  :stobjs state)
           (ignore step-limit))
  (b* ((name (open-problem->name prob))
       (formula (open-problem->formula prob))
       (benefit (open-problem->benefit prob))
       (technique (open-problem->technique prob)) ; (:generalize <term>)
       (old-techniques (open-problem->old-techniques prob))
       ;; TODO: When generalizing, we might need to add a type hyp about the new var.
       (term-to-generalize (farg1 technique))
       (vars (free-vars-in-term formula))
       (new-var (fresh-symbol 'x vars))
       (generalized-formula (replace-term-with-term term-to-generalize new-var formula))
       (- (cw " (Generalized Formula: ~x0)~%" generalized-formula))
       ;; Spawn a subproblem for the generalized problem:
       ((mv raw-subproblems subproblem-names name-map)
        (spawn-subproblems-for-formulas (list generalized-formula)
                                        name-map
                                        (+ -1 benefit) ; slightly less good than solving the original problem
                                        name
                                        (cons technique old-techniques)
                                        (pack$ name '-generalize-)
                                        1 ; todo: suppress the use of numbered indices when there is only one subproblem?
                                        nil nil))
       (- (cw "Spawned ~x0 new subproblems.~%" (len raw-subproblems))))
    (mv nil :split nil nil
        (pending-problem name formula subproblem-names
                         (list `(defthm ,name
                                  ,(untranslate formula nil (w state))
                                  :hints (("Goal" :in-theory nil
                                           :use (:instance ,(first subproblem-names)
                                                           (,new-var ,term-to-generalize)))))))
        raw-subproblems
        name-map
        state)))

;; Returns (mv erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state), where RES is :proved, :updated, or :split.
;; If RES is :proved, then PROOF-EVENTS contain the proof.
;; If RES is :updated, then UPDATED-OPEN-PROBLEM is a replacement for PROB (e.g., with a higher last-step-limit)
;; If RES is :split, then NEW-PENDING-PROBLEM is a pending problem awaiting solution of the RAW-SUBPROBLEMS (todo: since there might only be one, perhaps :split isn't a good name)
;; If RES is :failed, nothing else is returned
;; TODO: For some techniques, breaking down a problem into subproblems doesn't require a prover call, so we could do those first
(defund attack-open-problem (prob step-limit name-map state)
  (declare (xargs :guard (and (open-problemp prob)
                              (natp step-limit)
                              (name-mapp name-map))
                  :mode :program
                  :stobjs state))
  (b* ((technique (open-problem->technique prob))
       (name (open-problem->name prob))
       (formula (open-problem->formula prob))
       (- (cw "(Attacking ~x0 by~% ~x1.~%" name technique))
       (- (cw " (Step limit is ~x0.)~%" step-limit))
       (- (cw " (Formula: ~x0.)~%" (untranslate-lst formula t (w state)))))
    (mv-let (erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state)
      (case (car technique)
        (:induct (attack-induct-problem prob step-limit name-map state))
        (:enable (attack-enable-problem prob step-limit name-map state))
        (:generalize (attack-generalize-problem prob step-limit name-map state))
        ;;todo
        (otherwise (prog2$ (er hard? 'attack-open-problem "Unknown technique in problem ~x0." prob)
                           (mv t nil nil nil nil nil name-map state))))
      (progn$ (and (eq res :proved) (cw " Proved it!)~%"))
              (and (eq res :updated) (cw " Reached step limit.)~%"))
              (and (eq res :split) (cw " Split into ~x0 subproblems.)~%" (len raw-subproblems)))
              (and (eq res :failed) (cw " Failed.)~%" (len raw-subproblems)))
              (mv erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state)))))

;; For each subterms of the goal, this considers doing an induction based on it.
(defun make-induct-problems (subterms name formula benefit parents old-techniques wrld)
  (declare (xargs :guard (and (pseudo-term-listp subterms)
                              (symbolp name)
                              (pseudo-termp formula)
                              (benefitp benefit)
                              (problem-name-listp parents)
                              (technique-listp old-techniques)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable techniquep)))))
  (if (endp subterms)
      nil
    (let ((subterm (first subterms)))
      (if (and (consp subterm)
               (symbolp (ffn-symb subterm))
               (not (eq 'quote (ffn-symb subterm)))
               (recursivep (ffn-symb subterm) nil wrld)
               (= 1 (len (fn-recursive-partners (ffn-symb subterm) wrld))) ; ensures singly recursive (todo: add support for mutual recursion)
               (symbol-listp (fargs subterm)) ; must be a call on all vars (todo: relax?)
               )
          (let ((technique `(:induct ,subterm)))
            (if (member-equal technique old-techniques)
                (make-induct-problems (rest subterms) name formula benefit parents old-techniques wrld) ; already tried this technique
              (cons (open-problem name technique formula
                                  benefit
                                  parents
                                  500 ; todo: chance
                                  nil ; no step-limit tried yet
                                  old-techniques)
                    (make-induct-problems (rest subterms) name formula benefit parents old-techniques wrld))))
        (make-induct-problems (rest subterms) name formula benefit parents old-techniques wrld)))))

;; For each function call subterm of the goal, this considers generalizing it.
;; TODO: Try generalizing terms that only occur once.
(defun make-generalize-problems (subterms name formula benefit parents old-techniques wrld)
  (declare (xargs :guard (and (pseudo-term-listp subterms)
                              (symbolp name)
                              (pseudo-termp formula)
                              (benefitp benefit)
                              (problem-name-listp parents)
                              (technique-listp old-techniques)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable techniquep)))))
  (if (endp subterms)
      nil
    (let ((subterm (first subterms)))
      (if (and (consp subterm) ; not a var
               (symbolp (ffn-symb subterm)) ; not a lambda
               (not (eq 'quote (ffn-symb subterm))) ; not a quoted constant
               (< 1 (count-occurences-in-term subterm formula)) ; for now, we only generalize terms that appear more than once
               )
          (let ((technique `(:generalize ,subterm)))
            (if (member-equal technique old-techniques)
                ;; already tried this technique, so skip:
                (make-generalize-problems (rest subterms) name formula benefit parents old-techniques wrld)
              (cons (open-problem name technique formula
                                  benefit
                                  parents
                                  500 ; todo: chance
                                  nil ; no step-limit tried yet
                                  old-techniques)
                    (make-generalize-problems (rest subterms) name formula benefit parents old-techniques wrld))))
        (make-generalize-problems (rest subterms) name formula benefit parents old-techniques wrld)))))

(defun make-enable-problems (items name formula benefit parents old-techniques wrld)
  (declare (xargs :guard (and (true-listp items) ; names and runes
                              (symbolp name)
                              (pseudo-termp formula)
                              (benefitp benefit)
                              (problem-name-listp parents)
                              (technique-listp old-techniques)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable techniquep)))))
  (if (endp items)
      nil
    (let* ((item (first items))
           (technique `(:enable ,item)))
      (if (member-equal technique old-techniques) ; todo: what if an old-technique enabled this function and more?
          (make-enable-problems (rest items) name formula benefit parents old-techniques wrld) ; already tried this technique
        (cons (open-problem name technique formula
                            benefit
                            parents
                            600 ; todo: chance
                            nil ; no step-limit tried yet
                            old-techniques)
              (make-enable-problems (rest items) name formula benefit parents old-techniques wrld))))))

;; Given a raw-problem, analyze it to determine which proof techniques might apply.
;; Returns a list of open problems.
(defun elaborate-raw-problem (prob wrld)
  (declare (xargs :guard (and (raw-problemp prob)
                              (plist-worldp wrld))
                  :verify-guards nil ; todo
                  ))
  (b* ((name (raw-problem->name prob))
       (- (cw "(Determining techniques for ~x0:~%" name))
       (formula (raw-problem->formula prob))
       (benefit (raw-problem->benefit prob))
       (parents (raw-problem->parents prob))
       (old-techniques (raw-problem->old-techniques prob))
       (subterms (find-all-fn-call-subterms formula nil))
       (fns (all-fnnames formula)) ; todo: keep only defined ones?
       (defined-fns (filter-defined-fns fns wrld))
       (defined-rec-fns (filter-rec-fns defined-fns wrld))
       (defined-non-rec-fns (set-difference-eq defined-fns defined-rec-fns))
       ;; TODO: Consider using alternate definition rules for fns
       ;; start with an empty list of problems:
       (probs nil)
       ;; todo: :direct
       ;; Add :enable problems:
       (items-to-consider-enabling (append (set-difference-eq defined-non-rec-fns *fns-not-worth-enabling*)
                                           ;; here we try enabling just the :definition of the recursive functions,
                                           ;; because elsewhere we try induction with them:
                                           (wrap-all :definition defined-rec-fns)))
       (probs (append (make-enable-problems items-to-consider-enabling name formula benefit parents old-techniques wrld)
                      probs))
       ;; Add :induct problems:
       (probs (append (make-induct-problems subterms name formula benefit parents old-techniques wrld)
                      probs))
       ;; Add :generalize problems:
       (probs (append (make-generalize-problems subterms name formula benefit parents old-techniques wrld)
                      probs))
       (- (cw " Created ~x0 problems using these techniques:~| ~x1.)~%" (len probs) (map-open-problem->technique probs))))
    probs))

(defun elaborate-raw-problems (probs wrld)
  (declare (xargs :guard (and (raw-problem-listp probs)
                              (PLIST-WORLDP WRLD))
                  :verify-guards nil ; todo
                  ))
  (if (endp probs)
      nil
    (append (elaborate-raw-problem (first probs) wrld)
            (elaborate-raw-problems (rest probs) wrld))))


;; Returns (mv changep pending-probs done-map).
;; todo: optimize by building some indices?
;; TODO: Increase the benefit of remaining subproblems?
(defun handle-pending-probs-aux (pending-probs done-map pending-probs-acc changep)
  (declare (xargs :guard (and (pending-problem-listp pending-probs)
                              (name-mapp done-map)
                              (pending-problem-listp pending-probs-acc)
                              (booleanp changep))
                  :verify-guards nil ; todo
                  ))
  (if (endp pending-probs)
      (mv changep (reverse pending-probs-acc) done-map)
    (let* ((prob (first pending-probs)) ; should be non-empty, right?
           (subproblem-names (pending-problem->subproblem-names prob)))
      (if (not (all-keys-boundp subproblem-names done-map))
          ;; some subproblem remains to be handled, so we can't move this pending problem to done
          (handle-pending-probs-aux (rest pending-probs) done-map (cons prob pending-probs-acc) changep)
        ;; all subproblems are done!:
        (handle-pending-probs-aux (rest pending-probs)
                                  (acons (pending-problem->name prob)
                                         ;; We return the proofs of all the subproblems, followed by the events that prove then pending problem using them:
                                         ;; todo: what if early ones mess with later ones?:
                                         (append (append-all (lookup-all subproblem-names done-map))
                                                 (pending-problem->main-events prob))
                                         done-map)
                                  pending-probs-acc ; don't add this subproblem (no longer pending)
                                  t)))))

;; Returns (mv pending-probs done-map).
(defun handle-pending-probs (pending-probs done-map)
  (declare (xargs :mode :program)) ;todo
  (b* (((mv changep pending-probs done-map)
        (handle-pending-probs-aux pending-probs done-map nil nil)))
    (if changep
        (handle-pending-probs pending-probs done-map)
      (mv pending-probs done-map))))

(defund problem-goodness (prob)
  (declare (xargs :guard (open-problemp prob)))
  (let* ((chance-frac (/ (open-problem->chance prob) 1000))
         (goodness (floor (* (open-problem->benefit prob) chance-frac)
                          1)))
    goodness))

(defthm natp-of-problem-goodness
  (implies (open-problemp prob)
           (natp (problem-goodness prob)))
  :hints (("Goal" :in-theory (enable problem-goodness))))

(defthm <=-of-problem-goodness-and-1000
  (implies (open-problemp prob)
           (<= (problem-goodness prob) 1000))
  :hints (("Goal" :use (:instance <=-of-floor-by-1-and-1000
                                  (x (* 1/1000 (OPEN-PROBLEM->BENEFIT PROB)
                                        (OPEN-PROBLEM->CHANCE PROB))))
           :nonlinearp t
           :in-theory (e/d (problem-goodness) (<=-of-floor-by-1-and-1000)))))

(defun skip-step-limited-probs (open-probs step-limit)
  (declare (xargs :guard (and (open-problem-listp open-probs)
                              (natp step-limit))
                  ;; todo: can the tool prove the guard obligs without this hint?:
                  :guard-hints (("Goal" :in-theory (enable OPEN-PROBLEM-LISTP)))))
  (if (endp open-probs)
      nil
    (let* ((prob (first open-probs))
           (last-step-limit (open-problem->last-step-limit prob)))
      (if (and last-step-limit
               (<= step-limit last-step-limit))
          ;; no point in trying prob due to step limit, so skip it:
          (skip-step-limited-probs (rest open-probs) step-limit)
        open-probs))))

;; Returns the best problem
(defun choose-best-problem (open-probs
                            best-prob-so-far
                            goodness-of-best-so-far)
  (declare (xargs :guard (and (open-problem-listp open-probs)
                              (open-problemp best-prob-so-far)
                              (natp goodness-of-best-so-far)
                              (<= goodness-of-best-so-far 1000))
                  ;; todo: can the tool prove the guard obligs without this hint?:
                  :guard-hints (("Goal" :in-theory (enable OPEN-PROBLEM-LISTP)))
                  ))
  (if (endp open-probs)
      best-prob-so-far
    (let* ((prob (first open-probs))
           (goodness (problem-goodness prob)))
      (choose-best-problem (rest open-probs)
                           (if (> goodness goodness-of-best-so-far)
                               prob
                             best-prob-so-far)
                           (if (> goodness goodness-of-best-so-far)
                               goodness
                             goodness-of-best-so-far)))))

;; Returns nil, or :step-limited, or a problem
(defun choose-next-problem (open-probs step-limit)
  (declare (xargs :guard (and (open-problem-listp open-probs)
                              (consp open-probs) ; at least 1 problem
                              (natp step-limit))
                  :guard-hints (("Goal" :in-theory (enable OPEN-PROBLEM-LISTP)))
                  ))
  (let ((open-probs (skip-step-limited-probs open-probs step-limit)))
    (if (not open-probs)
        :step-limited ;; all problems have been tried with a step-limit at least STEP-LIMIT
      (choose-best-problem (rest open-probs) (first open-probs) (problem-goodness (first open-probs))))))

;; Returns (mv erp provedp proof-events state).
(defun repeatedly-attack-problems (open-probs
                                   pending-probs
                                   step-limit
                                   name-map ; alist from problem names to goals
                                   done-map ; alist from problem names to successful event sequences (ending in a proof of the goal corresponding to that name)
                                   top-name
                                   state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ( ;(- (cw "Loop iter.~%"))
       ((when (not open-probs))
        (cw "NO PROBLEMS LEFT! FAILING.")
        (mv t nil nil state))
       (- (cw "(Choosing next problem (~x0 open, ~x1 pending)." (len open-probs) (len pending-probs)))
       ;; (- (cw "~% (~x0 Pending problems: ~X12)~%" (len pending-probs) pending-probs nil))
       ;; (- (cw "~% (~x0 Open problems: ~X12)" (len open-probs) open-probs nil))
       (- (cw ")~%"))
       (res (choose-next-problem open-probs step-limit))
       ((when (not res)) ; can this happen?
        (er hard? 'repeatedly-attack-problems "No open problems.  Proof attempt failed.")
        (mv t nil nil state))
       ;; We've reached the current step limit for all problems left, so raise
       ;; the limit and try again:
       ((when (eq :step-limited res))
        (repeatedly-attack-problems open-probs
                                    pending-probs
                                    (* 2 step-limit)
                                    name-map
                                    done-map
                                    top-name
                                    state))
       (prob res)
       ;; Found a problem to attack:
       ((mv erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state)
        (attack-open-problem prob step-limit name-map state))
       ((when erp) (mv erp nil nil state)))
    ;; TODO: Handle failures, both "no progress" and subgoal of nil (remove other attempts to prove).  will need to update info on parent problem and maybe children (problems should track their parents, maybe along with benefits)
    (if (eq :proved res)
        (b* ((name (open-problem->name prob))
             (done-map (acons name proof-events done-map))
             ((mv pending-probs done-map)
              (handle-pending-probs pending-probs done-map)))
          (let ((res (assoc-eq top-name done-map)))
            (if res
                ;; We've proved the top-level goal!
                (mv nil t (cdr res) state)
              ;; Didn't prove the top-level goal yet:
              (repeatedly-attack-problems (remove-equal prob open-probs) ;this problem is done -- TODO: Remove other attempts to prove this formula
                                          pending-probs
                                          step-limit
                                          name-map ; alist from problem names to goals
                                          done-map ; alist from problem names to successful event sequences (ending in a proof of the goal corresponding to that name)
                                          top-name
                                          state))))
      (if (eq :updated res)
          (repeatedly-attack-problems (cons updated-open-problem (remove-equal prob open-probs))
                                      pending-probs
                                      step-limit
                                      name-map
                                      done-map
                                      top-name
                                      state)
        (if (eq :failed res)
            (repeatedly-attack-problems (remove-equal prob open-probs)
                                        pending-probs
                                        step-limit
                                        name-map
                                        done-map
                                        top-name
                                        state)
          (if (eq :split res)
              (let ((new-open-probs (elaborate-raw-problems raw-subproblems (w state)))) ; make open problems for all the ways of solving each raw-subproblem
                (repeatedly-attack-problems (append new-open-probs (remove-equal prob open-probs))
                                            (cons new-pending-problem pending-probs)
                                            step-limit
                                            name-map
                                            done-map
                                            top-name
                                            state))
            (prog2$ (er hard? 'repeatedly-attack-problems "Unknown result: ~x0." res)
                    (mv t nil nil state))))))))

;; Returns (mv erp event state).
(defun help-with-fn (form state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((state (set-print-case :downcase state)) ; make printing of forms downcase, to support the use copyind and pasting them
       (- (cw "~%~%Trying to help with:~%~x0.~%" form))
       (theorem-type (car form))
       (body (if (eq 'thm theorem-type)
                 (second form)
               (third form) ; for defthm
               ))
       (body (translate-term body 'help-fn (w state)))
       (name (if (eq 'thm theorem-type)
                 'the-thm
               (second form) ; for defthm
               ))
       (raw-prob (raw-problem name body 1000
                              nil ; no parents ; todo: perhaps we could use this instead of passing around the top-name
                              nil))
       (open-probs (elaborate-raw-problem raw-prob (w state)))
       ((mv erp provedp proof-events state)
        (repeatedly-attack-problems open-probs
                                    nil
                                    10000
                                    (acons name body nil) ; initial name-map
                                    nil                   ; initial done-map
                                    name                  ; top name to prove
                                    state))
       ((when erp) (mv erp nil state))
       ((when (not provedp))
        (cw "Failed to prove.~%")
        (mv t nil state)))
    (progn$ (cw "~% !!! PROOF FOUND:~%~X01" proof-events nil)
            (cw "Submitting proof now.~%")
            (mv nil `(progn ,@proof-events) state))))

;; Returns (mv erp event state).
(defun h-fn (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (help-with-fn (most-recent-theorem state) ;throws an error if there isn't one, TODO: What if the theorem is in an encapsulate?  Better to look for the checkpoints?
                state))

;; Call this to get help with the most recent thm or defthm attempt.
;; We could call this tool "help' but that name is already taken.
(defmacro h ()
  '(make-event-quiet (h-fn state)))

;; Wrap this around a form (a defthm or thm) to get help with it.
(defmacro help-with (form)
  `(make-event-quiet (help-with-fn ',form state)))
