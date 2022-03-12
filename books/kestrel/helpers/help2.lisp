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
(include-book "kestrel/terms-light/function-call-subterms" :dir :system)
(include-book "kestrel/terms-light/non-trivial-formals" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/negate-terms" :dir :system)
(include-book "std/util/defaggregate" :dir :system) ; reduce?
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))

;; TODO: Add more proof techniques!
;; TODO: After a successful proof, try to combine steps
;; TODO: Think about rule classes (watch for illegal rules!) and disablement of new theorems
;; TODO: How can we parallelize this?

(local (in-theory (disable natp)))

;;;
;;; Library stuff
;;;

;dup?
(defun append-all (xs)
  (declare (xargs :guard (true-list-listp xs)))
  (if (endp xs)
      nil
    (append (first xs) (append-all (rest xs)))))

;dup?
(defun lookup-all (keys alist)
  (declare (xargs :guard (and (symbol-listp keys)
                              (alistp alist))))
  (if (endp keys)
      nil
    (cons (cdr (assoc-eq (first keys) alist))
          (lookup-all (rest keys) alist))))

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

(defund problem-name-listp (names)
  (declare (xargs :guard t))
  (if (atom names)
      (null names)
    (and (problem-namep (first names))
         (problem-name-listp (rest names)))))

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
                    (benefit benefitp) ; benefit of solving this problem, from 0 to 1000 (with 1000 being as good as proving the top-level goal)
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

(defthm open-problemp-of-car
  (implies (and (open-problem-listp probs)
                (consp probs))
           (open-problemp (car probs)))
  :hints (("Goal" :in-theory (enable open-problem-listp))))

(std::defaggregate pending-problem
                   ((name problem-namep) ; name for the formula being to be prove (not the problem = formula + technique)
                    (formula pseudo-termp) ; or could store untranslated terms, or clauses
                    (subproblem-names problem-name-listp)
                    (main-events t) ; a list of events to be submitted after the proofs of the named subproblems, todo: strengthen guard?
                    )
                   :pred pending-problemp
                   )

(defund pending-problem-listp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (pending-problemp (first probs))
         (pending-problem-listp (rest probs)))))

;; A problem that we've not yet analyzed to determine which techniques may apply.
(std::defaggregate raw-problem
                   ((name problem-namep) ; name for the formula being to be prove (not the problem = formula + technique)
                    ;; (technique techniquep)
                    (formula pseudo-termp) ; or could store untranslated terms, or clauses
                    (benefit benefitp) ; benefit of solving this problem, from 0 to 1000 (with 1000 being as good as proving the top-level goal)
                    ;; (chance chancep)   ; estimated chance of success for this goal and technique
                    ;; todo: estimated cost of applying this technique to prove this goal (including proving and subgoals)
                    (old-techniques technique-listp) ; techniques to avoid trying again
                    )
                   :pred raw-problemp
                   )

(defund raw-problem-listp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (raw-problemp (first probs))
         (raw-problem-listp (rest probs)))))

;todo: allow benefit to differ for different subproblems
(defund make-raw-subproblems (names formulas benefit old-techniques)
  (declare (xargs :guard (and (problem-name-listp names)
                              (pseudo-term-listp formulas)
                              (benefitp benefit)
                              (technique-listp old-techniques))
                  :guard-hints (("Goal" :in-theory (enable problem-name-listp)))))
  (if (endp names)
      nil
    (cons (raw-problem (first names) (first formulas) benefit old-techniques)
          (make-raw-subproblems (rest names) (rest formulas) benefit old-techniques))))

(defund name-mapp (map)
  (declare (xargs :guard t))
  (and (alistp map)
       (symbol-listp (strip-cars map))
       (pseudo-term-listp (strip-cdrs map))))

;; clause is: ((not <hyp1>) ... (not <hypn>) conc)
(defun clause-to-implication (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (if (endp (rest clause))
      clause
    `(implies ,(conjoin (negate-terms (butlast clause 1))) ; todo: not very readable, but this has to be a translated term
              ,(car (last clause)))))

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
  (if (endp probs)
      nil
    (cons (open-problem->technique (first probs))
          (map-open-problem->technique (rest probs)))))


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
       (hints `(("Goal" :induct ,(farg1 technique)
                 :in-theory (enable ;(:i ,(farg1 technique))
                             ,(ffn-symb (farg1 technique)) ; induction and definition rules (usually want both)
                             ))))
       ((mv erp provedp failure-info state)
        (prove$+ formula
                 :hints hints
                 :step-limit 10000 ;todo
                 ;; todo: :otf-flg?
                 ))
       ((when erp) (mv erp nil nil nil nil nil name-map state))
       (form `(defthm ,name ,(untranslate formula nil (w state)) :hints ,hints))
       ((when provedp) (mv nil :proved (list form) nil nil nil name-map state))
       ;; Didn't prove it:
       ((when (eq :step-limit-reached failure-info))
        (mv nil :updated nil (change-open-problem prob :last-step-limit step-limit) nil nil name-map state))
       ;; (top-checkpoints (checkpoint-list t state))
       (non-top-checkpoints (checkpoint-list nil state))
       (non-top-checkpoints (clauses-to-implications non-top-checkpoints))
       ;; (- (cw "top-checkpoints: ~x0~%" top-checkpoints))
       (- (cw "non-top-checkpoints: ~x0~%" non-top-checkpoints))
       (subproblem-names (fresh-var-names (len non-top-checkpoints) (pack$ name '-induct) (strip-cars name-map))) ;slow?
       )
    (mv nil :split nil nil
        (pending-problem name formula subproblem-names
                         (list form) ; todo: put in use hints to prove the checkpoints using the subproblem defthms
                         )
        (make-raw-subproblems subproblem-names non-top-checkpoints
                              (+ -1 benefit) ; slightly less good than solving the original problem
                              (cons technique old-techniques))
        (append (pairlis$ subproblem-names non-top-checkpoints) ;inefficient
                name-map)
        state)))

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
       (hints `(("Goal" :in-theory (enable ,@(fargs technique)))))
       ((mv erp provedp failure-info state)
        (prove$+ formula
                 :hints hints
                 :step-limit 10000 ;todo
                 ;; todo: :otf-flg?
                 ))
       ((when erp) (mv erp nil nil nil nil nil name-map state))
       (form `(defthm ,name ,(untranslate formula nil (w state)) :hints ,hints))
       ((when provedp)
        (mv nil :proved (list form) nil nil nil name-map state))
       ;; Didn't prove it:
       ((when (eq :step-limit-reached failure-info))
        (mv nil :updated nil (change-open-problem prob :last-step-limit step-limit) nil nil name-map state))
       (top-checkpoints (checkpoint-list t state))
       (top-checkpoints (clauses-to-implications top-checkpoints))
       ;; (non-top-checkpoints (checkpoint-list nil state))
       (- (cw "top-checkpoints: ~x0~%" top-checkpoints))
       ;; (- (cw "non-top-checkpoints: ~x0~%" non-top-checkpoints))
       (subproblem-names (fresh-var-names (len top-checkpoints) (pack$ name '-enable) (strip-cars name-map))) ;slow?
       )
    (mv nil :split nil nil
        (pending-problem name formula subproblem-names
                         (list form) ; todo: put in use hints to prove the checkpoints using the subproblem defthms
                         )
        (make-raw-subproblems subproblem-names top-checkpoints
                              (+ -1 benefit) ; slightly less good than solving the original problem
                              (cons technique old-techniques))
        (append (pairlis$ subproblem-names top-checkpoints) ;inefficient
                name-map)
        state)))

;; Returns (mv erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state), where RES is :proved, :updated, or :split.
;; If RES is :proved, then PROOF-EVENTS contain the proof.
;; If RES is :updated, then UPDATED-OPEN-PROBLEM is a replacement for PROB (e.g., with a higher last-step-limit)
;; If RES is :split, then NEW-PENDING-PROBLEM is a pending problem awaiting solution of the RAW-SUBPROBLEMS.
;; TODO: For some techniques, breaking down a problem into subproblems doesn't require a prover call, so we could do those first
(defund attack-open-problem (prob step-limit name-map state)
  (declare (xargs :guard (and (open-problemp prob)
                              (natp step-limit)
                              (name-mapp name-map))
                  :mode :program
                  :stobjs state))
  (b* ((technique (open-problem->technique prob))
       (name (open-problem->name prob))
       (- (cw "(Attacking ~x0 by ~x1.~%" name technique)))
    (mv-let (erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state)
      (case (car technique)
        (:induct (attack-induct-problem prob step-limit name-map state))
        (:enable (attack-enable-problem prob step-limit name-map state))
        ;;todo
        (otherwise (prog2$ (er hard? 'attack-open-problem "Unknown technique in problem ~x0." prob)
                           (mv t nil nil nil nil nil name-map state))))
      (progn$ (and (eq res :proved) (cw "Proved it!)~%"))
              (and (eq res :updated) (cw "Reached step limit.)~%"))
              (and (eq res :split) (cw "Split into ~x0 subproblems.)~%" (len raw-subproblems)))
              (mv erp res proof-events updated-open-problem new-pending-problem raw-subproblems name-map state)))))

(defun make-induct-problems (subterms name formula benefit old-techniques wrld)
  (declare (xargs :guard (and (pseudo-term-listp subterms)
                              (symbolp name)
                              (pseudo-termp formula)
                              (benefitp benefit)
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
               (symbol-listp (fargs subterm)) ; must be a call on all vars (todo: relax?)
               )
          (let ((technique `(:induct ,subterm)))
            (if (member-equal technique old-techniques)
                (make-induct-problems (rest subterms) name formula benefit old-techniques wrld) ; already tried this technique
              (cons (open-problem name technique formula benefit
                                  500 ; todo: chance
                                  nil ; no step-limit tried yet
                                  old-techniques)
                    (make-induct-problems (rest subterms) name formula benefit old-techniques wrld))))
        (make-induct-problems (rest subterms) name formula benefit old-techniques wrld)))))

(defun make-enable-problems (items name formula benefit old-techniques wrld)
  (declare (xargs :guard (and (true-listp items) ; names and runes
                              (symbolp name)
                              (pseudo-termp formula)
                              (benefitp benefit)
                              (technique-listp old-techniques)
                              (plist-worldp wrld))
                  :guard-hints (("Goal" :in-theory (enable techniquep)))))
  (if (endp items)
      nil
    (let* ((item (first items))
           (technique `(:enable ,item)))
      (if (member-equal technique old-techniques) ; todo: what if an old-technique enabled this function and more?
          (make-enable-problems (rest items) name formula benefit old-techniques wrld) ; already tried this technique
        (cons (open-problem name technique formula benefit
                            600 ; todo: chance
                            nil ; no step-limit tried yet
                            old-techniques)
              (make-enable-problems (rest items) name formula benefit old-techniques wrld))))))

;; Given a raw-problem, analyze it to determine which proof techniques might apply.
;; Returns a list of open problems.
(defun elaborate-raw-problem (prob wrld)
  (declare (xargs :guard (and (raw-problemp prob)
                              (PLIST-WORLDP WRLD))
                  :verify-guards nil ; todo
                  ))
  (b* ((name (raw-problem->name prob))
       (- (cw "(Elaborating ~x0:~%" name))
       (formula (raw-problem->formula prob))
       (benefit (raw-problem->benefit prob))
       (old-techniques (raw-problem->old-techniques prob))
       (subterms (find-all-fn-call-subterms formula nil))
       (fns (all-fnnames formula))
       (rec-fns (filter-rec-fns fns wrld))
       (non-rec-fns (set-difference-eq fns rec-fns))
       ;; start with an empty list of problems:
       (probs nil)
       ;; todo: :direct
       ;; Add :enable problems:
       (items-to-consider-enabling (append (set-difference-eq non-rec-fns *fns-not-worth-enabling*)
                                           ;; here we try enabling just the :definition of the recursive functions,
                                           ;; because elsewhere we try induction with them:
                                           (wrap-all :definition rec-fns)))
       (probs (append (make-enable-problems items-to-consider-enabling name formula benefit old-techniques wrld)
                      probs))
       ;; Add :induct problems:
       (probs (append (make-induct-problems subterms name formula benefit old-techniques wrld)
                      probs))

       (- (cw "Created ~x0 problems using these techniques:~%~x1.)~%" (len probs) (map-open-problem->technique probs))))
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

(set-non-linearp t)
(defthm <=-of-problem-goodness-and-1000
  (implies (open-problemp prob)
           (<= (problem-goodness prob) 1000))
  :hints (("Goal" :use (:instance <=-of-floor-by-1-and-1000
                                  (x (* 1/1000 (OPEN-PROBLEM->BENEFIT PROB)
                                        (OPEN-PROBLEM->CHANCE PROB))))
           :in-theory (e/d (problem-goodness) (<=-of-floor-by-1-and-1000)))))
(set-non-linearp nil)

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
              (repeatedly-attack-problems (remove-equal prob open-probs) ;this problem is done
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
        (if (eq :split res)
            (let ((new-open-probs (elaborate-raw-problems raw-subproblems (w state)))) ; make open problems for all the ways of solving each raw-subproblem
              (repeatedly-attack-problems (append new-open-probs (remove-equal prob open-probs))
                                          (cons new-pending-problem pending-probs)
                                          step-limit
                                          name-map
                                          done-map
                                          top-name
                                          state))
          (prog2$ (er hard? "Unknown result: ~x0." res)
                  (mv t nil nil state)))))))

;; Returns (mv erp event state).
(defun help2-fn (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((state (set-print-case :downcase state)) ; make all printing downcase
       (most-recent-theorem (most-recent-theorem state))
       (- (cw "~%Trying to help with ~x0.~%" most-recent-theorem))
       (theorem-type (car most-recent-theorem))
       (body (if (eq 'thm theorem-type)
                 (second most-recent-theorem)
               (third most-recent-theorem) ; for defthm
               ))
       (body (translate-term body 'help2-fn (w state)))
       (name (if (eq 'thm theorem-type)
                 'the-thm
               (second most-recent-theorem) ; for defthm
               ))
       (raw-prob (raw-problem name body 1000 nil))
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
    (progn$ (cw "PROOF FOUND:~%~X01" proof-events nil)
            (cw "Submitting proof now.~%")
            (mv nil `(progn ,@proof-events) state))))

(defmacro help2 ()
  '(make-event-quiet (help2-fn state)))
