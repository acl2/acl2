; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../../README.

(in-package "ACL2")

(defun literalp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (equal x 0))))

(defthm literalp-compound-recognizer
  (equal (literalp x)
         (and (integerp x)
              (not (equal x 0))))
  :rule-classes :compound-recognizer)

(in-theory (disable literalp))

(defun literal-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (literalp (car x))
         (literal-listp (cdr x)))))

(defmacro negate (x)
  `(- ,x))

(defun unique-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      t
    (and (not (member (car x) (cdr x)))
         (unique-literalsp (cdr x)))))

(defun conflicting-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      nil
    (or (member (negate (car x)) (cdr x))
        (conflicting-literalsp (cdr x)))))

(defun clause-or-assignment-p (clause)
  (declare (xargs :guard t))
  (and (literal-listp clause)
       (unique-literalsp clause)
       (not (conflicting-literalsp clause))))

(defthm clause-or-assignment-p-forward-to-literal-listp
  (implies (clause-or-assignment-p x)
           (literal-listp x))
  :rule-classes :forward-chaining)

(defthm literal-listp-forward-to-eqlable-listp
  (implies (literal-listp x)
           (eqlable-listp x))
  :rule-classes :forward-chaining)

(defconst *deleted-clause* 0)

(defmacro deleted-clause-p (val)
  `(eql ,val *deleted-clause*))

(defun formula-fal-p (fal)

; Ensure tat every index from max down through 1 is bound to a clause or
; *deleted-clause*.

  (declare (xargs :guard t))
  (if (atom fal)
      t
    (let ((pair (car fal)))
      (and (consp pair)
           (let ((val (cdr pair)))
             (or (deleted-clause-p val)
                 (and (posp (car pair))
                      (clause-or-assignment-p val))))
           (formula-fal-p (cdr fal))))))

(defun formula-fal-max (fal)
  (declare (xargs :guard (formula-fal-p fal)))
  (cond ((atom fal) 0)
        ((deleted-clause-p (cdar fal))
         (formula-fal-max (cdr fal)))
        (t (max (caar fal)
                (formula-fal-max (cdr fal))))))

(defmacro formula-max (formula)
  `(car ,formula))

(defmacro formula-fal (formula)
  `(cdr ,formula))

(defmacro make-formula (max fal)
  `(cons ,max ,fal))

(defun formula-p (formula)
  (declare (xargs :guard t))
  (and (consp formula)
       (natp (formula-max formula))
       (formula-fal-p (formula-fal formula))
       (<= (formula-fal-max (formula-fal formula))
           (formula-max formula))))

(defun clause-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (clause-or-assignment-p (car x))
         (clause-listp (cdr x)))))

(defmacro index-listp (x)
  `(pos-listp ,x))

(defun drat-hint-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (posp (car x)) ; index
       (index-listp (cdr x))))

(defun drat-hint-listp (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        (t (and (drat-hint-p (car x))
                (drat-hint-listp (cdr x))))))

(defthm drat-hint-listp-forward-to-true-listp
  (implies (drat-hint-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defrec add-step
  ((index . clause)
   .
   (rup-indices . drat-hints))
  t)

(defun add-step-p (x)
  (declare (xargs :guard t))
  (and (weak-add-step-p x)
       (posp (access add-step x :index))
       (clause-or-assignment-p (access add-step x :clause))
       (index-listp (access add-step x :rup-indices))
       (drat-hint-listp (access add-step x :drat-hints))))

(defun proof-entry-p (entry)

; This function recognizes a "line" in the proof, which can have either of the
; following two formats.

; Deletion: (T i1 i2 ...), indicating deletion of the specified (by index)
; clauses.

; Addition: an ADD-STEP record indication addition of a clause with a given
; index and suitable unit propagation hints.

  (declare (xargs :guard t))
  (cond ((and (consp entry)
              (eq (car entry) t)) ; deletion
         (index-listp (cdr entry)))
        (t (add-step-p entry))))

(defmacro proof-entry-deletion-p (entry)

; assumes (proof-entry-p entry)

  `(eq (car ,entry) t))

(defmacro proof-entry-deletion-indices (entry)

; assumes (proof-entry-p entry) and (proof-entry-deletion-p entry)

  `(cdr ,entry))

(defun proofp (proof) ; primitive

; A proof is a true-list of proof-entry-p structures.

  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (proof-entry-p (car proof))
         (proofp (cdr proof)))))

(defthm proofp-forward-to-true-listp
  (implies (proofp x)
           (true-listp x))
  :rule-classes :forward-chaining)

(defun negate-clause-or-assignment (clause) ; primitive
  (declare (xargs :guard (clause-or-assignment-p clause)))
  (if (atom clause)
      nil
    (cons (negate (car clause))
          (negate-clause-or-assignment (cdr clause)))))

(defun-inline undefp (x)
  (declare (xargs :guard t))
  (not (booleanp x)))

(defun evaluate-literal (literal assignment)
  (declare (xargs :guard (and (literalp literal)
                              (clause-or-assignment-p assignment))))
  (cond
   ((member literal assignment) t)
   ((member (negate literal) assignment) nil)
   ;; When undefined, return 0.
   (t 0)))

(defun evaluate-clause (clause assignment)
  (declare (xargs :guard (and (clause-or-assignment-p clause)
                              (clause-or-assignment-p assignment))))
  (if (atom clause)
      nil
    (let* ((literal (car clause))
           (literal-value (evaluate-literal literal assignment)))
      (if (eq literal-value t)
          t
        (let* ((remaining-clause (cdr clause))
               (remaining-clause-value (evaluate-clause remaining-clause
                                                        assignment)))
          (cond
           ((eq remaining-clause-value t) t)
           ((undefp literal-value) 0)
           (t remaining-clause-value)))))))

(in-theory (disable clause-or-assignment-p))

(defthm clause-or-assignment-p-cdr
  (implies (clause-or-assignment-p clause)
           (clause-or-assignment-p (cdr clause)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defun is-unit-clause (clause assignment)

; If clause is a (pseudo) unit clause under assignment, return the unique
; unassigned literal (the others will be false).  Otherwise return nil unless
; the clause is false under assignment, in which case return t.

  (declare (xargs :guard (and (clause-or-assignment-p clause)
                              (clause-or-assignment-p assignment))
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
  (if (atom clause)
      t ; top-level clause is false under assignment
    (let ((val (evaluate-literal (car clause) assignment)))
      (cond
       ((eq val t) nil)
       ((undefp val)
        (if (null (evaluate-clause (cdr clause) assignment))
            (car clause)
          nil))
       (t ; (null val)
        (is-unit-clause (cdr clause) assignment))))))

(defthm booleanp-evaluate-clause-monotone
  (implies (booleanp (evaluate-clause cl a))
           (booleanp (evaluate-clause cl (cons lit a)))))

(defmacro unit-propagation-error (msg formula indices assignment)
  `(prog2$ (er hard? 'unit-propagation "~@0" ,msg)
           (unit-propagation ,formula (cdr ,indices) ,assignment)))

(defun unit-propagation (formula indices assignment)

; Return an extension of assignment by unit-propagation restricted to the given
; indices in formula, except that if a contradiction is found, return t
; instead.

  (declare (xargs :guard (and (formula-p formula)
                              (index-listp indices)
                              (clause-or-assignment-p assignment))
                  :verify-guards nil))
  (cond
   ((endp indices) assignment)
   ((> (car indices) (formula-max formula))

; This is a surprising case, discovered this case when attempting to prove that
; when unit propagation returns t then the formula does not evaluate to true
; (lemma unit-propagation-implies-unsat).  It is tempting simply to return
; assignment (hence failing to produce t).  However, it seems that would cause
; monotonicity to fail (unit-propagation-monotone), so reasoning would be more
; contorted: do all the reasoning about a version that recurs here (as we now
; do), and then fix the proof by connecting the two versions.  Instead, we go
; ahead and recur, but cause an error if we encounter this situation.

    (unit-propagation-error
     (msg "An index for unit-propagation, ~x0, has exceeded the maximum index ~
           of a formula, ~x1."
          (car indices) (formula-max formula))
     formula indices assignment))
   (t (let* ((pair (hons-get (car indices) (formula-fal formula)))
             (clause (and pair
                          (not (deleted-clause-p (cdr pair)))
                          (cdr pair)))
             (unit-literal (and clause
                                (is-unit-clause clause assignment))))

; Note that (member (- unit-literal) assignment) is false, because of how
; unit-literal is chosen.  So we don't need to consider that case.

        (cond ((not unit-literal)

; This case is surprising.  See the long comment about the previous surprising
; case, above, for a discussion of why we handle surprising cases this way.

               (unit-propagation-error
                (msg "Unit-propagation has failed for index ~x0 because ~
                      ~@1."
                     (car indices)
                     (cond ((null pair)
                            "no formula was found for that index")
                           ((null clause)
                            "that clause had been deleted")
                           (t
                            "that clause is not a unit")))
                formula indices assignment))
              ((eq unit-literal t) ; found contradiction
               t)
              (t (unit-propagation formula
                                   (cdr indices)
                                   (add-to-set unit-literal assignment))))))))

(defthm literalp-is-unit-clause
  (implies (force (literal-listp clause))
           (or (literalp (is-unit-clause clause assignment))
               (booleanp (is-unit-clause clause assignment))))
  :rule-classes :type-prescription)

(defthm clause-or-assignment-p-cdr-hons-assoc-equal
  (let ((clause (cdr (hons-assoc-equal max fal))))
    (implies (and (formula-fal-p fal)
                  (not (deleted-clause-p clause)))
             (clause-or-assignment-p clause))))

(defthm backchain-to-clause-or-assignment-p
  (implies (clause-or-assignment-p clause)
           (and (literal-listp clause)
                (unique-literalsp clause)
                (not (conflicting-literalsp clause))))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm not-member-complement-unit-clause-assignment
  (implies (and (clause-or-assignment-p clause)
                (clause-or-assignment-p assignment))
           (not (member-equal (negate (is-unit-clause clause assignment))
                              assignment)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(verify-guards unit-propagation
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defun remove-literal (literal clause)
  (declare (xargs :guard (and (literalp literal)
                              (clause-or-assignment-p clause))))
  (if (atom clause)
      nil
    (if (equal (car clause) literal)
        (remove-literal literal (cdr clause))
      (cons (car clause)
            (remove-literal literal (cdr clause))))))

(defthm literal-listp-union-equal
  (implies (true-listp x)
           (equal (literal-listp (union-equal x y))
                  (and (literal-listp x)
                       (literal-listp y)))))

(defthm member-equal-remove-literal
  (implies (not (member-equal a x))
           (not (member-equal a (remove-literal b x)))))

(defthm clause-or-assignment-p-remove-literal
  (implies (clause-or-assignment-p y)
           (clause-or-assignment-p (remove-literal x y)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm literal-listp-remove-literal
  (implies (literal-listp x)
           (literal-listp (remove-literal a x))))

(defthm literal-listp-negate-clause-or-assignment
  (implies (literal-listp x)
           (literal-listp (negate-clause-or-assignment x))))

(defthm unique-literalsp-remove-literal
  (implies (unique-literalsp x)
           (unique-literalsp (remove-literal a x))))

(defthm member-equal-negate-clause-or-assignment
  (implies (literalp x1)
           (iff (member-equal x1
                              (negate-clause-or-assignment x2))
                (member-equal (negate x1) x2))))

(defthm member-equal-union-equal
  (iff (member-equal a (union-equal x y))
       (or (member-equal a x)
           (member-equal a y))))

(defthm unique-literalsp-union-equal
  (implies (and (unique-literalsp x)
                (unique-literalsp y))
           (unique-literalsp (union-equal x y))))

(defthm unique-literalsp-negate-clause-or-assignment
  (implies (and (literal-listp x)
                (unique-literalsp x))
           (unique-literalsp (negate-clause-or-assignment x))))

(defstub drat-indices-and-hints-error (index) t)
(defun drat-indices-and-hints-error-on (msg)
  (declare (xargs :guard t))
  (er hard? 'drat-indices-and-hints
      "~@0"
      msg))
(defun drat-indices-and-hints-error-off (msg)
  (declare (xargs :guard t)
           (ignore msg))
  nil)
(defattach drat-indices-and-hints-error drat-indices-and-hints-error-on)

(defun drat-indices-and-hints (index drat-hints)

; Drat-hints is a non-empty alist with decreasing indices, and index is at most
; as large as the first key in alist.  We expect to find index as a key in
; drat-hints.

  (declare (xargs :guard (and (natp index)
                              (drat-hint-listp drat-hints))))
  (cond ((endp drat-hints)
         (mv (prog2$ (drat-indices-and-hints-error
                      (msg "Surprise: never found index ~x0!"
                           index))
                     nil)
             nil))
        ((eql index (caar drat-hints))
         (mv (cdar drat-hints) (cdr drat-hints)))
        ((< index (caar drat-hints))
         (drat-indices-and-hints index (cdr drat-hints)))
        (t
         (mv (prog2$ (drat-indices-and-hints-error
                      (msg "Surprise: index ~x0 exceeds first key in drat-hints, ~x1."
                           index drat-hints))
                     nil)
             nil))))

(defun rat-assignment (assignment nlit clause)

; This is approximately a tail-recursive, optimized version of:

; (union$ assignment
;         (negate-clause-or-assignment
;          (remove-literal nlit clause)))

; However, if a contradiction is discovered, then we return t.

  (declare (xargs :guard
                  (and (clause-or-assignment-p assignment)
                       (literalp nlit)
                       (clause-or-assignment-p clause))
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
  (cond ((endp clause) assignment)
        ((or (eql (car clause) nlit)
             (member (negate (car clause)) assignment))
         (rat-assignment assignment nlit (cdr clause)))
        ((member (car clause) assignment)
         t)
        (t
         (rat-assignment (cons (negate (car clause)) assignment)
                         nlit
                         (cdr clause)))))

(defthm minus-minus
  (implies (acl2-numberp x)
           (equal (- (- x)) x)))

(defthm clause-or-assignment-p-rat-assignment
  (implies (and (clause-or-assignment-p assignment)
                (clause-or-assignment-p clause)
                (not (equal (rat-assignment assignment nlit clause)
                            t)))
           (clause-or-assignment-p
            (rat-assignment assignment nlit clause)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defun RATp1 (index formula nlit drat-hints assignment)

; We think of assignment as being the result of having extended the global
; assignment with the negation of the current proof clause (to check that that
; clause is redundant with respect to formula).

  (declare (xargs :guard (and (natp index)
                              (formula-p formula)
                              (literalp nlit)
                              (drat-hint-listp drat-hints)
                              (clause-or-assignment-p assignment))
                  :verify-guards nil
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
  (if (zp index)
      t
    (let ((next-clause (cdr (hons-get index (formula-fal formula)))))
      (cond
       ((or (deleted-clause-p next-clause)
            (not (member nlit next-clause)))
        (RATp1 (1- index) formula nlit drat-hints assignment))
       (t ; otherwise, we have a RAT clause
        (let ((new-assignment (rat-assignment assignment nlit next-clause)))
          (if (eq new-assignment t)
              (RATp1 (1- index) formula nlit drat-hints assignment)
            (mv-let (indices rest-drat-hints)
              (drat-indices-and-hints index drat-hints)
              (and (eq t
                       (unit-propagation formula indices new-assignment))
                   (RATp1 (1- index) formula nlit rest-drat-hints
                          assignment))))))))))

; Start proof of (verify-guards RATp1).

(defthm not-conflicting-literalsp-negate-clause-or-assignment
  (implies (and (literal-listp x)
                (not (conflicting-literalsp x)))
           (not (conflicting-literalsp (negate-clause-or-assignment x)))))

(defthm clause-or-assignment-p-negate-clause-or-assignment
  (implies (clause-or-assignment-p x)
           (clause-or-assignment-p (negate-clause-or-assignment x)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm clause-or-assignment-p-union-equal
  (implies (and (clause-or-assignment-p x)
                (clause-or-assignment-p y)
                (not (conflicting-literalsp (union-equal x y))))
           (clause-or-assignment-p (union-equal x y)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm clause-or-assignment-p-unit-propagation
  (implies (and (formula-p formula)
                (clause-or-assignment-p x)
                (not (equal (unit-propagation formula indices x) t)))
           (clause-or-assignment-p (unit-propagation formula indices x)))
  :hints (("Goal" :in-theory (enable clause-or-assignment-p))))

(defthm drat-hint-listp-forward-to-alistp
  (implies (drat-hint-listp x)
           (alistp x))
  :rule-classes :type-prescription)

(defthm drat-hint-listp-implies-index-listp
  (implies (drat-hint-listp x)
           (index-listp (car (drat-indices-and-hints index x)))))

(defthm true-listp-lookup-formula-index
  (implies (formula-fal-p x)
           (or (true-listp (cdr (hons-assoc-equal index x)))
               (equal (cdr (hons-assoc-equal index x)) 0)))
  :rule-classes :type-prescription)

(defthm drat-hint-listp-mv-nth-1-drat-indices-and-hints
  (implies (drat-hint-listp x)
           (drat-hint-listp (mv-nth 1 (drat-indices-and-hints index x)))))

(verify-guards RATp1)

(defun RATp (formula literal drat-hints assignment)
  (declare (xargs :guard (and (formula-p formula)
                              (literalp literal)
                              (drat-hint-listp drat-hints)
                              (clause-or-assignment-p assignment))))
  (RATp1 (formula-max formula) formula (negate literal) drat-hints assignment))

(defun verify-clause (formula proof-clause rup-indices drat-hints)
  (declare (xargs :guard (and (formula-p formula)
                              (clause-or-assignment-p proof-clause)
                              (index-listp rup-indices)
                              (drat-hint-listp drat-hints))
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
  (let* ((assignment (negate-clause-or-assignment proof-clause))
         (assignment (unit-propagation formula rup-indices assignment)))
    (or (eq assignment t)
        (and (not (atom proof-clause))
             (RATp formula (car proof-clause) drat-hints assignment)))))

(defun delete-clauses-fal (index-list fal)
  (declare (xargs :guard (index-listp index-list)))
  (cond ((endp index-list) fal)
        (t (delete-clauses-fal
            (cdr index-list)
            (hons-acons (car index-list) *deleted-clause* fal)))))

(defun delete-clauses (index-list formula)
  (declare (xargs :guard (and (index-listp index-list)
                              (formula-p formula))))
  (make-formula (formula-max formula)
                (delete-clauses-fal index-list (formula-fal formula))))

(defun add-proof-clause (index clause formula)
  (declare (xargs :guard (and (posp index)
                              (formula-p formula))))
  (make-formula index
                (hons-acons index clause (formula-fal formula))))

(defun verify-proof (formula proof)
  (declare (xargs :guard (and (formula-p formula)
                              (proofp proof))))
  (if (atom proof)
      t
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (if delete-flg
          (let* ((indices (proof-entry-deletion-indices entry))
                 (new-formula (delete-clauses indices formula)))
            (verify-proof new-formula (cdr proof)))
        (let ((clause (access add-step entry :clause))
              (indices (access add-step entry :rup-indices))
              (drat-hints (access add-step entry :drat-hints)))
          (and (verify-clause formula clause indices drat-hints)
               (let ((index (access add-step entry :index)))
                 (and (or (< (formula-max formula) index)
                          (er hard? 'verify-proof
                              "Index did not exceed previous indices: ~x0"
                              index))
                      (verify-proof (add-proof-clause index clause formula)
                                    (cdr proof))))))))))

(defun proof-contradiction-p (proof)
  (declare (xargs :guard (proofp proof)))
  (if (endp proof)
      nil
    (or (let ((entry (car proof)))
          (and (not (proof-entry-deletion-p entry)) ; addition
               (null (access add-step entry :clause))))
        (proof-contradiction-p (cdr proof)))))

(defun valid-proofp (formula proof incomplete-okp)
  (declare (xargs :guard (formula-p formula)))
  (and (proofp proof)
       (or incomplete-okp
           (proof-contradiction-p proof))
       (verify-proof formula proof)))

; The functions defined below are only relevant to the correctness statement.

(defun refutation-p (proof formula)
  (declare (xargs :guard (formula-p formula)))
  (and (valid-proofp formula proof nil)
       (proof-contradiction-p proof)))

(defun evaluate-formula-fal (max fal assignment)
  (declare (xargs :guard (and (natp max)
                              (formula-fal-p fal)
                              (clause-or-assignment-p assignment))))
  (if (zp max)
      t
    (let ((pair (hons-get max fal)))
      (if (null pair)
          (evaluate-formula-fal (1- max) fal assignment)
        (let ((clause (cdr pair)))
          (if (deleted-clause-p clause)
              (evaluate-formula-fal (1- max) fal assignment)
            (let ((clause-value (evaluate-clause clause assignment)))
              (if (not clause-value)
                  nil
                (let ((remaining-formula-value
                       (evaluate-formula-fal (1- max) fal assignment)))
                  (cond
                   ((null remaining-formula-value) nil)
                   ((undefp clause-value) 0)
                   (t ; else clause-value = t
                    remaining-formula-value)))))))))))

(defun evaluate-formula (formula assignment)
  (declare (xargs :guard (and (formula-p formula)
                              (clause-or-assignment-p assignment))))
  (evaluate-formula-fal (formula-max formula)
                        (formula-fal formula)
                        assignment))

(defun solution-p (assignment formula)
  (declare (xargs :guard (formula-p formula)))
  (and (clause-or-assignment-p assignment)
       (eq (evaluate-formula formula assignment) t)))

(defun-sk satisfiable (formula)
  (exists assignment (solution-p assignment formula)))

; Goal:
#||
(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp proof formula))
           (not (satisfiable formula))))
||#

; Note: At some point we may want to use fast-alist-clean to clean up the
; fast-alist.  This lemma will be helpful in that regard, from
; books/std/alists/fast-alist-clean.lisp:

#||
(defthm hons-assoc-equal-in-fast-alist-clean
  (equal (hons-assoc-equal k (fast-alist-clean x))
         (hons-assoc-equal k x)))
||#
