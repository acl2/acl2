; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

; This work is derived from earlier work by Nathan Wetzler.  See
; lrat-checker.lisp.  Here, we give just the definitions in support of the
; checker and the proved soundness theorem.

; See ../tests/README for tests.

(in-package "LRAT")

(local (include-book "lrat-checker"))
(local (include-book "soundness"))

; The following is only to fool the dependency checker into certifying the
; parser when this top.lisp book is certified by the build system (cert.pl).
; There is no need to include the book here for defining the checker and
; proving soundness.
#||
(local (include-book "lrat-parser"))
||#

(set-enforce-redundancy t)

(defun literalp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (not (equal x 0))))

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

(defconst *deleted-clause* :deleted)

(defmacro deleted-clause-p (val)
  `(eq ,val *deleted-clause*))

(defun formula-p (fal)

; We recognize nil-terminated fast-alists (applicative hash tables), such that
; that every index is bound to a clause or *deleted-clause*.

  (declare (xargs :guard t))
  (if (atom fal)
      (null fal)
    (let ((pair (car fal)))
      (and (consp pair)
           (posp (car pair))
           (let ((val (cdr pair)))
             (or (deleted-clause-p val)
                 (clause-or-assignment-p val)))
           (formula-p (cdr fal))))))

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

(defun negate-clause-or-assignment-rec (clause acc)
  (declare (xargs :guard (and (literal-listp clause)
                              (literal-listp acc))))
  (if (endp clause)
      acc
    (negate-clause-or-assignment-rec (cdr clause)
                                     (cons (negate (car clause))
                                           acc))))

(defund negate-clause-or-assignment (clause)

; When we originally proved soundness for this checker, we wrote
; negate-clause-or-assignment using a straightforward recursion (not
; tail-recursion).  However, when we tried to prove a correspondence theorem
; between this checker and one with stobj-based assignments, we ran into
; trouble because the order of literals in this assignment was reversed from
; what is obtained by the stack.  (Of course, we could have reversed what we
; produced from the stack; but then rat-assignment, which is already
; tail-recursive for this checker, would have things backwards instead.)

  (declare (xargs :guard (literal-listp clause)))
  (negate-clause-or-assignment-rec clause nil))

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

(defun is-unit-clause (clause assignment)

; If clause is a (pseudo) unit clause under assignment, return the unique
; unassigned literal (the others will be false).  Otherwise return nil unless
; the clause is false under assignment, in which case return t.

  (declare (xargs :guard (and (clause-or-assignment-p clause)
                              (clause-or-assignment-p assignment))))
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

(defmacro unit-propagation-error (msg formula indices assignment)
  `(prog2$ (er hard? 'unit-propagation "~@0" ,msg)
           (unit-propagation ,formula (cdr ,indices) ,assignment)))

(defun-notinline my-hons-get (key alist)
  (declare (xargs :guard t))
  (hons-get key alist))

(defun unit-propagation (formula indices assignment)

; Return an extension of assignment by unit-propagation restricted to the given
; indices in formula, except that if a contradiction is found, return t
; instead.

  (declare (xargs :guard (and (formula-p formula)
                              (index-listp indices)
                              (clause-or-assignment-p assignment))))
  (cond
   ((endp indices) assignment)
   (t (let* ((pair (my-hons-get (car indices) formula))
             (clause (and pair
                          (not (deleted-clause-p (cdr pair)))
                          (cdr pair)))
             (unit-literal (and clause
                                (is-unit-clause clause assignment))))

; Note that (member (- unit-literal) assignment) is false, because of how
; unit-literal is chosen.  So we don't need to consider that case.

        (cond ((not unit-literal)

; This is a surprising case.  It is tempting simply to return
; assignment (hence failing to produce t).  However, it seems that would cause
; monotonicity to fail (unit-propagation-monotone), so reasoning would be more
; contorted: do all the reasoning about a version that recurs here (as we now
; do), and then fix the proof by connecting the two versions.  Instead, we go
; ahead and recur, but cause an error if we encounter this situation.

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

(defun remove-literal (literal clause)
  (declare (xargs :guard (and (literalp literal)
                              (clause-or-assignment-p clause))))
  (if (atom clause)
      nil
    (if (equal (car clause) literal)
        (remove-literal literal (cdr clause))
      (cons (car clause)
            (remove-literal literal (cdr clause))))))

(defun rat-assignment (assignment nlit clause)

; This is approximately a tail-recursive, optimized version of:

; (union$ assignment
;         (negate-clause-or-assignment
;          (remove-literal nlit clause)))

; However, if a contradiction is discovered, then we return t.

  (declare (xargs :guard
                  (and (clause-or-assignment-p assignment)
                       (literalp nlit)
                       (clause-or-assignment-p clause))))
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

(defun RATp1 (alist formula nlit drat-hints assignment)

; We think of assignment as being the result of having extended the global
; assignment with the negation of the current proof clause (to check that that
; clause is redundant with respect to formula).

  (declare (xargs :guard (and (formula-p alist)
                              (formula-p formula)
                              (literalp nlit)
                              (drat-hint-listp drat-hints)
                              (clause-or-assignment-p assignment))))
  (if (endp alist)
      t
    (let* ((index (caar alist))
           (clause (cdar alist)))
      (cond
       ((deleted-clause-p clause)
        (RATp1 (cdr alist) formula nlit drat-hints assignment))
       ((eql index (caar drat-hints)) ; perform RAT
        (let ((new-assignment (rat-assignment assignment nlit clause)))
          (cond
           ((eq new-assignment t)
            (RATp1 (cdr alist) formula nlit (cdr drat-hints) assignment))
           ((eq t
                (unit-propagation formula
                                  (cdar drat-hints)
                                  new-assignment))
            (RATp1 (cdr alist) formula nlit (cdr drat-hints)
                   assignment))
           (t ; error
            (list 'unit-propagation-failure index clause nlit)))))
       ((or (not (member nlit clause))
            (deleted-clause-p (cdr (my-hons-get index formula))))
        (RATp1 (cdr alist) formula nlit drat-hints assignment))
       (t ; error
        (list 'index-failure index clause nlit))))))

(defun RATp (formula literal drat-hints assignment)
  (declare (xargs :guard (and (formula-p formula)
                              (literalp literal)
                              (drat-hint-listp drat-hints)
                              (clause-or-assignment-p assignment))))
  (RATp1 formula formula (negate literal) drat-hints assignment))

(defun remove-deleted-clauses (fal acc)
  (declare (xargs :guard (alistp fal)))
  (cond ((endp fal) (make-fast-alist acc))
        (t (remove-deleted-clauses (cdr fal)
                                   (if (deleted-clause-p (cdar fal))
                                       acc
                                     (cons (car fal) acc))))))

(defun shrink-formula (fal)
  (declare (xargs :guard (formula-p fal)))
  (let ((fal2 (fast-alist-clean fal)))
    (fast-alist-free-on-exit fal2 (remove-deleted-clauses fal2 nil))))

(defun maybe-shrink-formula (ncls ndel formula factor)
  (declare (xargs :guard (and (integerp ncls) ; really natp; see verify-clause
                              (natp ndel)
                              (formula-p formula)
                              (rationalp factor))))
  (cond ((> ndel (* factor ncls))
         (let ((new-formula (shrink-formula formula)))
           #+skip ; This is a nice check but we don't want to pay the price.
           (assert$
            (or (eql ncls (fast-alist-len new-formula))
                (cw "ERROR: ncls = ~x0, (fast-alist-len new-formula) = ~x1"
                    ncls (fast-alist-len new-formula)))
            (mv ncls 0 new-formula))
           (mv ncls 0 new-formula)))
        (t (mv ncls ndel formula))))

(defun verify-clause (formula add-step ncls ndel)
  (declare (xargs :guard
                  (and (formula-p formula)
                       (add-step-p add-step)
                       (integerp ncls) ; really natp; see verify-proof-rec
                       (natp ndel))
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
  (let* ((proof-clause (access add-step add-step :clause))
         (assignment (negate-clause-or-assignment proof-clause))
         (rup-indices (access add-step add-step :rup-indices))
         (assignment (unit-propagation formula rup-indices assignment)))
    (cond
     ((eq assignment t)
      (maybe-shrink-formula ncls ndel formula
; shrink when ndel > 10 * ncls; factor can be changed
                            10))
     ((consp proof-clause)
      (mv-let
        (ncls ndel formula)
        (maybe-shrink-formula ncls ndel formula
; shrink when ndel > 1/3 * ncls; factor can be changed
                              1/3)
        (cond
         ((eq (RATp formula (car proof-clause)
                    (access add-step add-step :drat-hints)
                    assignment)
              t)
          (mv ncls ndel formula))
         (t

; We could have let-bound the RATp call above rather than making it again
; below.  But this case is presumably very rare, so we avoid any possibility of
; slowing down the normal case with a let-binding.

          (prog2$
           (let* ((current-index (access add-step add-step :index))
                  (er-type/index/clause/nlit
                   (RATp formula (car proof-clause)
                         (access add-step add-step :drat-hints)
                         assignment))
                  (er-type (nth 0 er-type/index/clause/nlit))
                  (earlier-index (nth 1 er-type/index/clause/nlit))
                  (clause (nth 2 er-type/index/clause/nlit))
                  (nlit (nth 3 er-type/index/clause/nlit)))
             (declare (ignore clause))
             (case er-type
               (unit-propagation-failure
                (er hard? 'verify-clause
                    "Unit propagation failure has cause the RAT check to fail ~
                     when attempting to add proof clause #~x0 for earlier RAT ~
                     clause #~x1."
                    current-index earlier-index))
               (index-failure
                (er hard? 'verify-clause
                    "The RAT check has failed for proof clause #~x0, because ~
                     literal ~x1 belongs to earlier proof clause #~x2 but no ~
                     hint for that clause is given with proof clause #~x0."
                    current-index nlit earlier-index))
               (otherwise ; surprising; RATp1 and this function are out of sync
                (er hard? 'verify-clause
                    "Unexpected error for RAT check, proof clause #~x0; the ~
                     error is probably a true error but the checker needs to ~
                     be fixed to print a more useful error in this case."
                    current-index))))
           (mv nil nil nil))))))
     (t (prog2$
         (er hard? 'verify-clause
             "The unit-propagation check failed at proof clause #~x0, which ~
              is the empty clause."
             (access add-step add-step :index))
         (mv nil nil nil))))))

(defun delete-clauses (index-list fal)
  (declare (xargs :guard (index-listp index-list)))
  (cond ((endp index-list) fal)
        (t (delete-clauses
            (cdr index-list)
            (hons-acons (car index-list) *deleted-clause* fal)))))

(defun add-proof-clause (index clause formula)
  (declare (xargs :guard (and (posp index)
                              (formula-p formula))))
  (hons-acons index clause formula))

(defun verify-proof-rec (ncls ndel formula proof)
  (declare (xargs :guard (and (integerp ncls) ; really natp; see comment below
                              (natp ndel)
                              (formula-p formula)
                              (proofp proof))))
  (cond
   ((atom proof) t)
   (t
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (cond
       (delete-flg
        (let* ((indices (proof-entry-deletion-indices entry))
               (new-formula (delete-clauses indices formula))
               (len (length indices))
               (ncls

; We expect that (<= len ncls).  It is tempting to assert that here (with
; assert$), but it's not necessary so we avoid the overhead (mostly in proof,
; but perhaps also a bit in execution).

                (- ncls len))
               (ndel (+ ndel len)))
          (verify-proof-rec ncls ndel new-formula (cdr proof))))
       (t ; addition
        (mv-let (ncls ndel new-formula)
          (verify-clause formula entry ncls ndel)
          (and ncls ; success
               (verify-proof-rec
                (1+ ncls)
                ndel
                (add-proof-clause (access add-step entry :index)
                                  (access add-step entry :clause)
                                  new-formula)
                (cdr proof))))))))))

(defun verify-proof (formula proof)
  (declare (xargs :guard (and (formula-p formula)
                              (proofp proof))))
  (verify-proof-rec (fast-alist-len formula)
                    0
                    formula
                    proof))

(defun proof-contradiction-p (proof)
  (declare (xargs :guard (proofp proof)))
  (if (endp proof)
      nil
    (or (let ((entry (car proof)))
          (and (not (proof-entry-deletion-p entry)) ; addition
               (null (access add-step entry :clause))))
        (proof-contradiction-p (cdr proof)))))

(defun valid-proofp (formula proof)

; This function returns two Boolean values, (mv valid-p contr-p), where valid-p
; is true when the given proof is valid for the given formula, and contr-p is
; true when the proof contains an addition step with the empty clause.
; Except, if proof is not syntactically valid (i.e., satisfies proofp), then we
; return (mv nil nil).

  (declare (xargs :guard (formula-p formula)))
  (let ((p (proofp proof)))
    (mv (and p (verify-proof formula proof))
        (and p (proof-contradiction-p proof)))))

; The functions defined below are only relevant to the correctness statement.

(defun refutation-p (proof formula)
  (declare (xargs :guard (formula-p formula)))
  (mv-let (v c)
    (valid-proofp formula proof)
    (and v c)))

(defun-sk formula-truep (formula assignment)
  (forall index
          (let ((pair (hons-get index formula)))
            (implies (and pair
                          (not (deleted-clause-p (cdr pair))))
                     (equal (evaluate-clause (cdr pair) assignment)
                            t)))))

(defun solution-p (assignment formula)
  (and (clause-or-assignment-p assignment)
       (formula-truep formula assignment)))

(defun-sk satisfiable (formula)
  (exists assignment (solution-p assignment formula)))

(defthm main-theorem-list-based
  (implies (and (formula-p formula)
                (refutation-p proof formula))
           (not (satisfiable formula))))
