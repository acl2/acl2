; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

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

(defun duplicate-literal (x)

; This function assumes that there is a duplicate literal in x.

  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      (er hard? 'duplicate-literal
          "Implementation error: Failed to find a duplicate literal!")
    (if (member (car x) (cdr x))
        (car x)
      (duplicate-literal (cdr x)))))

(defun conflicting-literals (x)
  (declare (xargs :guard (literal-listp x)))
  (if (atom x)
      (er hard? 'duplicate-literal
          "Implementation error: Failed to find conflicting literals!")
    (if (member (negate (car x)) (cdr x))
        (car x)
      (conflicting-literals (cdr x)))))

(defun clause-or-assignment-p-error-msg (clause)

; This function assumes that (clause-or-assignment-p clause) is nil.  We return
; a message to be printed after "The formula contains ".

  (declare (xargs :guard t))
  (cond ((not (literal-listp clause))
         (msg "the alleged clause ~x0, which is not a list of literals."
              clause))
        ((not (unique-literalsp clause))
         (msg "the alleged clause ~x0, whcih contains ~x1 as a duplicate literal."
              clause
              (duplicate-literal clause)))
        ((conflicting-literalsp clause)
         (let ((lit (conflicting-literals clause)))
           (msg "the alleged clause ~x0, which contains conflicting literals ~
                 ~x1 and ~x2."
                clause
                lit
                (negate lit))))
        (t (er hard? 'clause-or-assignment-p-error-msg
               "Implementation error: Expected the following to be nil, but ~
                apparently it is not:~|~x0"
               `(clause-or-assignment-p ',clause)))))

(defthm clause-or-assignment-p-forward-to-literal-listp
  (implies (clause-or-assignment-p x)
           (literal-listp x))
  :rule-classes :forward-chaining)

(defthm literal-listp-forward-to-eqlable-listp
  (implies (literal-listp x)
           (eqlable-listp x))
  :rule-classes :forward-chaining)

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

(defun formula-p-error-msg (fal)

; This function expects (formula-p fal) to be nil.

  (declare (xargs :guard t))
  (if (atom fal)
      (msg "The alleged formula is not a true-list")
    (let ((pair (car fal)))
      (cond  ((not (consp pair))
              (msg "A formula is represented internally as a list of pairs, ~
                    but the following is not a pair: ~x0"
                   pair))
             ((not (posp (car pair)))
              (msg "A formula is represented internally as a list of pairs.  ~
                    The following pair is invalid, however, because its first ~
                    element is expected to be a positive integer but is ~
                    not:~|~x0"
                   pair))
             ((and (not (deleted-clause-p (cdr pair)))
                   (not (clause-or-assignment-p (cdr pair))))
              (msg "The formula contains ~@0"
                   (clause-or-assignment-p-error-msg (cdr pair))))
             (t (formula-p-error-msg (cdr fal)))))))

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

(defthm drat-hint-listp-forward-to-alistp
  (implies (drat-hint-listp x)
           (alistp x))
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

; Change the following to defun-inline if you want a bit more performance and
; don't mind the inability to profile this function.  Note that it is illegal
; to profile hons-get.
(defun-notinline my-hons-get (key alist)
  (declare (xargs :guard t))
  (hons-get key alist))

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

(defthm literalp-is-unit-clause
  (implies (force (literal-listp clause))
           (or (literalp (is-unit-clause clause assignment))
               (booleanp (is-unit-clause clause assignment))))
  :rule-classes :type-prescription)

(defthm clause-or-assignment-p-cdr-hons-assoc-equal
  (let ((clause (cdr (hons-assoc-equal index fal))))
    (implies (and (formula-p fal)
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

(defthm literal-listp-negate-clause-or-assignment-rec
  (implies (and (literal-listp x)
                (literal-listp y))
           (literal-listp (negate-clause-or-assignment-rec x y))))

(defthm literal-listp-negate-clause-or-assignment
  (implies (literal-listp x)
           (literal-listp (negate-clause-or-assignment x)))
  :hints (("Goal" :in-theory (enable negate-clause-or-assignment))))

(defthm unique-literalsp-remove-literal
  (implies (unique-literalsp x)
           (unique-literalsp (remove-literal a x))))

(defthm member-equal-negate-clause-or-assignment-rec-lemma
  (implies (member-equal lit x2)
           (member-equal lit
                         (negate-clause-or-assignment-rec x1 x2))))

(defthm member-equal-negate-clause-or-assignment-rec
  (implies (literalp lit)
           (iff (member-equal lit
                              (negate-clause-or-assignment-rec x1 x2))
                (or (member-equal (negate lit) x1)
                    (member-equal lit x2)))))

(defthm member-equal-negate-clause-or-assignment
  (implies (literalp x1)
           (iff (member-equal x1
                              (negate-clause-or-assignment x2))
                (member-equal (negate x1) x2)))
  :hints (("Goal" :in-theory (enable negate-clause-or-assignment))))

(defthm member-equal-union-equal
  (iff (member-equal a (union-equal x y))
       (or (member-equal a x)
           (member-equal a y))))

(defthm unique-literalsp-union-equal
  (implies (and (unique-literalsp x)
                (unique-literalsp y))
           (unique-literalsp (union-equal x y))))

; Start proof of unique-literalsp-negate-clause-or-assignment

(defun intersectp-complementary (x y)
  (cond ((endp x) nil)
        (t (or (member-equal (negate (car x)) y)
               (intersectp-complementary (cdr x) y)))))

(defthm intersectp-complementary-cons-2
  (implies (literalp a)
           (iff (intersectp-complementary x (cons a y))
                (or (member-equal (negate a) x)
                    (intersectp-complementary x y))))
  :hints (("Goal" :in-theory (disable (force)))))

(defthm negate-negate ; too timid at this point to include an arithmetic book
  (implies (literalp lit)
           (equal (negate (negate lit))
                  lit)))

(defthm unique-literalsp-negate-clause-or-assignment-rec
  (implies (and (literal-listp x)
                (unique-literalsp x)
                (unique-literalsp y)
                (not (intersectp-complementary x y)))
           (unique-literalsp (negate-clause-or-assignment-rec x y)))
  :hints (("Goal"
           :induct (negate-clause-or-assignment-rec x y))))

(defthm not-intersectp-complementary-nil
  (not (intersectp-complementary x nil)))

(defthm unique-literalsp-negate-clause-or-assignment
  (implies (and (literal-listp x)
                (unique-literalsp x))
           (unique-literalsp (negate-clause-or-assignment x)))
  :hints (("Goal" :in-theory (enable negate-clause-or-assignment))))

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

(defun RATp1 (alist formula nlit drat-hints assignment)

; We think of assignment as being the result of having extended the global
; assignment with the negation of the current proof clause (to check that that
; clause is redundant with respect to formula).

  (declare (xargs :guard (and (formula-p alist)
                              (formula-p formula)
                              (literalp nlit)
                              (drat-hint-listp drat-hints)
                              (clause-or-assignment-p assignment))
                  :verify-guards nil
                  :guard-hints
                  (("Goal" :in-theory (enable clause-or-assignment-p)))))
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

; Start proof of (verify-guards RATp1).

; Start proof of not-conflicting-literalsp-negate-clause-or-assignment

(defthm intersectp-equal-cons-2
  (iff (intersectp-equal x (cons a y))
       (or (member-equal a x)
           (intersectp-equal x y))))

(defthm not-conflicting-literalsp-negate-clause-or-assignment-rec
  (implies (and (literal-listp x)
                (not (conflicting-literalsp x))
                (not (conflicting-literalsp y))
                (not (intersectp x y)))
           (not (conflicting-literalsp (negate-clause-or-assignment-rec x y))))
  :hints (("Goal" :induct (negate-clause-or-assignment-rec x y))))

(defthm not-intersectp-equal-nil
  (not (intersectp-equal x nil)))

(defthm not-conflicting-literalsp-negate-clause-or-assignment
  (implies (and (literal-listp x)
                (not (conflicting-literalsp x)))
           (not (conflicting-literalsp (negate-clause-or-assignment x))))
  :hints (("Goal" :in-theory (enable negate-clause-or-assignment))))

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

(defthm true-listp-lookup-formula-index
  (implies (formula-p x)
           (or (true-listp (cdr (hons-assoc-equal index x)))
               (equal (cdr (hons-assoc-equal index x)) *deleted-clause*)))
  :rule-classes :type-prescription)

(verify-guards RATp1)

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

(defthm formula-p-forward-to-alistp
  (implies (formula-p x)
           (alistp x))
  :rule-classes :forward-chaining)

(defthm alistp-fast-alist-fork
  (implies (and (alistp x)
                (alistp y))
           (alistp (fast-alist-fork x y))))

(local
 (defthm cdr-last-of-alistp
   (implies (alistp x)
            (equal (cdr (last x))
                   nil))))

(defund shrink-formula (fal)
  (declare (xargs :guard (formula-p fal)))
  (let ((fal2 (fast-alist-clean fal)))
    (fast-alist-free-on-exit fal2 (remove-deleted-clauses fal2 nil))))

(defun maybe-shrink-formula (ncls ndel formula factor)

; This function returns ncls unchanged, simply so that verify-clause can return
; directly by calling this function.

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

(defthm formula-p-remove-deleted-clauses
  (implies (and (formula-p fal1)
                (formula-p fal2))
           (formula-p (remove-deleted-clauses fal1 fal2))))

(defthm formula-p-fast-alist-fork
  (implies (and (formula-p fal1)
                (formula-p fal2))
           (formula-p (fast-alist-fork fal1 fal2))))

(defthm formula-p-shrink-formula
  (implies (formula-p fal)
           (formula-p (shrink-formula fal)))
  :hints (("Goal" :in-theory (enable shrink-formula))))

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

(in-theory (disable maybe-shrink-formula formula-truep satisfiable))

; Goal:
#||
(defthm main-theorem
  (implies (and (formula-p formula)
                (refutation-p proof formula))
           (not (satisfiable formula))))
||#
