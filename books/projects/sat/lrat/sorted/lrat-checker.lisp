; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This work is based on Nathan Wetzler's RAT checker work in ACL2 community
; books directory books/projects/sat/proof-checker-itp13/.  Here we accommodate
; a more recent input proof format to speed up unit propagation and add
; deletion (to obtain a DRAT checker).

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.  It provides a slight modification of
; ../stobj-based/lrat-checker.lisp; here we assume that each clause in a proof
; file is sorted except perhaps for the first literal.

(in-package "LRAT")

(local (include-book "../list-based/lrat-checker"))
(local (include-book "../stobj-based/lrat-checker"))
(local (include-book "lrat-checker-support"))

(set-enforce-redundancy t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code from ../list-based/lrat-checker.lisp:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defun intersectp-complementary (x y)
  (cond ((endp x) nil)
        (t (or (member-equal (negate (car x)) y)
               (intersectp-complementary (cdr x) y)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code from ../stobj-based/lrat-checker.lisp:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "std/util/bstar" :dir :system)

(defstobj a$

; Note that a$stk contains positive integers, i.e., variables; its entries are
; indices into a$arr.

  (a$ptr :type (integer 0 *) :initially 0) ; stack pointer
  (a$stk :type (array t (1)) :resizable t) ; stack
  (a$arr :type (array t (1)) ; array of 0, t, nil
         :initially 0
         :resizable t)
  :renaming ((a$arrp a$arrp-weak)
             (a$p a$p-weak))
  :non-memoizable t
  :inline t)

; Now that assignments are about to be stored in our new stobj, let's rename
; clause-or-assignment-p to the now-more-precise name, clausep.
(defmacro clausep (x)
  `(clause-or-assignment-p ,x))

(defmacro varp (x)
  `(posp ,x))

(defun varp$ (var a$)
  (declare (xargs :stobjs a$ :guard t))
  (and (varp var)
       (< (abs var) (a$arr-length a$))))

(defun literalp$ (lit a$)
  (declare (xargs :stobjs a$ :guard t))
  (and (literalp lit)
       (< (abs lit) (a$arr-length a$))))

(defun literal-listp$ (x a$)
  (declare (xargs :stobjs a$ :guard t))
  (if (atom x)
      (null x)
    (and (literalp$ (car x) a$)
         (literal-listp$ (cdr x) a$))))

(defun clausep$ (x a$)
  (declare (xargs :stobjs a$ :guard t))
  (and (literal-listp$ x a$)
       (unique-literalsp x)
       (not (conflicting-literalsp x))))

(defun find-var-on-stk (var i a$)

; Return t if variable var = (a$stki j a$) for some j < i, else nil.

  (declare (xargs :stobjs a$
                  :guard (and (varp var)
                              (natp i)
                              (<= i (a$ptr a$))
                              (<= (a$ptr a$) (a$stk-length a$)))))
  (cond ((zp i) nil)
        (t (let* ((i (1- i))
                  (var2 (a$stki i a$)))
             (cond
              ((eql var var2) t)
              (t (find-var-on-stk var i a$)))))))

(defun good-stk-p (i a$)

; This predicate holds when (varp$ (a$stk j a$) a$) is true for all j < i and
; moreover, there are no duplicate variables (a$stk j1 a$) = (a$stk j2 a$) for
; distinct j1, j2 < i.  Here i is initially the (a$ptr a$).

  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$ptr a$))
                              (<= (a$ptr a$) (a$stk-length a$)))))
  (cond ((zp i)
         t)
        (t (let* ((i (1- i))
                  (var (a$stki i a$)))
             (and (varp$ var a$)
                  (not (find-var-on-stk var i a$))
                  (good-stk-p i a$))))))

(defun arr-matches-stk (i a$)

; Check whether for all 0 < j < i, the (a$arri j a$) is boolean iff j is on the
; stk of a$.

  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$arr-length a$))
                              (<= (a$ptr a$) (a$stk-length a$)))))
  (cond ((or (zp i) (= i 1))
         t)
        (t (let ((var (1- i)))
             (and (eq (booleanp (a$arri var a$))
                      (find-var-on-stk var (a$ptr a$) a$))
                  (arr-matches-stk var a$))))))

(defun a$arrp-rec (i a$)
  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$arr-length a$)))))

; Check that every value below i in a$arr is a Boolean or 0.  Actually we don't
; need to check the value at index 0, since that is unused; but for simplicity
; (canonicity, maybe) let's check that too.

  (cond ((zp i) t)
        (t (let* ((i (1- i))
                  (v (a$arri i a$)))
             (and (or (booleanp v)
                      (eql v 0))
                  (a$arrp-rec i a$))))))

(defun a$arrp (a$)
  (declare (xargs :stobjs a$))
  (a$arrp-rec (a$arr-length a$) a$))

(defun a$p (a$)

; From the defstobj form for a$, specifically from the definition of a$ptrp, we
; know that (a$ptr a) is a natp.

; Note that a$ptr is one more than the maximum valid index in a$stk; it is the
; index where we would place a variable for the next literal to be put into the
; assignment.  Consider the following example to understand the relations
; below.  Let the variables be 1, 2, and 3.  Thus (a$stk-length a$) = 3 so that
; there is room for one literal for each of these variables, and (a$arr-length
; a$) = 4 since the maximum array index is 3.  In the case that the stack is
; full, the stack has one literal on it for each of these variables, in which
; case a$ptr is 3, which is an illegal place to place the next variable --
; which is fine, since the stack is full.

  (declare (xargs :stobjs a$))
  (and (a$p-weak a$)
       (<= (a$ptr a$) (a$stk-length a$))
       (equal (a$arr-length a$) (1+ (a$stk-length a$)))
       (good-stk-p (a$ptr a$) a$)
       (a$arrp a$)
       (arr-matches-stk (a$arr-length a$) a$)))

(defun-inline negate-value (val)
  (declare (xargs :guard t))
  (if (booleanp val) (not val) val))

(defun-inline evaluate-literal$ (lit a$)
  (declare (xargs :stobjs a$
                  :guard (literalp$ lit a$)))
  (if (< 0 lit)
      (a$arri lit a$)
    (negate-value (a$arri (negate lit) a$))))

(defun push-literal (lit a$)

; !! Possible future optimization:

; We may also want an optimized version of this function that assumes that lit
; is not already assigned.  There could be at least two applications: when we
; create an assignment from a clause by pushing (successively unassigned)
; literals onto the empty stack, and probably also in unit-propagation since we
; only call push-literal when the literal is unassigned (would need to think
; through if that's really the case).  Then the two tests below, (eq old t) and
; (eq old nil), would become part of the guard.  The two versions could
; trivially be proved equal under the assumption of that strengthened guard.

  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (literalp$ lit a$))
                  :verify-guards nil))
  (let* ((var (abs lit))
         (old (a$arri var a$))
         (lit-posp (eql var lit)))
    (cond
     ((eq old t)
      (mv (not lit-posp) a$))
     ((eq old nil)
      (mv lit-posp a$))
     (t (let* ((ptr (a$ptr a$))
               (a$ (update-a$stki ptr var a$))
               (a$ (update-a$ptr (1+ ptr) a$))
               (a$ (update-a$arri var lit-posp a$)))
          (mv nil a$))))))

(verify-guards push-literal)

(defun negate-clause (clause a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (clausep$ clause a$))
                  :guard-hints (("Goal" :in-theory (enable clausep$)))))
  (cond ((atom clause)
         (mv nil a$))
        (t (mv-let (flg a$)
             (push-literal (negate (car clause)) a$)
             (cond (flg (mv flg a$))
                   (t (negate-clause (cdr clause) a$)))))))

(defun evaluate-clause$ (clause a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (clausep$ clause a$))
                  :verify-guards nil))
  (if (atom clause)
      nil
    (let* ((literal (car clause))
           (literal-value (evaluate-literal$ literal a$)))
      (if (eq literal-value t)
          t
        (let* ((remaining-clause (cdr clause))
               (remaining-clause-value (evaluate-clause$ remaining-clause
                                                        a$)))
          (cond
           ((eq remaining-clause-value t) t)
           ((undefp literal-value) 0)
           (t remaining-clause-value)))))))

(verify-guards evaluate-clause$)

(defun is-unit-clause$ (clause a$)

; If clause is a (pseudo) unit clause under assignment, return the unique
; unassigned literal (the others will be false).  Otherwise return nil unless
; the clause is false under assignment, in which case return t.

  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (clausep$ clause a$))))
  (if (atom clause)
      t ; top-level clause is false under assignment
    (let ((val (evaluate-literal$ (car clause) a$)))
      (cond
       ((eq val t) nil)
       ((undefp val)
        (if (null (evaluate-clause$ (cdr clause) a$))
            (car clause)
          nil))
       (t ; (null val)
        (is-unit-clause$ (cdr clause) a$))))))

(defmacro unit-propagation$-error$ (msg formula indices a$)
  `(prog2$ (er hard? 'unit-propagation "~@0" ,msg)
           (unit-propagation$ ,formula (cdr ,indices) ,a$)))

(defun formula-p$ (formula a$)

; We recognize nil-terminated fast-alists (applicative hash tables), such that
; that every index is bound to a clause or *deleted-clause*.

  (declare (xargs :stobjs a$ :guard (a$p a$)))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (let ((val (cdr pair)))
             (or (deleted-clause-p val)
                 (clausep$ val a$)))
           (formula-p$ (cdr formula) a$)))))

(defun unit-propagation$ (formula indices a$)

; Extend a$ by unit-propagation$ restricted to the given indices in formula.
; Return (mv flg a$) where flg indicates whether a contradiction is found.

  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (formula-p$ formula a$)
                              (index-listp indices))
                  :verify-guards nil))
  (cond
   ((endp indices) (mv nil a$))
   (t (let* ((pair (my-hons-get (car indices) formula))
             (clause (and pair
                          (not (deleted-clause-p (cdr pair)))
                          (cdr pair)))
             (unit-literal (and clause
                                (is-unit-clause$ clause a$))))

; Note that (member (- unit-literal) assignment) is false, because of how
; unit-literal is chosen.  So we don't need to consider that case.

        (cond ((not unit-literal)

; This is a surprising case.  It is tempting simply to return
; assignment (hence failing to produce t).  However, it seems that would cause
; monotonicity to fail (unit-propagation$-monotone), so reasoning would be more
; contorted: do all the reasoning about a version that recurs here (as we now
; do), and then fix the proof by connecting the two versions.  Instead, we go
; ahead and recur, but cause an error if we encounter this situation.

               (unit-propagation$-error$
                (msg "unit-propagation$ has failed for index ~x0 because ~@1."
                     (car indices)
                     (cond ((null pair)
                            "no formula was found for that index")
                           ((null clause)
                            "that clause had been deleted")
                           (t
                            "that clause is not a unit")))
                formula indices a$))
              ((eq unit-literal t) ; found contradiction
               (mv t a$))
              (t (mv-let (flg a$)
                   (push-literal unit-literal a$)
                   (assert$
                    (null flg)
                    (unit-propagation$ formula (cdr indices) a$)))))))))

(verify-guards unit-propagation$)

(defun rat-assignment$ (a$ nlit clause)

; This is approximately a tail-recursive, optimized version of:

; (union$ assignment
;         (negate-clause-or-assignment
;          (remove-literal nlit clause)))

; However, if a contradiction is discovered, then we return t.

  (declare (xargs :stobjs a$
                  :guard
                  (and (a$p a$)
                       (literalp$ nlit a$)
                       (clausep$ clause a$))))
  (cond ((endp clause) (mv nil a$))
        ((eql (car clause) nlit)
         (rat-assignment$ a$ nlit (cdr clause)))
        (t (mv-let (flg a$)
             (push-literal (negate (car clause)) a$)
             (cond (flg (mv flg a$))
                   (t (rat-assignment$ a$ nlit (cdr clause))))))))

(defun pop-literals (old-ptr a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (natp old-ptr)
                              (<= old-ptr (a$ptr a$)))
                  :verify-guards nil
                  :measure (nfix (a$ptr a$))
                  :hints (("Goal" :in-theory (enable a$p)))))
  (cond
   ((and (mbt (and (a$p a$)
                   (natp old-ptr)
                   (<= old-ptr (a$ptr a$))))
         (not (= old-ptr (a$ptr a$))))
    (let* ((index (1- (a$ptr a$)))
           (var (a$stki index a$))
           (a$ (update-a$ptr index a$))
           (a$ (update-a$arri var 0 a$)))
      (pop-literals old-ptr a$)))
   (t a$)))

(verify-guards pop-literals)

(defun RATp1$ (alist formula nlit drat-hints a$)

; We think of assignment as being the result of having extended the global
; assignment with the negation of the current proof clause (to check that that
; clause is redundant with respect to formula).

  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (formula-p$ alist a$)
                              (formula-p$ formula a$)
                              (literalp$ nlit a$)
                              (drat-hint-listp drat-hints))
                  :verify-guards nil))
  (if (endp alist)
      (mv t a$)
    (let* ((index (caar alist))
           (clause (cdar alist)))
      (cond
       ((deleted-clause-p clause)
        (RATp1$ (cdr alist) formula nlit drat-hints a$))
       ((eql index (caar drat-hints)) ; perform RAT
        (b* ((old-ptr (a$ptr a$))
             ((mv flg a$) (rat-assignment$ a$ nlit clause)))
          (cond
           (flg (let ((a$ (pop-literals old-ptr a$)))
                  (RATp1$ (cdr alist) formula nlit (cdr drat-hints) a$)))
           (t (mv-let
                (flg a$)
                (unit-propagation$ formula (cdar drat-hints) a$)
                (let ((a$ (pop-literals old-ptr a$)))
                  (cond
                   (flg (RATp1$ (cdr alist) formula nlit (cdr drat-hints) a$))
                   (t ; error
                    (mv (list 'unit-propagation-failure index clause nlit)
                        a$)))))))))
       ((or (not (member nlit clause))
            (deleted-clause-p (cdr (my-hons-get index formula))))
        (RATp1$ (cdr alist) formula nlit drat-hints a$))
       (t ; error
        (mv (list 'index-failure index clause nlit)
            a$))))))

(verify-guards ratp1$
  :hints (("Goal" :in-theory (enable formula-p$))))

(defun RATp$ (formula literal drat-hints a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (formula-p$ formula a$)
                              (literalp$ literal a$)
                              (drat-hint-listp drat-hints))))
  (RATp1$ formula formula (negate literal) drat-hints a$))

(defun verify-clause$ (formula add-step ncls ndel a$)

; In the normal case this function returns (mv ncls ndel formula a$) for new
; ncls, ndel, formula, and a$.  Otherwise it returns (mv nil _ formula a$)
; where formula is unchanged, but in that case a hard error occurs.  Note that
; a$ptr is the same for the input and output a$.

  (declare (xargs :stobjs a$
                  :guard
                  (and (a$p a$)

; The following is necessary for proof that follows below, but perhaps it can
; be eliminated if we also eliminate the corresponding conjunct from other
; guards below.  It will then likely be necessary to prove that a$ptr can only
; increase with various operations, in particular, unit-propagation$ and
; negate-clause.  That shouldn't be difficult (in fact, such lemmas might be
; somewhere in this book already).  However, it seems harmless to leave this
; conjunct in guards.

                       (= (a$ptr a$) 0)
                       (formula-p$ formula a$)
                       (add-step-p add-step)
                       (clausep$ (access add-step add-step :clause) a$)
                       (integerp ncls) ; really natp; see verify-proof-rec
                       (natp ndel))
                  :verify-guards nil))
  (b* ((proof-clause (access add-step add-step :clause))
       (old-ptr (a$ptr a$))
       ((mv flg0 a$) (negate-clause proof-clause a$))
       ((when flg0) ; Shouldn't happen
        (prog2$ (er hard? 'verify-clause$
                    "Implementation error?!  Note that a$ptr is ~x0."
                    (a$ptr a$))
                (let ((a$ (pop-literals old-ptr a$)))
                  (mv nil nil nil a$))))
       (rup-indices (access add-step add-step :rup-indices))
       ((mv flg a$) (unit-propagation$ formula rup-indices a$)))
    (cond
     ((eq flg t)
      (b* ((a$ (pop-literals old-ptr a$))
           ((mv ncls nlit new-formula)
            (maybe-shrink-formula ncls ndel formula
; shrink when ndel > 10 * ncls; factor can be changed
                                  10)))
        (mv ncls nlit new-formula a$)))
     ((consp proof-clause)
      (b* (((mv ncls ndel formula)
            (maybe-shrink-formula ncls ndel formula
; shrink when ndel > 1/3 * ncls; factor can be changed
                                  1/3))
           ((mv flg a$)
            (RATp$ formula (car proof-clause)
                   (access add-step add-step :drat-hints)
                   a$))
           (a$ (pop-literals old-ptr a$)))
        (cond
         ((eq flg t)
          (mv ncls ndel formula a$))
         (t (prog2$
             (b* ((current-index (access add-step add-step :index))
                  ((list er-type earlier-index & nlit) flg))
               (case er-type
                 (unit-propagation-failure
                  (er hard? 'verify-clause$
                      "Unit propagation failure has caused the RAT check to ~
                       fail when attempting to add proof clause #~x0 for ~
                       earlier RAT clause #~x1."
                      current-index earlier-index))
                 (index-failure
                  (er hard? 'verify-clause$
                      "The RAT check has failed for proof clause #~x0, ~
                       because literal ~x1 belongs to earlier proof clause ~
                       #~x2 but no hint for that clause is given with proof ~
                       clause #~x0."
                      current-index nlit earlier-index))
                 (otherwise ; surprising; RATp1$ and this function are out of sync
                  (er hard? 'verify-clause$
                      "Unexpected error for RAT check, proof clause #~x0; the ~
                       error is probably a true error but the checker needs ~
                       to be fixed to print a more useful error in this case."
                      current-index))))
             (mv nil nil nil a$))))))
     (t (prog2$
         (er hard? 'verify-clause$
             "The unit-propagation$ check failed at proof clause #~x0, which ~
              is the empty clause."
             (access add-step add-step :index))
         (b* ((a$ (pop-literals old-ptr a$)))
           (mv nil nil nil a$)))))))

(verify-guards verify-clause$)

(defun proofp$ (proof a$)

; We could make this predicate more efficient by folding the clausep$ check
; into a suitable strengthening proof-entry-p$ of proof-entry-p.  But this
; predicate is only for proof purposes, not to be executed.

  (declare (xargs :stobjs a$
                  :guard (a$p a$)))
  (if (atom proof)
      (null proof)
    (and (proof-entry-p (car proof))
         (or (proof-entry-deletion-p (car proof))
             (clausep$ (access add-step (car proof) :clause) a$))
         (proofp$ (cdr proof) a$))))

(defun verify-proof$-rec (ncls ndel formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (integerp ncls) ; really natp; see comment below
                              (natp ndel)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))
                  :verify-guards nil))
  (cond
   ((atom proof) (mv t a$))
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
          (verify-proof$-rec ncls ndel new-formula (cdr proof) a$)))
       (t ; addition
        (mv-let (ncls ndel new-formula a$)
          (verify-clause$ formula entry ncls ndel a$)
          (cond (ncls ; success
                 (verify-proof$-rec
                  (1+ ncls)
                  ndel
                  (add-proof-clause (access add-step entry :index)
                                    (access add-step entry :clause)
                                    new-formula)
                  (cdr proof)
                  a$))
                (t (mv nil a$))))))))))

;;; !!! Delete these foo= fns?
(defun-nx lst= (ptr lst1 lst2)
  (if (zp ptr)
      t
    (let ((ptr (1- ptr)))
      (and (equal (nth ptr lst1) (nth ptr lst2))
           (lst= ptr lst1 lst2)))))

(defun-nx a$= (a1 a2)
  (or (equal a1 a2)
      (and (a$p a1)
           (a$p a2)
           (equal (nth *a$ptr* a1) (nth *a$ptr* a2))
           (equal (nth *a$arri* a1) (nth *a$arri* a2))
           (lst= (nth *a$ptr* a1) (nth *a$stki* a1) (nth *a$stki* a2)))))

(verify-guards verify-proof$-rec)

(defun verify-proof$ (formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))))
  (verify-proof$-rec (fast-alist-len formula)
                     0
                     formula
                     proof
                     a$))

(defund initialize-a$ (max-var a$)
  (declare (xargs :stobjs a$
                  :guard (varp max-var)))
  (let* ((a$ (update-a$ptr 0 a$))
         (a$ (resize-a$stk 0 a$))
         (a$ (resize-a$stk max-var a$))
         (a$ (resize-a$arr 0 a$))
         (a$ (resize-a$arr (1+ max-var) a$)))
    a$))

(defun clause-max-var (clause acc)
  (declare (xargs :guard (and (literal-listp clause)
                              (natp acc))))
  (cond ((endp clause) acc)
        (t (clause-max-var (cdr clause)
                           (max (abs (car clause))
                                acc)))))

(defun formula-max-var (fal acc)

; We only apply this function to formulas with no deleted clauses, so there is
; a slight opportunity for optimization.  But that seems really minor.

  (declare (xargs :guard (and (formula-p fal)
                              (natp acc))))
  (cond ((atom fal) acc)
        (t (formula-max-var (cdr fal)
                            (if (deleted-clause-p (cdar fal))
                                acc
                              (clause-max-var (cdar fal) acc))))))

(defun proof-max-var (proof acc)
  (declare (xargs :guard (and (proofp proof)
                              (natp acc))))
  (cond
   ((endp proof) acc)
   (t (proof-max-var (cdr proof)
                     (let ((entry (car proof)))
                       (if (proof-entry-deletion-p entry)
                           acc
                         (clause-max-var (access add-step entry :clause)
                                         acc)))))))

(defun valid-proofp$ (formula proof a$)
  (declare (xargs :stobjs a$ ; not necessarily satisfying a$p
                  :guard (formula-p formula)
                  :verify-guards nil))
  (let* ((formula (make-fast-alist formula))
         (max-var (and (proofp proof)
                       (proof-max-var proof
                                      (formula-max-var formula 0)))))
    (cond ((varp max-var)
           (let ((a$ (initialize-a$ max-var a$)))
             (mv-let (v a$)
               (verify-proof$ formula proof a$)
               (mv v
                   (proof-contradiction-p proof)
                   a$))))
          (t (mv nil nil a$)))))

(verify-guards valid-proofp$)

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

(defun valid-proofp$-top (formula proof incomplete-okp)
  (declare (xargs :guard t))
  (if (formula-p formula)
      (with-local-stobj a$
        (mv-let (v c a$)
          (valid-proofp$ formula proof a$)
          (if v
              (or incomplete-okp
                  c
                  (er hard? 'valid-proofp$-top
                      "Incomplete proof!"))
            (er hard? 'valid-proofp$-top
                "Invalid proof!"))))
    (er hard? 'valid-proofp$-top
        "Invalid formula!~|~@0"
        (formula-p-error-msg formula))))

(defun refutation-p$ (proof formula)
  (declare (xargs :guard t))
  (valid-proofp$-top formula proof nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code and main theorem from lrat-checker-support.lisp:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ordered-literalsp (x)
  (declare (xargs :guard (literal-listp x)))
  (cond ((endp x) t)
        (t (or (null (cdr x))
               (and (< (abs (car x)) (abs (cadr x)))
                    (ordered-literalsp (cdr x)))))))

(defun lrat-clausep (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (literal-listp x)
           (not (member (car x) (cdr x)))
           (not (member (negate (car x)) (cdr x)))
           (ordered-literalsp (cdr x)))))

(defun lrat-add-step-p (x)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :use (:guard-theorem add-step-p)))))
  (and (weak-add-step-p x)
       (posp (access add-step x :index))
       (lrat-clausep (access add-step x :clause))
       (index-listp (access add-step x :rup-indices))
       (drat-hint-listp (access add-step x :drat-hints))))

(defun lrat-proof-entry-p (entry)
  (declare (xargs :guard t))
  (cond ((and (consp entry)
              (eq (car entry) t)) ; deletion
         (index-listp (cdr entry)))
        (t (lrat-add-step-p entry))))

(defun lrat-proofp (proof)
  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (lrat-proof-entry-p (car proof))
         (lrat-proofp (cdr proof)))))

(defun lrat-valid-proofp$ (formula proof a$)
  (declare (xargs :stobjs a$ ; not necessarily satisfying a$p
                  :guard (formula-p formula)
                  :guard-hints (("Goal" :use (:guard-theorem valid-proofp$)))))
  (let* ((formula (make-fast-alist formula))
         (max-var (and (lrat-proofp proof)
                       (proof-max-var proof
                                      (formula-max-var formula 0)))))
    (cond ((varp max-var)
           (let ((a$ (initialize-a$ max-var a$)))
             (mv-let (v a$)
               (verify-proof$ formula proof a$)
               (mv v
                   (proof-contradiction-p proof)
                   a$))))
          (t (mv nil nil a$)))))

(defun lrat-valid-proofp$-top (formula proof incomplete-okp)
  (declare (xargs :guard t))
  (and (formula-p formula)
       (with-local-stobj a$
         (mv-let (v c a$)
           (lrat-valid-proofp$ formula proof a$)
           (and v
                (or incomplete-okp
                    c))))))


(defun lrat-refutation-p$ (proof formula)
  (declare (xargs :guard t))
  (lrat-valid-proofp$-top formula proof nil))

(defthm main-theorem
  (implies (and (formula-p formula)
                (lrat-refutation-p$ proof formula))
           (not (satisfiable formula))))

