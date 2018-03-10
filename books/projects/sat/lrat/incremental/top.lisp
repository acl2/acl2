; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

; Included books:
(include-book "std/util/bstar" :dir :system) ; b* is used below
(include-book "clrat-parser")
(include-book "tools/er-soft-logic" :dir :system)

; Locally included books:
(local (include-book "incremental"))
(local (include-book "../sorted/lrat-checker"))

; Avoid doing any proofs below by ensuring that every event is introduced in
; one of the books above:
(set-enforce-redundancy t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code from ../list-based/lrat-checker.lisp
; (some of which was defined in yet earlier checkers):
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

; Change the following to defun-inline if you want a bit more performance and
; don't mind the inability to profile this function.  Note that it is illegal
; to profile hons-get.
(defun-notinline my-hons-get (key alist)
  (declare (xargs :guard t))
  (hons-get key alist))

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

; The functions defined below are only relevant to the correctness statement.

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
                              (literalp$ lit a$))))
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

(defun negate-clause (clause a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (clausep$ clause a$))))
  (cond ((atom clause)
         (mv nil a$))
        (t (mv-let (flg a$)
             (push-literal (negate (car clause)) a$)
             (cond (flg (mv flg a$))
                   (t (negate-clause (cdr clause) a$)))))))

(defun evaluate-clause$ (clause a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (clausep$ clause a$))))
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
                              (index-listp indices))))
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
                  :measure (nfix (a$ptr a$))))
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

(defun RATp1$ (alist formula nlit drat-hints a$)

; We think of assignment as being the result of having extended the global
; assignment with the negation of the current proof clause (to check that that
; clause is redundant with respect to formula).

  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (formula-p$ alist a$)
                              (formula-p$ formula a$)
                              (literalp$ nlit a$)
                              (drat-hint-listp drat-hints))))
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
                       (natp ndel))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code from lrat-checker-support.lisp:
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
  (declare (xargs :guard t))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include code from incremental.lisp:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun incl-verify-proof$-rec (ncls ndel formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (integerp ncls) ; really natp; see comment below
                              (natp ndel)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))))
  (cond
   ((atom proof) (mv t formula a$))
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
          (incl-verify-proof$-rec ncls ndel new-formula (cdr proof) a$)))
       (t ; addition
        (mv-let (ncls ndel new-formula a$)
          (verify-clause$ formula entry ncls ndel a$)
          (cond (ncls ; success
                 (let* ((entry-clause (access add-step entry :clause))
                        (newest-formula
                         (add-proof-clause (access add-step entry :index)
                                           entry-clause
                                           new-formula)))
                   (cond
                    ((null entry-clause)
                     (mv :complete newest-formula a$))
                    (t
                     (incl-verify-proof$-rec
                      (1+ ncls)
                      ndel
                      newest-formula
                      (cdr proof)
                      a$)))))
                (t (mv nil formula a$))))))))))

(defun incl-verify-proof$ (formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))))
  (incl-verify-proof$-rec (fast-alist-len formula)
                          0
                          formula
                          proof
                          a$))

(defun incl-initialize-a$ (max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (equal (a$ptr a$) 0)
                              (natp max-var))))
  (cond ((<= max-var (a$stk-length a$))
         a$)
        (t (let* ((new-max-var (* 2 max-var)))
             (initialize-a$ new-max-var a$)))))

(defun check-proofp (proof) ; primitive

; This variant of proofp causes an error when false, printing the offending
; entry.

  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (or (lrat-proof-entry-p (car proof))
             (er hard? 'check-proof
                 "Illegal proof entry: ~X01"
                 (car proof)
                 nil))
         (check-proofp (cdr proof)))))

(defun incl-valid-proofp$ (formula proof old-max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))))
  (let* ((formula (shrink-formula formula))
         (max-var (and (check-proofp proof)
                       (proof-max-var proof old-max-var))))
    (cond ((natp max-var)
           (let ((a$ (incl-initialize-a$ max-var a$)))
             (mv-let (v new-formula a$)
               (incl-verify-proof$ formula proof a$)
               (mv v
                   new-formula
                   max-var
                   a$))))
          (t (mv nil formula old-max-var a$)))))

(defun incl-valid-proofp$-top-rec (formula clrat-file posn chunk-size
                                           clrat-file-length old-suffix debug
                                           old-max-var a$ ctx state)
  (declare (xargs :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (natp posn)
                              (< posn *2^56*)
                              (posp chunk-size)
                              (posp clrat-file-length)
                              (stringp old-suffix)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :ruler-extenders (:lambdas mv-list return-last) ; ugly bug work-around
                  :measure (nfix (- clrat-file-length posn))
                  :stobjs (state a$)))
  (cond
   ((and (mbt (natp posn))
         (mbt (posp clrat-file-length))
         (mbt (posp chunk-size))
         (<= posn clrat-file-length))
    (prog2$
     (and debug
          (cw "; Note: Reading from position ~x0~|" posn))
     (mv-let (proof suffix new-posn)
       (clrat-read-next clrat-file posn chunk-size old-suffix
                        clrat-file-length state)
       (cond
        ((null suffix) ; error (normally a string, possibly even "")
         (mv (er hard? ctx "Implementation error: Null suffix!")
             a$))
        ((null proof)
         (mv :incomplete a$))
        ((stringp proof) ; impossible
         (mv (er hard? ctx
                 "Implementation error: ~x0 returned a string for its proof, ~
                  which we thought was impossible!"
                 'clrat-read-next)
             a$))
        (t
         (mv-let (v new-formula new-max-var a$)
           (prog2$
            (cw "; Note: Checking next proof segment.~|")
            (incl-valid-proofp$ formula proof old-max-var a$))
           (cond
            ((>= new-posn *2^56*)
             (mv (er hard? ctx
                     "Attempted to read at position ~x0, but the maximum ~
                      legal such position is 2^56 = ~x1."
                     new-posn *2^56*)
                 a$))
            ((not v) (mv nil a$))
            ((eq v :complete)
             (mv :complete a$))
            ((> new-posn clrat-file-length)

; If new-posn is exactly clrat-file-length, then as per the discussion of the
; "truncation case" in :doc read-file-into-string, we need to iterate.  But if
; new-posn exceeds clrat-file-length, then we have a valid proof that does not
; include the empty clause.

             (mv :incomplete a$))
            (t
             (incl-valid-proofp$-top-rec new-formula clrat-file new-posn
                                         chunk-size clrat-file-length suffix
                                         debug new-max-var a$ ctx
                                         state)))))))))
   (t ; impossible
    (mv nil a$))))

(defun incl-valid-proofp$-top-aux (formula clrat-file incomplete-okp chunk-size
                                           clrat-file-length debug a$ ctx state)
  (declare (xargs :stobjs (a$ state)
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (posp chunk-size)
                              (posp clrat-file-length))))
  (mv-let (val a$)
    (incl-valid-proofp$-top-rec formula clrat-file 0 chunk-size
                                clrat-file-length "" debug
                                (formula-max-var formula 0)
                                a$ ctx state)
    (case val
      (:complete (mv t a$))
      (:incomplete (mv (or incomplete-okp
                           (er hard? ctx
                               "The proof is valid but does not contain the ~
                                empty clause."))
                       a$))
      (t

; We do not expect to reach the following case.  If nil is returned as the
; first value, it is ultimately because an error occurred.  In particular,
; verify-clause$ either succeeds or causes an error.

       (mv (er hard? ctx
               "Invalid proof!")
           a$)))))

(defun ordered-formula-p1 (formula index)
  (declare (xargs :guard (posp index)))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (< (car pair) index)
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defund ordered-formula-p (formula)

; It is important that the formula produced by the cnf parser does not have
; duplicate indices, since otherwise the first call of shrink-formula will
; change its semantics.  Fortunately, the cnf parser presents the formula in
; reverse order; so we can check for duplicate-free indices in linear time.

  (declare (xargs :guard t))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defun incl-valid-proofp$-top (cnf-file clrat-file incomplete-okp chunk-size
                                        debug ctx state)
  (declare (xargs :guard t :stobjs state))
  (let ((formula (ec-call (cnf-read-file cnf-file state))))
    (cond
     ((not (stringp clrat-file))
      (er-soft-logic
       ctx
       "The filename argument is not a string:~|~x0"
       clrat-file))
     ((not (posp chunk-size))
      (er-soft-logic
       ctx
       "The supplied :chunk-size must be a positive integer, but ~x0 is ~
        not.~|~x0"
       clrat-file))
     ((not (ordered-formula-p formula))
      (er-soft-logic ctx
                     "An invalid formula was supplied by the parser from ~
                      input file ~x0."
                     cnf-file))
     (t
      (mv-let (clrat-file-length state)
        (file-length$ clrat-file state)
        (cond
         ((posp clrat-file-length)
          (prog2$
           (and debug
                (cw "Length of file ~x0: ~x1~|" clrat-file clrat-file-length))
           (value
            (with-fast-alist
              formula
              (with-local-stobj a$
                (mv-let
                  (val a$)
                  (let ((a$ (resize-a$arr 2 a$))) ; to get a$p to hold
                    (incl-valid-proofp$-top-aux formula
                                                clrat-file
                                                incomplete-okp chunk-size
                                                clrat-file-length debug a$
                                                ctx state))
                  (cons val formula)))))))
         ((eql clrat-file-length 0)
          (er-soft-logic
           ctx
           "Zero-length file: ~x0."
           clrat-file))
         (t (er-soft-logic
             ctx
             "Sorry, Lisp cannot determine the file-length of file ~x0."
             clrat-file))))))))

(defun incl-verify-proof-fn (cnf-file clrat-file incomplete-okp chunk-size
                                      debug state)

; This is just a little interface to incl-valid-proofp$-top.

  (declare (xargs :guard t
                  :stobjs state))
  (er-let* ((val/formula
             (time$ (incl-valid-proofp$-top cnf-file clrat-file incomplete-okp
                                            chunk-size debug 'incl-verify-proof
                                            state))))
    (value (car val/formula))))

(defconst *256mb*
  (expt 2 28))

(defconst *default-chunk-size*
  *256mb*)

(defmacro incl-verify-proof (cnf-file clrat-file
                                      &key
                                      incomplete-okp
                                      chunk-size
                                      (debug 't))
  `(incl-verify-proof-fn ,cnf-file ,clrat-file ,incomplete-okp
                         ,(or chunk-size *default-chunk-size*)
                         ,debug
                         state))

; Soundness

(local (include-book "soundness"))

(defun proved-formula (cnf-file clrat-file chunk-size debug incomplete-okp ctx
                                state)
  (declare (xargs :stobjs state))
  (mv-let (erp val/formula state)
    (incl-valid-proofp$-top cnf-file clrat-file
                            incomplete-okp
                            chunk-size debug ctx state)
    (value (and (null erp)
                (consp val/formula)
                (eq (car val/formula) t)

; The formula returned by incl-valid-proofp$-top is in reverse order.  We
; prefer to return a formula that we expect to agree with the formula
; represented in the input cnf-file.

                (reverse (cdr val/formula))))))

(defthm soundness
  (let ((formula (mv-nth 1
                         (proved-formula cnf-file clrat-file chunk-size debug
                                         nil ; incomplete-okp
                                         ctx state))))
    (implies formula
             (not (satisfiable formula)))))
