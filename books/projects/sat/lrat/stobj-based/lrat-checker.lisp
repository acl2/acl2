; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.

(in-package "LRAT")

(include-book "../list-based/lrat-checker")

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

(defthm a$arrp-weak-is-true-listp
  (equal (a$arrp-weak x)
         (true-listp x)))

; Now that assignments are about to be stored in our new stobj, let's rename
; clause-or-assignment-p to the now-more-precise name, clausep.
(defmacro clausep (x)
  `(clause-or-assignment-p ,x))
(add-macro-fn clausep clause-or-assignment-p)

(in-theory (enable literalp clausep))

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

; Not sure if we need this:
(defthm literal-listp$-implies-literal-listp
  (implies (literal-listp$ x a$)
           (literal-listp x))
  :rule-classes (:rewrite :forward-chaining))

(defun clausep$ (x a$)
  (declare (xargs :stobjs a$ :guard t))
  (and (literal-listp$ x a$)
       (unique-literalsp x)
       (not (conflicting-literalsp x))))

(defthm clausep$-forward
  (implies (clausep$ x a$)
           (and (literal-listp$ x a$)
                (unique-literalsp x)
                (not (conflicting-literalsp x))))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable clausep$))

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

(defthm len-resize-list
  (equal (len (resize-list lst n d))
         (nfix n)))

; Start proof of a$p-resize-a$stk

(defthm a$stkp-is-true-listp
  (equal (a$stkp x)
         (true-listp x)))

(encapsulate
  ()

  (local (include-book "std/lists/resize-list" :dir :system))

  #!acl2
  (defthm nth-of-resize-list
    (equal (nth n (resize-list lst m default-value))
           (let ((n (nfix n)) (m (nfix m)))
             (and (< n m)
                  (if (< n (len lst))
                      (nth n lst)
                    default-value))))))

(defthm a$p-good-stk-p-lemma
  (implies (and (<= i (a$stk-length a$))
                (integerp len)
                (<= (a$stk-length a$) len))
           (equal (find-var-on-stk var
                                   i
                                   (update-nth *a$stki*
                                               (resize-list (nth *a$stki* a$)
                                                            len default)
                                               a$))
                  (find-var-on-stk var i a$)))
  :hints (("Goal" :induct (find-var-on-stk var i a$))))

(defthm a$p-good-stk-p
  (implies (and (good-stk-p i a$)
                (<= i (len (nth *a$stki* a$)))
                (integerp len)
                (<= (a$stk-length a$) len))
           (good-stk-p i
                       (update-nth *a$stki*
                                   (resize-list (nth *a$stki* a$) len default)
                                   a$)))
  :hints (("Goal" :induct (good-stk-p i a$))))

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

; Start proof of (verify-guards push-literal)

(defun n-unassigned (i a$)

; Return the number of unassigned literals in a$arr.  Note that this does not
; consider (a$arri 0 a$).

  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$arr-length a$)))))
  (cond ((or (zp i) (= i 1))
         0)
        (t (let ((i (1- i)))
             (cond ((booleanp (a$arri i a$))
                    (n-unassigned i a$))
                   (t (1+ (n-unassigned i a$))))))))

; Here we start the proof of ptr+unassigned=arr-length-lemma.  The proof is by
; induction, according to the scheme suggested by the following defintiion.  We
; split out the base and induction steps and prove them with functions enabled,
; and then prove ptr+unassigned=arr-length-lemma with several function disabled
; so that these base and induction step lemmas can do the job with rewriting.

(defun ptr+unassigned=arr-length-induction (a$)
  (declare (xargs :stobjs a$
                  :guard (a$p a$)
                  :verify-guards nil ; not intended for execution
                  :measure (nfix (a$ptr a$))))
  (cond
   ((zp (a$ptr a$))
    a$)
   (t (let* ((new-ptr (1- (a$ptr a$)))
             (a$ (update-a$ptr new-ptr a$))
             (a$ (update-a$arri (a$stki new-ptr a$)
                                0
                                a$)))
        (ptr+unassigned=arr-length-induction a$)))))

(defthm n-unassigned-for-a$ptr-0
  (implies (and (posp k)
                (arr-matches-stk k a$)
                (equal (a$ptr a$) 0))
           (equal (n-unassigned k a$)
                  (- k 1))))

(defthm ptr+unassigned=arr-base
  (implies (and (a$p a$)
                (zp (a$ptr a$)))
           (equal (n-unassigned (len (nth *a$arri* a$))
                                a$)
                  (+ (len (nth *a$arri* a$))
                     (- (+ (nth *a$ptr* a$) 1))))))

; Start proof of ptr+unassigned=arr-step-1.

; (in-theory (disable a$ptr update-a$ptr a$stki update-a$stki a$arri update-a$arri))

(defthm a$arrp-rec-update-nth
  (implies (and (a$arrp-rec bound a$)
                (natp index)
                (integerp bound))
           (equal (a$arrp-rec bound
                              (update-nth *a$arri*
                                          (update-nth index val (nth *a$arri* a$))
                                          a$))
                  (or (booleanp val)
                      (equal val 0)
                      (>= index bound)))))

(defthm a$arrp-update-nth
  (implies (and (a$arrp a$)
                (natp index)
                (< index (len (nth *a$arri* a$))))
           (equal (a$arrp (update-nth *a$arri*
                                      (update-nth index val (nth *a$arri* a$))
                                      a$))
                  (or (booleanp val)
                      (equal val 0)))))

(local (in-theory (disable nth update-nth)))

(defthm find-var-on-stk-update-nth
  (implies (if (equal j *a$arri*)
               (equal (len x)
                      (len (nth *a$arri* a$)))
             (not (equal j *a$stki*)))
           (equal (find-var-on-stk var i (update-nth j x a$))
                  (find-var-on-stk var i a$))))

(defthm good-stk-p-update-nth
  (implies (if (equal j *a$arri*)
               (equal (len x)
                      (len (nth *a$arri* a$)))
             (not (equal j *a$stki*)))
           (equal (good-stk-p i (update-nth j x a$))
                  (good-stk-p i a$))))

(defthm arr-matches-stk-when-popped
  (implies (and (arr-matches-stk i a$)
                (good-stk-p (a$ptr a$) a$)
                (equal new-ptr (1- (nth *a$ptr* a$)))
                (equal a$1 (update-nth *a$ptr* new-ptr a$))
                (equal a$2 (update-nth *a$arri*
                                       (update-nth (nth new-ptr
                                                        (nth *a$stki* a$1))
                                                   0
                                                   (nth *a$arri* a$1))
                                       a$1)))
           (arr-matches-stk i a$2)))

(defthm a$arrp-rec-update-other-fields
  (implies (not (equal k *a$arri*))
           (equal (a$arrp-rec i (update-nth k x a$))
                  (a$arrp-rec i a$))))

(defthm a$arrp-update-other-fields
  (implies (not (equal k *a$arri*))
           (equal (a$arrp (update-nth k x a$))
                  (a$arrp a$))))

; Trivial consequence of a$arrp-update-nth:
(defthm a$arrp-update-a$arr
  (implies (and (a$arrp a$)
                (varp$ var a$)
                (or (booleanp val)
                    (equal val 0))
                (equal arr (nth *a$arri* a$)))
           (a$arrp (update-nth *a$arri*
                               (update-nth var val arr)
                               a$))))

(in-theory (disable a$arrp))

(defthm ptr+unassigned=arr-step-1
  (implies (and (not (zp (a$ptr a$)))
                (a$p a$))
           (let* ((new-ptr (1- (a$ptr a$)))
                  (a$ (update-a$ptr new-ptr a$)))
             (a$p (update-a$arri (a$stki new-ptr a$)
                                 0
                                 a$)))))

; Start proof of ptr+unassigned=arr-step-2

(defthm n-unassigned-update-a$arri
  (implies (and (equal arr (nth *a$arri* a$))
                (varp i)
                (integerp j))
           (equal (n-unassigned j
                                (update-nth *a$arri*
                                            (update-nth i 0 arr)
                                            a$))
                  (if (and (< i j)
                           (booleanp (nth i (nth *a$arri* a$))))
                      (1+ (n-unassigned j a$))
                    (n-unassigned j a$)))))

(defthm n-unassigned-update-nth
  (implies (not (equal j *a$arri*))
           (equal (n-unassigned i (update-nth j x a$))
                  (n-unassigned i a$))))

(defthm good-stk-p-implies-find-var-on-stk
  (implies (and (natp j)
                (natp i)
                (< i j))
           (find-var-on-stk (nth i (nth *a$stki* a$)) j a$)))

(defthm arr-matches-stk-implies-booleanp-lemma
  (implies (and (arr-matches-stk j a$)
                (integerp j)
                (varp var)
                (< var j)
                (find-var-on-stk var (a$ptr a$) a$))
           (booleanp (nth var (nth *a$arri* a$)))))

(defthm good-stk-p-implies-good-members
  (implies (and (good-stk-p j a$)
                (integerp j)
                (natp i)
                (< i j))
           (and (< (nth i (nth *a$stki* a$))
                   (len (nth *a$arri* a$)))
                (varp (nth i (nth *a$stki* a$)))))
  :rule-classes nil)

(defthm good-stk-p-implies-varp-members
  (implies (and (force (good-stk-p (a$ptr a$) a$))
                (natp (nth *a$ptr* a$))
                (natp i)
                (force (< i (a$ptr a$))))
           (varp (nth i (nth *a$stki* a$))))
  :hints (("Goal" :use ((:instance good-stk-p-implies-good-members
                                   (j (a$ptr a$))))))
  :rule-classes :type-prescription)

(defthm good-stk-p-implies-members-bounded-above
  (implies (and (good-stk-p (a$ptr a$) a$)
                (natp (nth *a$ptr* a$))
                (natp i)
                (< i (a$ptr a$)))
           (< (nth i (nth *a$stki* a$))
              (len (nth *a$arri* a$))))
  :hints (("Goal" :use ((:instance good-stk-p-implies-good-members
                                   (j (a$ptr a$))))))
  :rule-classes :linear)

(defthm arr-matches-stk-implies-booleanp
  (implies (and (arr-matches-stk (len (nth *a$arri* a$)) a$)
                (good-stk-p (a$ptr a$) a$)
                (natp (nth *a$ptr* a$))
                (natp i)
                (< i (a$ptr a$)))
           (booleanp (nth (nth i (nth *a$stki* a$))
                          (nth *a$arri* a$)))))

(defthm ptr+unassigned=arr-step-2
  (let* ((new-ptr (1- (a$ptr a$)))
         (a$1 (update-a$ptr new-ptr a$))
         (a$2 (update-a$arri (a$stki new-ptr a$1)
                             0
                             a$1)))
    (implies (and (not (zp (a$ptr a$)))
                  (equal (n-unassigned (len (nth 2 a$2)) a$2)
                         (+ (len (nth 2 a$2))
                            (- (+ (nth *a$ptr* a$2) 1))))
                  (a$p a$))
             (equal (n-unassigned (len (nth *a$arri* a$))
                                  a$)
                    (+ (len (nth *a$arri* a$))
                       (- (+ (nth *a$ptr* a$) 1)))))))

(encapsulate
  ()

  (local
   (defthm ptr+unassigned=arr-length-lemma
     (implies (a$p a$)
              (equal (n-unassigned (len (nth 2 a$)) a$)
                     (- (len (nth 2 a$))
                        (+ (nth 0 a$) 1))))
     :hints (("Goal"
              :induct
              (ptr+unassigned=arr-length-induction a$)
              :in-theory
              (disable a$p update-a$arri a$stki update-a$ptr a$ptr)))))

  (defthm ptr+unassigned=arr-length
; Note that (a$arr-length a$) = (len (nth 2 a$)) and
; (a$ptr a$) = (nth 0 a$).
    (implies (and (a$p a$)
                  (equal k (len (nth 2 a$))))
             (equal (n-unassigned k a$)
                    (- (len (nth 2 a$))
                       (+ (nth 0 a$) 1))))))

(defthm n-unassigned-positive-lemma
  (implies (and (posp var)
                (integerp k)
                (< var k)
                (not (booleanp (nth var (nth *a$arri* a$)))))
           (< 0 (n-unassigned k a$)))
  :rule-classes nil)

(defthm n-unassigned-positive
  (implies (and (posp var)
                (equal k (len (nth *a$arri* a$)))
                (equal (n-unassigned k a$) 0)
                (< var k)
                (nth var (nth *a$arri* a$)))
           (equal (nth var (nth *a$arri* a$))
                  t))
  :hints (("Goal" :use ((:instance n-unassigned-positive-lemma)))))

(verify-guards push-literal)

(defthm literal-listp$-push-literal

; This lemma is likely important for guard verification for negate-clause,
; below.  But it's probably also helpful for proving a$p-push-literal.

  (implies (and (a$p a$)
                (literal-listp$ lst a$)
                (literalp$ lit a$))
           (literal-listp$ lst
                           (mv-nth 1 (push-literal lit a$)))))

; Start proof of a$p-push-literal.

; We're about to do better than these....
(in-theory (disable arr-matches-stk-implies-booleanp-lemma
                    arr-matches-stk-implies-booleanp))

(defthm arr-matches-stk-iff-booleanp-lemma
  (implies (and (integerp j)
                (varp var)
                (< var j)
                (arr-matches-stk j a$))
           (equal (find-var-on-stk var (nth *a$ptr* a$) a$)
                  (booleanp (nth var (nth *a$arri* a$))))))

(defthm arr-matches-stk-iff-booleanp
  (implies (and (varp var)
                (< var (len (nth *a$arri* a$)))
                (arr-matches-stk (len (nth *a$arri* a$)) a$)
                (equal ptr (nth *a$ptr* a$)))
           (equal (find-var-on-stk var ptr a$)
                  (booleanp (nth var (nth *a$arri* a$))))))

(defthm find-var-on-stk-update-stk-past-ptr

; Updating the stack out of range doesn't affect find-var-on-stk.

  (implies (and (integerp j)
                (<= i j))
           (equal (find-var-on-stk
                   var
                   i
                   (update-nth *a$stki*
                               (update-nth j lit (nth *a$stki* a$))
                               a$))
                  (find-var-on-stk var i a$))))

(defthm arr-matches-stk-update-stk-past-ptr

; Updating the stack at or above the  ptr doesn't affect arr-matches-stk.

  (implies (and (integerp i)
                (<= (nth *a$ptr* a$) i))
           (equal (arr-matches-stk
                   j
                   (update-nth *a$stki*
                               (update-nth i lit (nth *a$stki* a$))
                               a$))
                  (arr-matches-stk j a$))))

(defthm good-stk-p-update-a$stki-at-larger
  (implies (and (natp ptr2)
                (<= ptr1 ptr2))
           (equal (good-stk-p ptr1
                              (update-nth *a$stki*
                                          (update-nth ptr2
                                                      var
                                                      (nth *a$stki* a$))
                                          a$))
                  (good-stk-p ptr1 a$))))

(defthm arr-matches-stk-push

; Updating the stack at or above the ptr doesn't affect arr-matches-stk.

  (implies (and (arr-matches-stk j a$)
                (natp (nth *a$ptr* a$))
                (varp$ var a$)
                (booleanp b))
           (arr-matches-stk
            j
            (update-nth *a$arri*
                        (update-nth var b (nth *a$arri* a$))
                        (update-nth *a$ptr*
                                    (+ 1 (nth *a$ptr* a$))
                                    (update-nth *a$stki*
                                                (update-nth (nth *a$ptr* a$)
                                                            var
                                                            (nth *a$stki* a$))
                                                a$))))))

(defthm a$p-push-literal
  (implies (and (a$p a$)
                (literalp$ lit a$))
           (a$p (mv-nth 1 (push-literal lit a$)))))

(defthm literal-listp$-forward-to-literalp$-car
  (implies (and (literal-listp$ lst a$)
                (consp lst))
           (literalp$ (car lst) a$))
  :rule-classes :forward-chaining)

(defthm literal-listp$-forward-to-literal$-listp-cdr
  (implies (literal-listp$ lst a$)
           (literal-listp$ (cdr lst) a$))
  :rule-classes :forward-chaining)

(defthm literalp$-forward
  (implies (literalp$ lit a$)
           (and (literalp lit)
                (< lit (len (nth *a$arri* a$)))
                (< (- lit) (len (nth *a$arri* a$)))))
  :rule-classes :forward-chaining)

(defthm literalp$-minus
  (implies (literalp$ lit a$)
           (literalp$ (negate lit) a$))
  :rule-classes :forward-chaining)

(in-theory (disable a$p push-literal literalp$ literal-listp$))

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

(defthm clausep$-cdr
  (implies (clausep$ x a$)
           (clausep$ (cdr x) a$))
  :hints (("Goal" :in-theory (enable clausep$ literal-listp$)))
  :rule-classes (:forward-chaining :rewrite))

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

(defthm literalp$-is-unit-clause$
  (implies (and (a$p a$)
                (clausep$ clause a$)
                (is-unit-clause$ clause a$)
                (not (equal (is-unit-clause$ clause a$) t)))
           (literalp$ (is-unit-clause$ clause a$) a$)))

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

(defthm clausep$-hons-assoc-equal
  (implies (and (formula-p$ formula a$)
                (hons-assoc-equal index formula)
                (not (deleted-clause-p
                      (cdr (hons-assoc-equal index formula)))))
           (clausep$ (cdr (hons-assoc-equal index formula))
                     a$)))

; Not sure the following is needed; but seems harmless:
(defthm a$p-forward-to-natp-a$ptr
  (implies (a$p a)
           (natp (nth *a$ptr* a)))
  :hints (("Goal" :in-theory (enable a$p)))
  :rule-classes :forward-chaining)

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

(defthm car-push-literal-for-unit-clause
  (implies (and (clausep u)
                (is-unit-clause$ u a$)
                (not (equal (is-unit-clause$ u a$)
                            t)))
           (equal (car (push-literal (is-unit-clause$ u a$) a$))
                  nil))
  :hints (("Goal" :in-theory (enable push-literal))))

(defthm formula-p$-implies-formula-p
  (implies (formula-p$ x a$)
           (formula-p x))
  :rule-classes (:rewrite :forward-chaining))

(defthm formula-p$-implies-clausep$
  (implies (and (formula-p$ x a$)
                (not (equal (cdr (hons-assoc-equal i x))
                            *deleted-clause*)))
           (clausep$ (cdr (hons-assoc-equal i x))
                     a$))
  :hints (("Goal" :in-theory (enable clausep$ literal-listp$)))
  :rule-classes (:rewrite :forward-chaining))

(defthm formula-p-implies-clausep
  (implies (and (formula-p x)
                (not (equal (cdr (hons-assoc-equal i x))
                            *deleted-clause*)))
           (clausep (cdr (hons-assoc-equal i x))))
; This is already a rewrite rule, as
; acl2::clause-or-assignment-p-cdr-hons-assoc-equal.
  :rule-classes :forward-chaining)

(defthm clausep$-implies-clausep
  (implies (clausep$ x a$)
           (clausep x))
  :rule-classes (:rewrite :forward-chaining))

(defthm literalp$-mv-nth-1-push-literal
  (implies (literalp$ lit2 a$)
           (equal (literalp$ lit1
                             (mv-nth 1 (push-literal lit2 a$)))
                  (literalp$ lit1 a$)))
  :hints (("Goal"
           :in-theory (enable push-literal literalp$))))

(defthm literal-listp$-nil
  (literal-listp$ nil a$)
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm literal-listp$-mv-nth-1-push-literal
  (implies (literalp$ lit a$)
           (equal (literal-listp$ clause (mv-nth 1 (push-literal lit a$)))
                  (literal-listp$ clause a$)))
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm clausep$-mv-nth-1-push-literal
  (implies (literalp$ lit a$)
           (equal (clausep$ clause (mv-nth 1 (push-literal lit a$)))
                  (clausep$ clause a$)))
  :hints (("Goal" :in-theory (enable clausep$))))

(defthm formula-p$-mv-nth-1-push-literal
  (implies (literalp$ lit a$)
           (equal (formula-p$ formula (mv-nth 1 (push-literal lit a$)))
                  (formula-p$ formula a$))))

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

; Start proof for (verify-guards pop-literals).

(defthm varp$-nth-stk
  (implies (and (a$p a$)
                (natp i)
                (< i (nth *a$ptr* a$)))
           (varp$ (nth i (nth *a$stki* a$))
                  a$))
  :hints (("Goal" :in-theory (enable a$p)))
  :rule-classes
  ((:forward-chaining :trigger-terms
                      ((nth i (nth *a$stki* a$)))
                      :corollary
                      (implies (and (force (a$p a$))
                                    (force (natp i))
                                    (force (< i (nth *a$ptr* a$))))
                               (varp (nth i (nth *a$stki* a$)))))
   (:linear :corollary (implies (and (force (a$p a$))
                                     (force (natp i))
                                     (force (< i (nth *a$ptr* a$))))
                                (< (nth i (nth *a$stki* a$))
                                   (len (nth *a$arri* a$)))))))

(defthm a$ptr-<=-a$stk-length
  (implies (a$p a$)
           (<= (nth *a$ptr* a$)
               (len (nth *a$stki* a$))))
  :hints (("Goal" :in-theory (enable a$p)))
  :rule-classes :linear)

(defthm good-stk-p-implies-varp
  (implies (and (good-stk-p i a$)
                (natp j)
                (integerp i)
                (< j i))
           (varp$ (nth j (nth *a$stki* a$))
                  a$)))

(defthm find-var-on-stk-update-a$arri
  (equal (find-var-on-stk var
                          i
                          (update-nth *a$arri* x a$))
         (find-var-on-stk var i a$)))

(defthm arr-matches-stk-pop

; Updating the stack at or above the  ptr doesn't affect arr-matches-stk.

  (implies (and (arr-matches-stk j a$)
                (good-stk-p (nth *a$ptr* a$) a$)
                (natp j)
                (natp (nth *a$ptr* a$))
                (equal var (nth (+ -1 (nth *a$ptr* a$))
                                (nth *a$stki* a$)))
                (natp var)
                (< var j))
           (arr-matches-stk
            j
            (update-nth *a$arri*
                        (update-nth var 0 (nth *a$arri* a$))
                        (update-nth *a$ptr*
                                    (+ -1 (nth *a$ptr* a$))
                                    a$)))))

(encapsulate
  ()
  (local (in-theory (enable a$p)))
  (local (disable-forcing))
  (defthm a$p-pop-literal
    (implies (and (a$p a$)
                  (< 0 (nth *a$ptr* a$)))
             (a$p (update-nth *a$arri*
                              (update-nth (nth (+ -1 (nth *a$ptr* a$))
                                               (nth *a$stki* a$))
                                          0
                                          (nth *a$arri* a$))
                              (update-nth *a$ptr*
                                          (+ -1 (nth *a$ptr* a$))
                                          a$))))))

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

; Start proof of (verify-guards ratp1)

(defthm a$p-rat-assignment$
  (implies (and (force (a$p a$))
                (force (clausep$ clause a$)))
           (a$p (mv-nth 1 (rat-assignment$ a$ nlit clause))))
  :rule-classes
  (:rewrite
   (:forward-chaining :trigger-terms
                      ((mv-nth 1 (rat-assignment$ a$ nlit clause))))))

(defthm literalalp$-update-a$arri
  (implies (< i (len (nth *a$arri* a$)))
           (equal (literalp$ lit (update-nth *a$arri*
                                             (update-nth i x (nth *a$arri* a$))
                                             a$2))
                  (literalp$ lit a$)))
  :hints (("Goal" :in-theory (enable literalp$))))

(defthm literal-listp$-update-a$arri
  (implies (< i (len (nth *a$arri* a$)))
           (equal (literal-listp$ lst
                                  (update-nth *a$arri*
                                              (update-nth i x (nth *a$arri* a$))
                                              a$2))
                  (literal-listp$ lst a$)))
  :hints (("Goal" :in-theory (enable literal-listp$))))

(defthm clausep$-update-a$arri
  (implies (< i (len (nth *a$arri* a$)))
           (equal (clausep$ clause
                            (update-nth *a$arri*
                                        (update-nth i x (nth *a$arri* a$))
                                        a$2))
                  (clausep$ clause a$)))
  :hints (("Goal" :in-theory (enable clausep$))))

(defthm clausep$-pop-literals
  (equal (clausep$ clause (pop-literals old-ptr a$))
         (clausep$ clause a$))
  :hints (("Goal" :in-theory (e/d (a$p) (force)))))

(defthm formula-p$-pop-literals
  (equal (formula-p$ formula (pop-literals old-ptr a$))
         (formula-p$ formula a$)))

(defthm literalp$-mv-nth-1-rat-assignment$
  (implies (clausep$ clause a$)
           (equal (literalp$ lit
                             (mv-nth 1 (rat-assignment$ a$ lit clause)))
                  (literalp$ lit a$))))

(defthm clausep$-mv-nth-1-rat-assignment$
  (implies (clausep$ clause a$)
           (equal (clausep$ c
                            (mv-nth 1 (rat-assignment$ a$ lit clause)))
                  (clausep$ c a$))))

(defthm formula-p$-mv-nth-1-rat-assignment$
  (implies (clausep$ clause a$)
           (equal (formula-p$ formula
                              (mv-nth 1 (rat-assignment$ a$ lit clause)))
                  (formula-p$ formula a$)))
  :hints (("Goal" :in-theory (enable formula-p$))))

(defthm literalp$-pop-literals
  (equal (literalp$ lit (pop-literals ptr a$))
         (literalp$ lit a$))
  :hints (("Goal" :in-theory (enable a$p literalp$))))

(defthm a$ptr-mv-nth-1-push-literal-larger
  (<= (nth *a$ptr* a$)
      (nth *a$ptr*
           (mv-nth 1 (push-literal lit a$))))
  :hints (("Goal" :in-theory (enable push-literal)))
  :rule-classes :linear)

(defthm a$ptr-rat-assignment-larger
  (<= (nth *a$ptr* a$)
      (nth *a$ptr*
           (mv-nth 1
                   (rat-assignment$ a$ lit clause))))
  :rule-classes :linear)

(defthm a$p-mv-nth-1-unit-propagation$
  (implies
   (and (force (a$p a$))
        (force (formula-p$ formula a$)))
   (a$p (mv-nth 1
                (unit-propagation$ formula indices a$)))))

(defthm a$p-pop-literals
  (implies (force (a$p a$))
           (a$p (pop-literals index a$))))

(defthm literalp$-mv-nth-1-unit-propagation$
  (implies (and (a$p a$)
                (formula-p$ formula a$))
           (equal (literalp$ lit (mv-nth 1 (unit-propagation$ formula indices a$)))
                  (literalp$ lit a$))))

(defthm clausep$-mv-nth-1-unit-propagation$
  (implies (and (force (a$p a$))
                (force (formula-p$ formula a$)))
           (equal
            (clausep$ clause
                      (mv-nth 1
                              (unit-propagation$ formula indices a$)))
            (clausep$ clause a$))))

(defthm formula-p$-mv-nth-1-unit-propagation$
  (implies (and (a$p a$)
                (formula-p$ formula a$))
           (equal (formula-p$ f2 (mv-nth 1 (unit-propagation$ formula indices a$)))
                  (formula-p$ f2 a$))))

(defthm a$ptr-mv-nth-1-unit-propagation$-larger
  (<= (nth *a$ptr* a$)
      (nth *a$ptr*
           (mv-nth 1 (unit-propagation$ formula indices a$))))
  :rule-classes :linear)

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

; Start proof of (verify-guards verify-clause$)

(defthm a$p-mv-nth-1-negate-clause
  (implies (and (a$p a$)
                (clausep$ clause a$))
           (a$p (mv-nth 1
                        (negate-clause clause a$))))
  :rule-classes (:rewrite

; The following additional rule class helps with (verify-guards verify-clause$)
; below.

                 (:forward-chaining
                  :trigger-terms
                  ((mv-nth 1 (negate-clause clause a$))))))

(defthm formula-p$-mv-nth-1-negate-clause
  (implies (clausep$ clause a$)
           (equal (formula-p$ formula (mv-nth 1 (negate-clause clause a$)))
                  (formula-p$ formula a$))))

(defthm natp-a$ptr-mv-nth-1-push-literal
  (implies (force (natp (nth *a$ptr* a$)))
           (natp (nth *a$ptr*
                      (mv-nth 1 (push-literal lit a$)))))
  :hints (("Goal" :in-theory (enable push-literal)))
  :rule-classes :type-prescription)

(defthm natp-a$ptr-mv-nth-1-unit-propagation$
  (implies (force (natp (nth *a$ptr* a$)))
           (natp (nth *a$ptr*
                      (mv-nth 1 (unit-propagation$ formula indices a$)))))
  :rule-classes :type-prescription)

(defthm a$p-mv-nth-1-ratp1
  (implies (and (a$p a$)
                (formula-p$ alist a$)
                (formula-p$ formula a$))
           (a$p (mv-nth 1 (RATp1$ alist formula nlit drat-hints a$))))
  :hints (("Goal" :induct (RATp1$ alist formula nlit drat-hints a$))))

(defthm formula-p$-remove-deleted-clauses
  (implies (and (formula-p$ formula a$)
                (formula-p$ acc a$))
           (formula-p$ (remove-deleted-clauses formula acc)
                       a$)))

(defthm formula-p$-fast-alist-fork
  (implies (and (formula-p$ formula a$)
                (formula-p$ acc a$))
           (formula-p$ (fast-alist-fork formula acc)
                       a$)))

(defthm cdr-last-formula
  (implies (formula-p formula)
           (equal (cdr (last formula))
                  nil)))

(defthm formula-p$-shrink-formula
  (implies (formula-p$ formula a$)
           (formula-p$ (shrink-formula formula) a$))
  :hints (("Goal" :in-theory (enable shrink-formula))))

(defthm formula-p$-mv-nth-2-maybe-shrink-formula
  (implies (force (formula-p$ formula a$))
           (formula-p$ (mv-nth 2 (maybe-shrink-formula ncls ndel formula
                                                       factor))
                       a$))
  :hints (("Goal" :in-theory (enable maybe-shrink-formula))))

(defthm literalp$-mv-nth-1-negate-clause
  (implies (clausep$ clause a$)
           (equal (literalp$ lit (mv-nth 1 (negate-clause clause a$)))
                  (literalp$ lit a$))))

(defthm a$ptr-pop-literals
  (implies (and (force (a$p a$))
                (force (natp ptr))
                (<= ptr (nth *a$ptr* a$)))
           (equal (nth *a$ptr* (pop-literals ptr a$))
                  ptr)))

(defthm a$ptr-mv-nth-1-ratp1
  (implies (and (a$p a$)
                (formula-p$ alist a$)
                (formula-p$ formula a$))
           (equal (nth *a$ptr*
                       (mv-nth 1 (RATp1$ alist formula nlit drat-hints a$)))
                  (nth *a$ptr* a$)))
  :hints (("Goal"
           :induct (RATp1$ alist formula nlit drat-hints a$)
           :in-theory (disable (force))))
  :rule-classes :linear)

(defthm ratp1-error-shape
  (implies (not (equal (car (RATp1$ alist formula nlit drat-hints a$))
                       t))
           (and (true-listp (car (RATp1$ alist formula nlit drat-hints a$)))
                (equal (len (car (RATp1$ alist formula nlit drat-hints a$)))
                       4)))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((car (RATp1$ alist formula nlit drat-hints a$))))))

(defthm a$p-mv-nth-1-negate-clause-forward
  (implies (and (a$p a$)
                       (clausep$ clause a$))
           (a$p (mv-nth 1
                        (negate-clause clause a$))))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((mv-nth 1 (negate-clause clause a$))))))

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

; Start proof of (verify-guards verify-proof$-rec)

(defthm proofp$-forward-to-proofp
  (implies (proofp$ proof a$)
           (proofp proof))
  :rule-classes :forward-chaining)

(defthm proofp-forward-to-proof-entry-p
  (implies (and (proofp proof)
                proof)
           (proof-entry-p (car proof)))
  :rule-classes :forward-chaining)

(defthm proof-entry-p-forward-to-add-step-p
  (implies (and (proof-entry-p entry)
                (not (equal (car entry) t)))
           (add-step-p entry))
  :rule-classes :forward-chaining)

(defthm proof-entry-p-forward-to-index-listp
  (implies (and (proof-entry-p entry)
                (equal (car entry) t))
           (index-listp (cdr entry)))
  :rule-classes :forward-chaining)

(defthm formula-p$-delete-clauses
  (implies (and (formula-p$ formula a$)
                (index-listp index-list))
           (formula-p$ (delete-clauses index-list formula) a$)))

;; !! Perhaps maybe-shrink-formula shouldn't return the unchanged ncls.
(defthm car-maybe-shrink-formula
  (equal (car (maybe-shrink-formula ncls ndel formula factor))
         ncls)
  :hints (("Goal" :in-theory (enable maybe-shrink-formula))))

(defthm formula-p-mv-nth-2-maybe-shrink-formula
  (implies (formula-p formula)
           (formula-p (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor))))
  :hints (("Goal" :in-theory (enable maybe-shrink-formula))))

(defthm natp-mv-nth-1-maybe-shrink-formula
  (implies (natp ndel)
           (natp (mv-nth 1 (maybe-shrink-formula ncls ndel formula factor))))
  :hints (("Goal" :in-theory (enable maybe-shrink-formula))))

(defthm literal-listp$-mv-nth-1-negate-clause
  (implies (and (literal-listp$ c1 a$)
                (clausep$ c2 a$))
           (literal-listp$ c1 (mv-nth 1 (negate-clause c2 a$)))))

(defthm clausep$-mv-nth-1-negate-clause
  (implies (and (clausep$ c1 a$)
                (clausep$ c2 a$))
           (clausep$ c1 (mv-nth 1 (negate-clause c2 a$)))))

(defthm add-step-p-forward
  (implies (add-step-p x)
           (and (weak-add-step-p x)
                (posp (access add-step x :index))
                (clause-or-assignment-p
                 (access add-step x :clause))
                (index-listp (access add-step x :rup-indices))
                (drat-hint-listp
                 (access add-step x :drat-hints))))
  :rule-classes :forward-chaining)

(defthm proofp$-forward-to-clausep$
  (implies (and (proofp$ proof a$)
                proof
                (not (equal (car (car proof)) t)))
           (clausep$ (access add-step (car proof) :clause)
                     a$))
  :rule-classes :forward-chaining)

(defthm clausep$-mv-nth-1-ratp1
  (implies (and (a$p a$)
                (formula-p$ alist a$)
                (formula-p$ formula a$))
           (equal (clausep$ clause
                            (mv-nth 1 (RATp1$ alist formula nlit drat-hints a$)))
                  (clausep$ clause a$)))
  :hints (("Goal" :induct (RATp1$ alist formula nlit drat-hints a$))))

(defthm formula-p$-mv-nth-1-ratp1
  (implies (and (a$p a$)
                (formula-p$ alist a$)
                (formula-p$ formula a$)
                (formula-p$ formula2 a$))
           (formula-p$ formula2
                       (mv-nth 1 (RATp1$ alist formula nlit drat-hints a$))))
  :hints (("Goal" :induct (RATp1$ alist formula nlit drat-hints a$))))

; It is convenient to introduce a notion of equivalence, a$=, saying that to
; a$p structures are equal except perhaps for the a$stk elements at or above
; position a$ptr.  The reason is that our functions push and pop the a$stk,
; leaving "garbage" at or above a$ptr that is irrelevant for reasoning.  There
; are congruence rules below for that notion of "irrelevant" i.e., of a$=, and
; there are also rewrite rules that rewrite with respect to this equivalence
; relation, so that the ACL2 rewriter can easily simplify accesses into complex
; updates of a$p structures.  Hmmm, perhaps it would have been useful to do
; this earlier above.

; We start with a notion of list equivalence, to be used for two a$stk
; structures and also, for convenience, may be used for two a$arr structures.

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

(defthm lst=-symmetric
  (equal (lst= ptr stk1 stk2)
         (lst= ptr stk2 stk1)))

(defthm lst=-transitive
  (implies (and (lst= ptr stk1 stk2)
                (lst= ptr stk2 stk3))
           (lst= ptr stk1 stk3)))

(defequiv a$=)

(defthm a$=-implies-equal-literalp$-2
  (implies (a$= a1 a2)
           (equal (literalp$ lit a1)
                  (literalp$ lit a2)))
  :hints (("Goal" :in-theory (enable literalp$)))
  :rule-classes :congruence)

(defthm a$=-implies-equal-literalp$-2-rewrite
  (implies (and (literalp$ lit a1)
                (not (literalp$ lit a2)))
           (not (a$= a1 a2))))

(in-theory (disable a$=))

(defthm a$=-implies-equal-literal-listp$-2
  (implies (a$= a1 a2)
           (equal (literal-listp$ clause a1)
                  (literal-listp$ clause a2)))
  :hints (("Goal" :in-theory (enable literalp$ literal-listp$)))
  :rule-classes :congruence)

(defthm a$=-implies-equal-literal-listp$-2-rewrite
  (implies (and (literal-listp$ clause a1)
                (not (literal-listp$ clause a2)))
           (not (a$= a1 a2))))

(defthm a$=-implies-equal-clausep$-2
  (implies (a$= a1 a2)
           (equal (clausep$ clause a1)
                  (clausep$ clause a2)))
  :hints (("Goal" :in-theory (enable clausep$)))
  :rule-classes :congruence)

(defthm a$=-implies-equal-proofp$-2
  (implies (a$= a1 a2)
           (equal (proofp$ proof a1)
                  (proofp$ proof a2)))
  :rule-classes :congruence)

; Start proof of a$=-for-pop-literals-mv-nth-1-unit-propagation$

; Start proof of a$arr-pop-literals-mv-nth-1-unit-propagation$

; AHA -- at this point I realized that after pushing and popping a
; previously-unassigned literal lit with variable var, the a$arr will return to
; its original value only if the value of var was 0, not some other non-Boolean
; value.  Ths is why we now require a$arr to consist entirely of t, nil, and 0
; values.

; Start proof of a$arr-pop-literals-mv-nth-1-push-literal

(defthm update-nth-same
  (equal (update-nth n x
                     (update-nth n y lst))
         (update-nth n x lst))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm literalp$-implies-boolean-or-0-nth-lemma
  (implies (and (a$arrp-rec bound a$)
                (natp var)
                (natp bound)
                (< var bound))
           (or (booleanp (nth var (nth *a$arri* a$)))
               (equal (nth var (nth *a$arri* a$)) 0)))
  :rule-classes nil)

(defthm literalp$-implies-boolean-or-0-nth
  (implies (and (force (a$p a$))
                (force (varp$ var a$)))
           (or (booleanp (nth var (nth *a$arri* a$)))
               (equal (nth var (nth *a$arri* a$)) 0)))
  :hints (("Goal"
           :use ((:instance literalp$-implies-boolean-or-0-nth-lemma
                            (bound (len (nth *a$arri* a$)))))
           :in-theory (enable a$p a$arrp)))
  :rule-classes :type-prescription)

(defthm update-nth-update-nth
  (implies (and (natp i)
                (natp j)
                (not (equal i j)))
           (equal (update-nth i x (update-nth j y a))
                  (update-nth j y (update-nth i x a))))
  :rule-classes ((:rewrite :loop-stopper
                           ((i j update-nth) (x y update-nth))))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm update-nth-no-op
  (implies (and (force (natp i))
                (force (< i (len a))))
           (equal (equal (update-nth i v a)
                         a)
                  (equal v (nth i a))))
  :hints (("Goal" :in-theory (enable nth update-nth))))

(defthm literalp$-update-nth-other
  (implies (not (equal k *a$arri*))
           (equal (literalp$ lit (update-nth k x a$))
                  (literalp$ lit a$)))
  :hints (("Goal" :in-theory (enable literalp$))))

(defthm update-nth-no-op-alt
  (implies (and (equal v (nth i a))
                (force (natp i))
                (force (< i (len a))))
           (equal (update-nth i v a)
                  a)))

; Start proof of pop-literals-update-a$stk-large

(defthm a$p-when-decrementing-a$ptr
  (implies (and (a$p a$)
                (not (equal 0 (nth *a$ptr* a$))))
           (a$p (update-nth *a$ptr* (+ -1 (nth *a$ptr* a$))
                            (update-nth *a$arri*
                                        (update-nth (nth (+ -1 (nth *a$ptr* a$))
                                                         (nth *a$stki* a$))
                                                    0
                                                    (nth *a$arri* a$))
                                        a$))))
  :hints (("Goal" :in-theory (e/d (a$p) ((force))))))

(defthm non-boolean-lit-is-0
  (implies (and (a$p a$)
                (posp var)
                (< var (len (nth *a$arri* a$)))
                (not (equal (nth var (nth *a$arri* a$))
                            t)))
           (iff (nth var (nth *a$arri* a$))
                (equal (nth var (nth *a$arri* a$))
                       0))))

(defthm len-a$
  (implies (a$p a$)
           (equal (len a$) 3))
  :hints (("Goal" :in-theory (enable a$p))))

(defthm a$p-push-literal-special-case-expanded
  (implies (and (a$p a$)
                (literalp$ lit a$)
                (equal var (abs lit))
                (equal val (equal var lit))
                (equal (nth var (nth *a$arri* a$))
                       0))
           (a$p (update-nth
                 *a$ptr*
                 (+ 1 (nth *a$ptr* a$))
                 (update-nth
                  *a$stki*
                  (update-nth (nth *a$ptr* a$)
                              var
                              (nth *a$stki* a$))
                  (update-nth *a$arri*
                              (update-nth var val (nth *a$arri* a$))
                              a$)))))
  :hints (("Goal"
           :use a$p-push-literal
           :in-theory (e/d (push-literal) (a$p-push-literal)))))

(defthm a$p-update-a$stk-large
  (implies (and (force (a$p a$))
                (force (< (nth *a$ptr* a$)
                          (len (nth *a$stki* a$)))))
           (a$p (update-nth *a$stki*
                            (update-nth (nth *a$ptr* a$)
                                        lit
                                        (nth *a$stki* a$))
                            a$)))
  :hints (("Goal" :in-theory (enable a$p))))

(defthm a$p-forward-to-len-a$arr
  (implies (a$p a$)
           (equal (len (nth *a$arri* a$))
                  (+ 1 (len (nth *a$stki* a$)))))
  :hints (("Goal" :in-theory (enable a$p)))
  :rule-classes (:forward-chaining :rewrite))

(defun-nx pop-literals-2-induction (old-ptr a1 a2)
  (declare (xargs :measure (nfix (a$ptr a1))
                  :hints (("Goal" :in-theory (enable a$p)))))
  (cond
   ((and (mbt (and (a$p a1)
                   (natp old-ptr)
                   (<= old-ptr (a$ptr a1))))
         (not (= old-ptr (a$ptr a1))))
    (let* ((index (1- (a$ptr a1)))
           (var (a$stki index a1))
           (a1 (update-a$ptr index a1))
           (a1 (update-a$arri var 0 a1))
           (a2 (update-a$ptr index a2))
           (a2 (update-a$arri var 0 a2)))
      (pop-literals-2-induction old-ptr a1 a2)))
   (t a1)))

(defthm a$=-implies-equal-a$arr-pop-literals-lemma
  (implies (and (a$= a1 a2)
                (a$p a1)
                (a$p a2))
           (equal (nth *a$arri*
                       (pop-literals ptr a1))
                  (nth *a$arri*
                       (pop-literals ptr a2))))
  :hints (("Goal"
           :in-theory (enable a$=)
           :induct (pop-literals-2-induction ptr a1 a2)))
  :rule-classes nil)

(defthm a$=-implies-equal-a$arr-pop-literals
  (implies (a$= a1 a2)
           (equal (nth *a$arri*
                       (pop-literals ptr a1))
                  (nth *a$arri*
                       (pop-literals ptr a2))))
  :hints (("Goal"
           :in-theory (enable a$=)
           :use a$=-implies-equal-a$arr-pop-literals-lemma))
  :rule-classes :congruence)

(defthm lst=-update-stk-by-ptr
  (implies (and (natp ptr1)
                (integerp ptr2)
                (<= ptr1 ptr2))
           (lst= ptr1
                 stk
                 (update-nth ptr2 lit stk))))

(defthm a=-update-stk-by-ptr
  (implies (and (force (a$p a$))
                (force (< (nth *a$ptr* a$)
                          (len (nth *a$stki* a$)))))
           (a$= (update-nth *a$stki*
                            (update-nth (nth *a$ptr* a$)
                                        lit
                                        (nth *a$stki* a$))
                            a$)
                a$))
  :hints (("Goal" :in-theory (enable a$=))))

(defthm stk-full-implies-array-all-boolean-pos
  (implies (and (a$p a$)
                (equal (nth *a$ptr* a$)
                       (len (nth *a$stki* a$)))
                (literalp$ lit a$)
                (<= 0 lit))
           (booleanp (nth lit (nth *a$arri* a$))))
  :hints (("Goal" :in-theory (enable booleanp)))
  :rule-classes :type-prescription)

(defthm stk-full-implies-array-all-boolean-neg
  (implies (and (a$p a$)
                (equal (nth *a$ptr* a$)
                       (len (nth *a$stki* a$)))
                (literalp$ lit a$)
                (< lit 0))
           (booleanp (nth (- lit) (nth *a$arri* a$))))
  :hints (("Goal" :in-theory (enable booleanp)))
  :rule-classes :type-prescription)

(defthm a$arr-pop-literals-mv-nth-1-push-literal
  (implies
   (and (a$p a$)
        (literalp$ lit a$)
        (natp ptr)
        (<= ptr (nth *a$ptr* a$)))
   (equal (nth *a$arri*
               (pop-literals ptr
                             (mv-nth 1 (push-literal lit a$))))
          (nth *a$arri*
               (pop-literals ptr a$))))
  :hints (("Goal" :in-theory (enable push-literal))))

(defthm a$arr-pop-literals-mv-nth-1-unit-propagation$
  (implies
   (and (a$p a$)
        (formula-p$ formula a$)
        (natp ptr)
        (<= ptr (nth *a$ptr* a$)))
   (equal (nth *a$arri*
               (pop-literals ptr
                             (mv-nth 1 (unit-propagation$ formula indices a$))))
          (nth *a$arri*
               (pop-literals ptr a$)))))

; Start proof of lst=-a$stk-for-pop-literals-mv-nth-1-unit-propagation$-2

(defthm list=-x-x
  (lst= ptr x x))

(defthm lst=pop-literals
  (implies (and (a$p a$)
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (lst= ptr
                 (nth *a$stki* (pop-literals ptr a$))
                 (nth *a$stki* a$))))

(defthmd lst=pop-literals-rewrite
  (implies (and (a$p a$)
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (and (equal (lst= ptr
                             (nth *a$stki* (pop-literals ptr a$))
                             stk)
                       (lst= ptr
                             (nth *a$stki* a$)
                             stk))
                (equal (lst= ptr
                             stk
                             (nth *a$stki* (pop-literals ptr a$)))
                       (lst= ptr
                             stk
                             (nth *a$stki* a$))))))

(defthm lst=-a$stk-for-pop-literals-mv-nth-1-push-literal
  (implies
   (and (a$p a$)
        (literalp$ lit a$)
        (natp ptr)
        (<= ptr (nth *a$ptr* a$)))
   (lst= ptr
         (nth *a$stki* (pop-literals ptr a$))
         (nth *a$stki*
              (pop-literals ptr
                            (mv-nth 1 (push-literal lit a$))))))
  :hints (("Goal" :in-theory (enable push-literal lst=pop-literals-rewrite))))

(defthm a$=-for-pop-literals-mv-nth-1-push-literal
  (implies (and (literalp$ lit a$)
                (a$p a$)
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (a$= (pop-literals ptr (mv-nth 1 (push-literal lit a$)))
                (pop-literals ptr a$)))
  :hints (("Goal" :in-theory (enable a$=))))

(defthm a$=-for-pop-literals-mv-nth-1-unit-propagation$
  (implies (and (force (a$p a$))
                (force (formula-p$ formula a$))
                (force (natp ptr))
                (force (<= ptr (nth *a$ptr* a$))))
           (a$= (pop-literals ptr
                              (mv-nth 1 (unit-propagation$ formula indices a$)))
                (pop-literals ptr a$))))

(defthm a$=-for-pop-literals-mv-nth-1-negate-clause
  (implies (and (a$p a$)
                (clausep$ clause (double-rewrite a$)) ; avoid warning
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (a$= (pop-literals ptr
                              (mv-nth 1 (negate-clause clause a$)))
                (pop-literals ptr a$))))

; Start proof of a$=-for-pop-literals-mv-nth-1-ratp1 (maybe started earlier
; above)

(defthm pop-literals-pop-literals
  (implies (and (natp ptr1)
                (<= ptr1 ptr2))
           (equal (pop-literals ptr1 (pop-literals ptr2 a$))
                  (pop-literals ptr1 a$))))

(defthm a$=-for-pop-literals-mv-nth-1-rat-assignment$
  (implies (and (a$p a$)
                (clausep$ clause a$)
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (a$= (pop-literals ptr
                              (mv-nth 1 (rat-assignment$ a$ nlit clause)))
                (pop-literals ptr a$))))

(in-theory (disable rat-assignment$ pop-literals))

(defthm a$=-for-pop-literals-mv-nth-1-ratp1
  (implies (and (a$p a$)
                (formula-p$ formula a$)
                (formula-p$ alist a$)
                (natp ptr)
                (<= ptr (nth *a$ptr* a$)))
           (a$= (pop-literals ptr
                              (mv-nth 1 (RATp1$ alist formula nlit drat-hints
                                               a$)))
                (pop-literals ptr a$)))
  :hints (("Goal" :induct (RATp1$ alist formula nlit drat-hints a$))))

(defthm pop-literals-no-op
  (implies (equal old-ptr (nth *a$ptr* a$))
           (equal (pop-literals old-ptr a$)
                  a$))
  :hints (("Goal" :in-theory (enable pop-literals))))

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

; Start proof of (verify-guards valid-proofp$)

(defun double-natp-induction (i j)

; We actually induct on j, but decrementing both i and j on the recursive call.

  (cond ((zp j) i) ; arbitrary value
        (t (double-natp-induction (1- i) (1- j)))))

(defthm nth-cons-0-resize-lst
  (implies (and (integerp n)
                (<= j n))
           (equal (nth j (cons 0 (resize-list nil n 0)))
                  0))
  :hints (("Goal"
           :in-theory (enable nth)
           :induct (double-natp-induction j n))))

(defun single-natp-induction (i)
  (cond ((zp i) i) ; arbitrary value
        (t (single-natp-induction (1- i)))))

(defthm a$p-initialize-a$-2
  (implies (and (integerp n)
                (<= j n))
           (a$arrp-rec j
                       (update-nth
                        *a$arri*
                        (cons 0 (resize-list nil n 0))
                        a$)))
  :hints (("Goal" :induct (single-natp-induction j))))

(defthm a$p-initialize-a$-3
  (implies (and (integerp n)
                (<= j n))
           (arr-matches-stk
            j
            (update-nth *a$ptr* 0
                        (update-nth *a$stki*
                                    (resize-list nil n nil)
                                    (update-nth *a$arri*
                                                (cons 0 (resize-list nil n 0))
                                                a$)))))
  :hints (("Goal" :induct (single-natp-induction j))))

(defthm a$p-initialize-a$
  (implies (and (true-listp a$)
                (equal (len a$) 3)
                (natp n))
           (a$p (initialize-a$ n a$)))
  :hints (("Goal" :in-theory (enable initialize-a$ a$p a$arrp))))

(defthm a$ptr-initialize-a$
  (equal (nth *a$ptr*
              (initialize-a$ n a$))
         0)
  :hints (("Goal" :in-theory (enable initialize-a$))))

(defthm natp-clause-max-var
  (implies (and (force (natp acc))
                (force (clausep clause)))
           (natp (clause-max-var clause acc)))
  :rule-classes :type-prescription)

(defthm natp-formula-max-var
  (implies (and (force (natp acc))
                (force (formula-p formula)))
           (natp (formula-max-var formula acc)))
  :rule-classes :type-prescription)

; Start proof of formula-p$-initialize-a$

; It seems easier to reason about the following two functions than their
; original tail-recursive analogues.

(defun clause-max-var-1 (clause)
  (cond ((endp clause) 0)
        (t (max (abs (car clause))
                (clause-max-var-1 (cdr clause))))))

(defthm clause-max-var-is-clause-max-var-1
  (implies (and (integerp acc)
                (<= 0 acc)
                (clausep clause))
           (equal (clause-max-var clause acc)
                  (max acc (clause-max-var-1 clause)))))

(defun formula-max-var-1 (formula)
  (cond ((atom formula) 0)
        ((deleted-clause-p (cdar formula))
         (formula-max-var-1 (cdr formula)))
        (t (max (clause-max-var-1 (cdar formula))
                (formula-max-var-1 (cdr formula))))))

(defthm formula-max-var-is-formula-max-var-1
  (implies (and (natp acc)
                (formula-p formula))
           (equal (formula-max-var formula acc)
                  (max acc (formula-max-var-1 formula)))))

(defthm len-a$arr-initialize-a$
  (implies (natp n)
           (equal (len (nth *a$arri* (initialize-a$ n a$)))
                  (1+ n)))
  :hints (("Goal" :in-theory (enable initialize-a$))))

(defthm literal-listp$-initialize-a$
  (implies (and (literal-listp literal-list)
                (natp n)
                (<= (clause-max-var-1 literal-list) n))
           (literal-listp$ literal-list
                           (initialize-a$ n a$)))
  :hints (("Goal" :in-theory (e/d (literal-listp$ literalp$)))))

(defthm clause-p$-initialize-a$
  (implies (and (clausep clause)
                (natp n)
                (<= (clause-max-var-1 clause) n))
           (clausep$ clause
                     (initialize-a$ n a$)))
  :hints (("Goal" :in-theory (enable clausep$))))

(defthm formula-p$-initialize-a$-lemma
  (implies (and (formula-p formula)
                (natp n)
                (<= (formula-max-var-1 formula) n))
           (formula-p$ formula
                       (initialize-a$ n a$))))

(defthm proof-max-var-inequality
  (implies (and (natp acc)
                (proofp proof))
           (<= acc (proof-max-var proof acc)))
  :rule-classes :linear)

(defthm natp-clause-max-var-1
  (implies (force (clausep clause))
           (natp (clause-max-var-1 clause)))
  :rule-classes :type-prescription)

(defthm natp-formula-max-var-1
  (implies (force (formula-p formula))
           (natp (formula-max-var-1 formula)))
  :rule-classes :type-prescription)

(defthm natp-proof-max-var
  (implies (and (proofp proof)
                (natp acc))
           (natp (proof-max-var proof acc)))
  :rule-classes :type-prescription)

(defthm formula-p$-initialize-a$
  (implies (and (formula-p formula)
                (proofp proof))
           (formula-p$ formula
                       (initialize-a$ (proof-max-var proof (formula-max-var formula 0))
                                      a$))))

; Start proof of proofp$-initialize-a$

; Again, it seem convenient to avoid reasoning about tail-recursive functions.

(defun proof-max-var-1 (proof)
  (cond
   ((endp proof) 0)
   ((proof-entry-deletion-p (car proof))
    (proof-max-var-1 (cdr proof)))
   (t (max (clause-max-var-1 (access add-step (car proof) :clause))
           (proof-max-var-1 (cdr proof))))))

(defthm proof-max-var-is-proof-max-var-1
  (implies (and (natp acc)
                (proofp proof))
           (equal (proof-max-var proof acc)
                  (max acc (proof-max-var-1 proof)))))

(defthm proofp$-initialize-a$-lemma
  (implies (and (proofp proof)
                (natp n)
                (<= (proof-max-var-1 proof) n))
           (proofp$ proof
                    (initialize-a$ n a$))))

(defthm natp-proof-max-var-1
  (implies (proofp proof)
           (natp (proof-max-var-1 proof)))
  :rule-classes :type-prescription)

(defthm proofp$-initialize-a$
  (implies (and (formula-p formula)
                (proofp proof))
           (proofp$ proof
                    (initialize-a$ (proof-max-var proof (formula-max-var formula 0))
                                   a$))))

(in-theory (disable clause-max-var-is-clause-max-var-1
                    formula-max-var-is-formula-max-var-1
                    proof-max-var-is-proof-max-var-1))

(verify-guards valid-proofp$)

; The following functions are relevant to the correctness statement.

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

; To be proved:
; (defthm main-theorem
;   (implies (and (formula-p formula)
;                 (refutation-p$ proof formula))
;            (not (satisfiable formula))))

; debugging tools

(defun show-a$-stk (i a$ acc)
  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$stk-length a$)))))
; Show stack below i.
  (cond ((zp i) acc)
        (t (let ((i (1- i)))
             (show-a$-stk i a$ (cons (a$stki i a$) acc))))))

(defun show-a$-arr (i a$ acc)
  (declare (xargs :stobjs a$
                  :guard (and (natp i)
                              (<= i (a$arr-length a$)))))
; Show array below i.
  (cond ((zp i) acc)
        (t (let ((i (1- i)))
             (show-a$-arr i a$ (cons (a$arri i a$) acc))))))

(defun show-a$ (a$)
  (declare (xargs :stobjs a$
                  :guard (<= (a$ptr a$) (a$stk-length a$))
                  :verify-guards nil))
  (list :a$ptr (a$ptr a$)
        :a$stk-length (a$stk-length a$)
        :a$arr-length (a$arr-length a$)
        :a$stk (show-a$-stk (a$ptr a$) a$ nil)
        :a$arr (show-a$-arr (a$arr-length a$) a$ nil)))
