(in-package "ACL2")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

; Section 11.5 Tautology Checking

; In this section, we define a notion of ifexp and prove the correctness
; of a simple tautology checker for such expressions.

(defun ifp (x)
  (and (consp x)
       (equal (car x) 'if)))

(defun test (x)
  (second x))

(defun tb (x)
  (third x))

(defun fb (x)
  (fourth x))

; ---------------------------------------------------------------------------
; Exercise 11.34

; Define the function if-exprp to recognize ifexp x.

(defun if-exprp (x)
  (cond
   ((ifp x)
    (and (true-listp x)
         (equal (len x) 4)
         (if-exprp (test x))
         (if-exprp (tb x))
         (if-exprp (fb x))))
   (t (atom x))))

(defun if-n (x)
  (declare (xargs :mode :program))
  (if (ifp x)
      (let ((test (test x))
            (tb (tb x))
            (fb (fb x)))
        (if (ifp test)
            (if-n (list 'if (test test)
                        (list 'if (tb test) tb fb)
                        (list 'if (fb test) tb fb)))
          (list 'if test (if-n tb) (if-n fb))))
    x))


; ---------------------------------------------------------------------------
; Exercise 11.35

; Add the above definition in :program mode and execute it on
; several examples.

; We cannot put test evaluations in books.  So our answer to this
; exercise is just a comment.

; ACL2 !>(if-n '(if (if alpha beta gamma) delta epsilon))
; (IF ALPHA
;     (IF BETA  DELTA EPSILON)
;     (IF GAMMA DELTA EPSILON))

; Hence, the first call of if-n above is problematic to justify:  its
; argument may be larger than the input.

; ---------------------------------------------------------------------------
; Exercise 11.36

; Admit if-n in :logic mode.

(include-book "arithmetic/top" :dir :system)

(defun if-depth (x)
  (if (ifp x)
      (+ 1 (if-depth (test x)))
    0))

(defun if-complexity (x)
  (if (ifp x)
      (* (if-complexity (test x))
         (+ (if-complexity (tb x))
            (if-complexity (fb x))))
    1))

; This command converts a :program mode function into a :logic mode
; function, after proving the measure conjectures.  We have to specify
; the measure to use.  It is the lexicographic combination of the two
; measures just defined.

(verify-termination
 if-n
 (declare (xargs :measure
		 (cons (+ 1 (if-complexity x))
		       (if-depth x)))))

; ---------------------------------------------------------------------------
; Exercise 11.37

; Admit if-n with a natural-number-valued measure function.  (We
; suspect that the measure function you used for the previous exercise
; returned ordinals past the naturals.)

; We cannot re-admit the function named if-n.  Nor can we undo a
; previously admitted function in a book to be certified, such as
; these solutions.  So we admit a re-named version of if-n just to
; show we can.

(defun natm (x)
  (if (ifp x)
      (+ (* 2 (natm (test x)))
         (* (natm (test x))
            (+ (natm (tb x)) (natm (fb x)))))
    1))

(defun if-n1 (x)
  (declare (xargs :measure (natm x)))
  (if (ifp x)
      (let ((test (test x))
            (tb (tb x))
            (fb (fb x)))
        (if (ifp test)
            (if-n1 (list 'if (test test)
                         (list 'if (tb test) tb fb)
                         (list 'if (fb test) tb fb)))
          (list 'if test (if-n1 tb) (if-n1 fb))))
    x))


; ---------------------------------------------------------------------------
; Exercise 11.38

; Define (peval x a) to determine the value of an if-expression, x,
; under the alist a.  For example, if x is '(if (if t c b) c b) and a
; is '((c . t) (b . nil)), then (peval x a) is t.  Notice that t and
; nil retain their status Boolean constants.

; The next function recognizes when x is a Boolean constant, e.g., t or nil.

(defun boolean-constantp (x)
  (or (equal x t)
      (equal x nil)))

; This returns the value under alist of the atomic symbol atm, which
; may be a Boolean constant and is otherwise a propositional variable symbol.

(defun atomic-val (atm alist)
  (if (boolean-constantp atm)
      atm
    (cdr (assoc-equal atm alist))))

; And so here is the recursive evaluation function for if-expressions.

(defun peval (x alist)
  (cond ((ifp x)
         (if (peval (test x) alist)
             (peval (tb x) alist)
           (peval (fb x) alist)))
        (t (atomic-val x alist))))

; ---------------------------------------------------------------------------
; Exercise 11.39

; Define (tautp x) to recognize ``tautologies'' if-expressions s that
; evaluate to t under all alists.  (Hint: Consider normalizing the
; if-expression and then exploring all paths through it.)

; The next function determines whether the value of the atomic symbol atm is
; already assigned in alist.  Boolean constants are always considered
; assigned.

(defun assignedp (atm alist)
   (or (boolean-constantp atm)
       (assoc-equal atm alist)))

; The next two functions add new binding pairs to an assignment.  The first
; assigns the value t to the variable, the second assigns the value nil.

(defun assume-true (var alist)
   (cons (cons var t)
         alist))

(defun assume-false (var alist)
  (cons (cons var nil)
        alist))

; This is the exploration function.  It walks through the if-expression x and
; steers through any test whose value is already assigned.  Of course, every
; test must be an atomic symbol, so x should be in if-normal form.  When
; tautp reaches a test that is unassigned, it checks that both branches lead
; to tautologies, provided the test is assigned appropriately.

(defun tautp (x alist)
  (if (ifp x)
      (if (assignedp (test x) alist)
          (if (atomic-val (test x) alist)
              (tautp (tb x) alist)
            (tautp (fb x) alist))
        (and (tautp (tb x)
                    (assume-true (test x) alist))
             (tautp (fb x)
                    (assume-false (test x) alist))))
    (atomic-val x alist)))

; So the tautology checking algorithm is just:  normalize the expression
; and then walk through it checking each branch.

(defun tautology-checker (x)
   (tautp (if-n x) nil))

; ---------------------------------------------------------------------------
; Exercise 11.40

; Prove that tautp is sound: when tautp returns t, its argument
; evaluates to non-nil under every alist.

; Here we determine if x is in if-normal form.

(defun normp (x)
  (if (ifp x)
      (and (not (ifp (test x)))
           (normp (tb x))
           (normp (fb x)))
    t))

; These lemmas were generated with The Method.  Append was introduced
; into the problem in tautp-implies-peval, below, because we must
; generalize from the empty initial assignment to an arbitrary one.

(defthm assoc-equal-append
  (implies (alistp a)
           (equal (assoc-equal v (append a b))
                  (if (assoc-equal v a)
                      (assoc-equal v a)
                    (assoc-equal v b)))))

; If a variable is already assigned value val, a new pair binding it to
; val can be ignored (in the sense that no peval is changed).

(defthm peval-ignores-redundant-assignments
  (implies (iff (cdr (assoc-equal var alist)) val)
           (iff (peval x (cons (cons var val) alist))
                (peval x alist))))

; So here is the main soundness result about tautp: if the expression is in
; if-normal form and is a tautology under some assignment, then its value is
; true under any extension of that assignment.  In our intended use, b will
; be nil, and so the (append b a) expression will just be a.  Thus, this
; lemma is not going to be used as a rewrite rule -- (append nil a) will not
; occur in the target.  Instead we will :use it explicitly.  So we make it of
; :rule-classes nil.

(defthm tautp-implies-peval
  (implies (and (alistp b)
                (normp x)
                (tautp x b))
           (peval x (append b a)))
  :rule-classes nil)

; Now we deal with the normalization phase.  We prove that if-n normalizes
; while preserving the value under all assignments.

(defthm normp-if-n
  (normp (if-n x)))

(defthm peval-if-n
  (equal (peval (if-n x) a)
         (peval x a)))

; We can now put these together.

(defthm tautology-checker-is-sound
  (implies (tautology-checker x)
           (peval x a))
  :hints (("Goal" :use (:instance tautp-implies-peval
                                  (x (if-n x))
                                  (b nil)))))


; ---------------------------------------------------------------------------
; Exercise 11.41

; Prove that tautp is complete: when tautp returns nil, there is some
; alist under which the if-expression evaluates to nil.

; This function constructs a falsifying assignment to a normalized
; if-expression by extending alist, if possible.  The function returns two
; values, (mv ans alist').  Ans is either t or nil and indicates whether a
; falsifying assignment was found.  Alist' is relevant only when ans is t and
; is the falsifying assignment.  We need to know whether the attempt to
; falsify a branch succeeds or not, so we can select the branch that can be
; falsified, if either.  The reason we need two values is that the falsifying
; assignment might be the empty assignment.  Of course, we could have coded
; that up as some special value but this is more elegant.

(defun falsify (x alist)
  (if (ifp x)
      (if (assignedp (test x) alist)
          (if (atomic-val (test x) alist)
              (falsify (tb x) alist)
            (falsify (fb x) alist))
        (mv-let (ans new-alist)
                (falsify (tb x)
                         (assume-true (test x) alist))
                (if ans
                    (mv ans new-alist)
                  (falsify (fb x)
                           (assume-false (test x) alist)))))
    (if (assignedp x alist)
        (if (atomic-val x alist)
            (mv nil nil)
          (mv t alist))
      (mv t (assume-false x alist)))))

; Assuming that there is a falsifying assignment, this function returns it.
; Note that the first result of falsify is just ignored.

(defun falsifying-alist (x)
  (mv-let (ans alist)
          (falsify (if-n x) nil)
          (declare (ignore ans))
          alist))

; Part of the specification of falsify is that on non-tautological normalized
; if-expressions, the first result of falsify is t.  The first result is
; (mv-nth 0 ...).

(defthm when-tautp-fails-falsify-wins
  (implies (and (normp x)
                (not (tautp x a)))
           (mv-nth 0 (falsify x a)))
  :rule-classes nil)

; Another part of the spec is that the assignment it returns extends
; the given one, when falsify succeeds.

(defthm falsify-extends-alists
  (implies (and (mv-nth 0 (falsify x alist))
                (assoc-equal var alist))
           (equal (assoc-equal var (mv-nth 1 (falsify x alist)))
                  (assoc-equal var alist))))

; The final part is that when falsify's first result is t (on a normalized
; if-expression), its second is a falsifying assignment.

(defthm when-falsify-wins-it-falsifies
  (implies (and (normp x)
                (mv-nth 0 (falsify x a)))
           (not (peval x (mv-nth 1 (falsify x a)))))
  :rule-classes nil)

; And so here is the final result.

(defthm tautology-checker-is-complete
  (implies (not (tautology-checker x))
           (not (peval x (falsifying-alist x))))
  :hints (("Goal" :use ((:instance when-tautp-fails-falsify-wins
                                   (x (if-n x))
                                   (a nil))
                        (:instance when-falsify-wins-it-falsifies
                                   (x (if-n x))
                                   (a nil))))))
