; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;

; extra-operations.lisp - additional bdd operations (q-and, q-or, etc.)

(in-package "ACL2")
(include-book "core")

(local (defun q-binop-induct (x y vals)
         (declare (xargs :verify-guards nil))
         (if (atom x)
             (list x y vals)
           (if (atom y)
               nil
             (if (car vals)
                 (q-binop-induct (car x) (car y) (cdr vals))
               (q-binop-induct (cdr x) (cdr y) (cdr vals)))))))


(defsection cheap-and-expensive-arguments
  :parents (ubdd-constructors)
  :short "Sort arguments into those that we think are definitely cheap to evaluate
versus those that may be expensive."

  :long "<p>This is the same idea as in @(see q-ite).  Variables and quoted
constants are cheap to evaluate, so in associative/commutative operations like
@(see q-and) we prefer to evaluate them first.</p>"

  (defun cheap-and-expensive-arguments-aux (x cheap expensive)
    (declare (xargs :mode :program))
    (if (atom x)
        (mv cheap expensive)
      (if (or (quotep (car x))
              (atom (car x)))
          (cheap-and-expensive-arguments-aux (cdr x) (cons (car x) cheap) expensive)
        (cheap-and-expensive-arguments-aux (cdr x) cheap (cons (car x) expensive)))))

  (defun cheap-and-expensive-arguments (x)
    (declare (xargs :mode :program))
    (mv-let (cheap expensive)
            (cheap-and-expensive-arguments-aux x nil nil)
            (mv (reverse cheap) (reverse expensive)))))


(defsection q-and
  :parents (ubdd-constructors)
  :short "@(call q-and) constructs a UBDD representing the conjunction of its
arguments."

  :long "<p>In the logic,</p>

@({
 (Q-AND)        = T
 (Q-AND X)      = X
 (Q-AND X Y)   = (Q-BINARY-AND X Y)
 (Q-AND X Y Z) = (Q-BINARY-AND X (Q-BINARY-AND Y Z))
 ... etc ...
})

<p>But as a special optimization, in the execution, when there is more than one
argument, we can sometimes \"short-circuit\" the computation and avoid
evaluating some arguments.  In particular, we classify the arguments as cheap
or expensive using @(see cheap-and-expensive-arguments).  We then arrange
things so that the cheap arguments are considered first.  If any cheap argument
is @('nil'), we can stop before any expensive arguments even need to be
computed.</p>"

  (defund q-binary-and (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x
               ;; [Jared hack]: normalize in the atom case for fewer hyps
               (if (atom y) (if y t nil) y)
             nil))
          ((atom y)
           ;; We know x is not an atom, so no need to normalize
           (if y x nil))
          ((hons-equal x y)
           x)
          (t
           (qcons (q-binary-and (car x) (car y))
                  (q-binary-and (cdr x) (cdr y))))))

  (add-bdd-fn q-binary-and)

  (defun q-and-macro-logic-part (args)
    ;; Generates the :logic part for a q-and MBE call.
    (declare (xargs :mode :program))
    (cond ((atom args)
           t)
          ((atom (cdr args))
           (car args))
          (t
           `(q-binary-and ,(car args) ,(q-and-macro-logic-part (cdr args))))))

  (defun q-and-macro-exec-part (args)
    ;; Generates the :exec part for a q-and MBE call.
    (declare (xargs :mode :program))
    (cond ((atom args)
           t)
          ((atom (cdr args))
           (car args))
          (t
           `(let ((q-and-x-do-not-use-elsewhere ,(car args)))
              (and q-and-x-do-not-use-elsewhere
                   (prog2$
                    (last-chance-wash-memory)
                    (q-binary-and q-and-x-do-not-use-elsewhere
                                  ,(q-and-macro-exec-part (cdr args)))))))))

  (defun q-and-macro-fn (args)
    (declare (xargs :mode :program))
    (cond ((atom args)
           t)
          ((atom (cdr args))
           (car args))
          (t
           (mv-let (cheap expensive)
                   (cheap-and-expensive-arguments args)
                   (if (not expensive)
                       ;; If everything is cheap, there's no reason to bother
                       ;; with all this MBE stuff.
                       (q-and-macro-logic-part cheap)
                     ;; Otherwise, try to process the cheap arguments first in
                     ;; hopes of avoiding as many expensive computations as
                     ;; possible.  It would be nice if the :logic part below did
                     ;; not have to have the arguments reordered, but to do that
                     ;; we need a hyp-free associativity rule for q-and (for our
                     ;; guard theorems), and that's hard.  Oh well.
                     (let ((reordered-args (append cheap expensive)))
                       `(mbe :logic ,(q-and-macro-logic-part reordered-args)
                             :exec ,(q-and-macro-exec-part reordered-args))))))))

  (defmacro q-and (&rest args)
    (q-and-macro-fn args))

  (add-macro-alias q-and q-binary-and)
  (add-binop q-and q-binary-and)

  (local (in-theory (enable q-and)))

  (defthm ubddp-of-q-and
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-and x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-and
    (equal (eval-bdd (q-and x y) values)
           (and (eval-bdd x values)
                (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (enable eval-bdd)
            :induct (q-binop-induct x y values)
            :expand (q-and x y))))

  (defthm canonicalize-q-and
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-and x y)
                    (q-ite x y nil))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-and))

  ;; One strategy is to canonicalize away q-and into q-ite whenever it is seen,
  ;; using canonicalize-q-and.  But if this strategy is not being followed,
  ;; weak-boolean-listp may find the following theorems useful.  It is
  ;; important that these theorems come after canonicalize-q-and, since in
  ;; particular q-and-of-nil is to verify the guards when the q-and macro is
  ;; being used.

  (defthm q-and-of-nil
    (and (equal (q-and nil x) nil)
         (equal (q-and x nil) nil))
    :hints(("Goal" :in-theory (disable canonicalize-q-and))))

  (defthm q-and-of-t-slow
    (and (equal (q-and t x) (if (consp x) x (if x t nil)))
         (equal (q-and x t) (if (consp x) x (if x t nil))))
    :hints(("Goal" :in-theory (disable canonicalize-q-and))))

  (defthm q-and-of-t-aggressive
    (implies (force (ubddp x))
             (and (equal (q-and t x) x)
                  (equal (q-and x t) x))))

  (defthm q-and-symmetric
    (equal (q-and x y)
           (q-and y x))
    :hints(("Goal" :in-theory (disable equal-by-eval-bdds
                                       canonicalize-q-and))))

  (memoize 'q-binary-and
           :condition '(and (consp x) (consp y))
           :commutative 'q-and-symmetric)

  (defthm q-and-of-self-slow
    (equal (q-and x x) (if (consp x) x (if x t nil))))

  (defthm q-and-of-self-aggressive
    (implies (force (ubddp x))
             (equal (q-and x x) x)))

  ;; The following ensures that a trivial usage of our Q-AND macro
  ;; will succeed in guard verification.

  (local (in-theory (disable q-and)))

  (local (defun test-q-and (a b c x y z)
           (declare (xargs :guard t
                           :guard-hints
                           (("Goal" :in-theory (disable (force))))))
           (list (q-and x y)
                 (q-and x (q-not y))
                 (q-and (q-not x) y)
                 (q-and x y (q-not x) a b (q-ite y z c))))))


(defsection q-or
  :parents (ubdd-constructors)
  :short "@(call q-or) constructs a UBDD representing the disjunction of its
arguments."
  :long "<p>In the logic,</p>

@({
 (Q-OR)       = NIL
 (Q-OR X)     = X
 (Q-OR X Y)   = (Q-BINARY-OR X Y)
 (Q-OR X Y Z) = (Q-BINARY-OR X (Q-BINARY-OR Y Z))
})

<p>In the execution, we use the same sort of optimization as in @(see
q-and).</p>"

  (defund q-binary-or (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x
               t
             ;; [Jared hack]: normalize atoms
             (if (atom y) (if y t nil) y)))
          ((atom y)
           ;; We know x is not an atom, so no need to normalize.
           (if y t x))
          ((hons-equal x y)
           x)
          (t
           (let ((l (q-binary-or (car x) (car y)))
                 (r (q-binary-or (cdr x) (cdr y))))
             (qcons l r)))))

  (add-bdd-fn q-binary-or)

  (defun q-or-macro-logic-part (args)
    (declare (xargs :mode :program))
    (cond ((atom args)
           nil)
          ((atom (cdr args))
           (car args))
          (t
           `(q-binary-or ,(car args) ,(q-or-macro-logic-part (cdr args))))))

  (defun q-or-macro-exec-part (args)
    (declare (xargs :mode :program))
    (cond ((atom args)
           nil)
          ((atom (cdr args))
           (car args))
          (t
           `(let ((q-or-x-do-not-use-elsewhere ,(car args)))
              ;; We could be slightly more permissive and just check
              ;; for any non-nil atom here.  But it's probably faster
              ;; to check equality with t and we probably don't care
              ;; about performance on non-ubddp bdds?
              (if (eq t q-or-x-do-not-use-elsewhere)
                  t
                (prog2$
                 (last-chance-wash-memory)
                 (q-binary-or q-or-x-do-not-use-elsewhere
                              ,(q-or-macro-exec-part (cdr args)))))))))

  (defun q-or-macro-fn (args)
    (declare (xargs :mode :program))
    (cond ((atom args)
           nil)
          ((atom (cdr args))
           (car args))
          (t
           (mv-let (cheap expensive)
                   (cheap-and-expensive-arguments args)
                   (if (not expensive)
                       (q-or-macro-logic-part cheap)
                     (let ((reordered-args (append cheap expensive)))
                       `(mbe :logic ,(q-or-macro-logic-part reordered-args)
                             :exec ,(q-or-macro-exec-part reordered-args))))))))

  (defmacro q-or (&rest args)
    (q-or-macro-fn args))

  (add-macro-alias q-or q-binary-or)
  (add-binop q-or q-binary-or)

  (local (in-theory (enable q-or)))

  (defthm ubddp-of-q-or
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-or x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-or
    (equal (eval-bdd (q-or x y) values)
           (or (eval-bdd x values)
               (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (enable eval-bdd)
            :induct (q-binop-induct x y values)
            :expand (q-or x y))))

  (defthm canonicalize-q-or
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-or x y)
                    (q-ite x t y))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-or))

  (defthm q-or-of-nil-slow
    (and (equal (q-or nil x) (if (consp x) x (if x t nil)))
         (equal (q-or x nil) (if (consp x) x (if x t nil)))))

  (defthm q-or-of-nil-aggressive
    (implies (force (ubddp x))
             (and (equal (q-or nil x) x)
                  (equal (q-or x nil) x))))

  (defthm q-or-of-t
    (and (equal (q-or t x) t)
         (equal (q-or x t) t))
    :hints(("Goal" :in-theory (disable canonicalize-q-or))))

  (defthm q-or-symmetric
    (equal (q-or x y)
           (q-or y x))
    :hints(("Goal" :in-theory (disable canonicalize-q-or
                                       q-or-of-nil-aggressive
                                       equal-by-eval-bdds))))

  (memoize 'q-binary-or
           :condition '(and (consp x) (consp y))
           :commutative 'q-or-symmetric)

  (defthm q-or-of-self-slow
    (equal (q-or x x)
           (if (consp x) x (if x t nil))))

  (defthm q-or-of-self-aggressive
    (implies (force (ubddp x))
             (equal (q-or x x) x)))

  (local (in-theory (disable q-or)))

  (local (defun test-q-or (a b c x y z)
           (declare (xargs :guard t))
           (list (q-or x y)
                 (q-or x (q-not y))
                 (q-or (q-not x) y)
                 (q-or x y (q-not x) a b (q-ite y z c))))))


(defsection q-implies
  :parents (ubdd-constructors)
  :short "@(call q-implies) constructs a UBDD representing @('(implies x y)')."

  (defund q-implies-fn (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x
               ;; [Jared hack]: changing this base case to get
               ;; always-boolean behavior on atoms.  Previously this
               ;; was just "y".
               (if (atom y)
                   (if y t nil)
                 y)
             t))
          ((atom y)
           (if y t (q-not x)))
          ((hons-equal x y)
           t)
          (t
           (qcons (q-implies-fn (car x) (car y))
                  (q-implies-fn (cdr x) (cdr y))))))

  (memoize 'q-implies-fn :condition '(and (consp x) (consp y)))

  (add-bdd-fn q-implies-fn)

  (defun q-implies-macro-fn (x y)
    (declare (xargs :mode :program))
    (cond ((and (or (quotep x) (atom x))
                (or (quotep y) (atom y)))
           ;; X and Y both look cheap.  Don't optimize anything.
           `(q-implies-fn ,x ,y))
          ((or (quotep y) (atom y))
           ;; Y looks cheap. Try to avoid computing X.
           `(mbe :logic (q-implies-fn ,x ,y)
                 :exec (let ((q-implies-y-do-not-use-elsewhere ,y))
                         (if (eq t q-implies-y-do-not-use-elsewhere)
                             t
                           (prog2$
                            (last-chance-wash-memory)
                            (q-implies-fn ,x q-implies-y-do-not-use-elsewhere))))))
          (t
           ;; Try to avoid computing Y.
           `(mbe :logic (q-implies-fn ,x ,y)
                 :exec (let ((q-implies-x-do-not-use-elsewhere ,x))
                         (if (not q-implies-x-do-not-use-elsewhere)
                             t
                           (prog2$
                            (last-chance-wash-memory)
                            (q-implies-fn q-implies-x-do-not-use-elsewhere
                                          ,y))))))))

  (defmacro q-implies (x y)
    (q-implies-macro-fn x y))

  (add-macro-alias q-implies q-implies-fn)

  (local (in-theory (enable q-implies)))

  (defthm ubddp-of-q-implies
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-implies x y))
                    t))
    :hints(("Goal" :in-theory (e/d (ubddp)
                                   (canonicalize-q-not)))))

  (defthm eval-bdd-of-q-implies
    (equal (eval-bdd (q-implies x y) values)
           (implies (eval-bdd x values)
                    (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-implies x y))))

  (defthm canonicalize-q-implies
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-implies x y)
                    (q-ite x y t))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-implies))

  (defthm q-implies-of-nil
    (and (equal (q-implies nil x) t)
         (equal (q-implies x nil) (q-not x)))
    :hints(("Goal" :in-theory (e/d (q-not)
                                   (canonicalize-q-not
                                    canonicalize-q-implies)))))

  (defthm q-implies-of-t-left-slow
    (equal (q-implies t x) (if (consp x) x (if x t nil)))
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (defthm q-implies-of-t-left-aggressive
    (implies (force (ubddp x))
             (equal (q-implies t x) x))
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (defthm q-implies-of-t-right
    (equal (q-implies x t) t)
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (defthm q-implies-of-self
    (equal (q-implies x x) t)
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (local (in-theory (disable q-implies)))

  (local (defun test-q-implies (a b)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-implies a b)
                 (q-implies a (q-not b))
                 (q-implies (q-not b) a)
                 (q-implies (q-not a) (q-not b))))))



(defsection q-or-c2
  :parents (ubdd-constructors)
  :short "@(call q-or-c2) constructs a UBDD representing @('(or x (not y))')."

  (defund q-or-c2-fn (x y)
    (declare (xargs :guard t))
    (cond ((atom y)
           (if y x t))
          ((atom x)
           (if x t (q-not y)))
          ((hons-equal x y)
           t)
          (t (qcons (q-or-c2-fn (car x) (car y))
                    (q-or-c2-fn (cdr x) (cdr y))))))

  (add-bdd-fn q-or-c2-fn)

  (defun q-or-c2-macro-fn (x y)
    (declare (xargs :mode :program))
    (cond ((and (or (quotep x) (atom x))
                (or (quotep y) (atom y)))
           ;; Both look cheap.  Don't try to avoid anything.
           `(q-or-c2-fn ,x ,y))
          ((or (quotep y) (atom y))
           ;; Y looks cheap.  Try to avoid computing X.
           `(mbe :logic (q-or-c2-fn ,x ,y)
                 :exec (let ((q-or-c2-y-do-not-use-elsewhere ,y))
                         (if (not q-or-c2-y-do-not-use-elsewhere)
                             t
                           (prog2$
                            (last-chance-wash-memory)
                            (q-or-c2-fn ,x q-or-c2-y-do-not-use-elsewhere))))))
          (t
           ;; Try to avoid computing Y.
           `(mbe :logic (q-or-c2-fn ,x ,y)
                 :exec (let ((q-or-c2-x-do-not-use-elsewhere ,x))
                         (if (eq q-or-c2-x-do-not-use-elsewhere t)
                             t
                           (prog2$
                            (last-chance-wash-memory)
                            (q-or-c2-fn q-or-c2-x-do-not-use-elsewhere ,y))))))))

  (defmacro q-or-c2 (x y)
    (q-or-c2-macro-fn x y))

  (add-macro-alias q-or-c2 q-or-c2-fn)
  (local (in-theory (enable q-or-c2)))

  (memoize 'q-or-c2   :condition '(and (consp x) (consp y)))

  (defthm ubddp-of-q-or-c2
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-or-c2 x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-or-c2
    (equal (eval-bdd (q-or-c2 x y) values)
           (implies (eval-bdd y values)
                    (eval-bdd x values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-or-c2 x y))))

  (defthm canonicalize-q-or-c2
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-or-c2 x y)
                    (q-ite y x t))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-or-c2))

  (defthm q-or-c2-of-t
    (and (equal (q-or-c2 t x) t)
         (equal (q-or-c2 x t) x))
    :hints(("Goal" :in-theory (disable canonicalize-q-or-c2))))

  (defthm q-or-c2-of-nil
    (and (equal (q-or-c2 nil x) (q-not x))
         (equal (q-or-c2 x nil) t))
    :hints(("Goal" :in-theory (e/d (q-not)
                                   (canonicalize-q-not
                                    canonicalize-q-or-c2)))))

  (local (in-theory (disable q-or-c2)))

  (local (defun test-q-or-c2 (a b)
           (declare (xargs :guard t))
           (list (q-or-c2 a b)
                 (q-or-c2 a (q-not b))
                 (q-or-c2 (q-not a) b)
                 (q-or-c2 (q-not a) (q-not b))))))


(defsection q-and-c1
  :parents (ubdd-constructors)
  :short "@(call q-and-c1) constructs a UBDD representing @('(and (not x) y)')."

  (defund q-and-c1-fn (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x nil y))
          ((atom y)
           (if y (q-not x) nil))
          ((hons-equal x y)
           nil)
          (t
           (qcons (q-and-c1-fn (car x) (car y))
                  (q-and-c1-fn (cdr x) (cdr y))))))

  (memoize 'q-and-c1-fn  :condition '(and (consp x) (consp y)))

  (add-bdd-fn q-and-c1-fn)

  (defun q-and-c1-macro-fn (x y)
    (declare (xargs :mode :program))
    (cond ((and (or (quotep x) (atom x))
                (or (quotep y) (atom y)))
           ;; Both look cheap.  Don't try to avoid anything.
           `(q-and-c1-fn ,x ,y))
          ((or (quotep y) (atom y))
           ;; Y looks cheap.  Try to avoid computing X.
           `(mbe :logic (q-and-c1-fn ,x ,y)
                 :exec (let ((q-and-c1-y-do-not-use-elsewhere ,y))
                         (if (not q-and-c1-y-do-not-use-elsewhere)
                             nil
                           (prog2$
                            (last-chance-wash-memory)
                            (q-and-c1-fn ,x q-and-c1-y-do-not-use-elsewhere))))))
          (t
           ;; Try to avoid computing Y.
           `(mbe :logic (q-and-c1-fn ,x ,y)
                 :exec (let ((q-and-c1-x-do-not-use-elsewhere ,x))
                         (if (eq t q-and-c1-x-do-not-use-elsewhere)
                             nil
                           (prog2$
                            (last-chance-wash-memory)
                            (q-and-c1-fn q-and-c1-x-do-not-use-elsewhere ,y))))))))

  (defmacro q-and-c1 (x y)
    (q-and-c1-macro-fn x y))

  (add-macro-alias q-and-c1 q-and-c1-fn)
  (local (in-theory (enable q-and-c1)))

  (defthm ubddp-of-q-and-c1
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-and-c1 x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-and-c1
    (equal (eval-bdd (q-and-c1 x y) values)
           (if (eval-bdd x values)
               nil
             (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-and-c1 x y))))

  (defthm canonicalize-q-and-c1
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-and-c1 x y)
                    (q-ite x nil y))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-and-c1))

  (defthm q-and-c1-of-nil
    (and (equal (q-and-c1 nil x) x)
         (equal (q-and-c1 x nil) nil))
    :hints(("Goal" :in-theory (disable canonicalize-q-and-c1))))

  (defthm q-and-c1-of-t
    (and (equal (q-and-c1 t x) nil)
         (equal (q-and-c1 x t) (q-not x)))
    :hints(("Goal" :in-theory (e/d (q-not)
                                   (canonicalize-q-and-c1
                                    canonicalize-q-not)))))

  (local (in-theory (disable q-and-c1)))

  (local (defun test-q-and-c1 (a b)
           (declare (xargs :guard t))
           (list (q-and-c1 a b)
                 (q-and-c1 a (q-not b))
                 (q-and-c1 (q-not a) b)
                 (q-and-c1 (q-not a) (q-not b))))))


(defsection q-and-c2
  :parents (ubdd-constructors)
  :short "@(call q-and-c2) constructs a UBDD representing @('(and x (not y))')."

  (defund q-and-c2-fn (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x (q-not y) nil))
          ((atom y)
           (if y nil x))
          ((hons-equal x y)
           nil)
          (t
           (qcons (q-and-c2-fn (car x) (car y))
                  (q-and-c2-fn (cdr x) (cdr y))))))

  (memoize 'q-and-c2-fn  :condition '(and (consp x) (consp y)))

  (add-bdd-fn q-and-c2-fn)

  (defun q-and-c2-macro-fn (x y)
    (declare (xargs :mode :program))
    (cond ((and (or (quotep x) (atom x))
                (or (quotep y) (atom y)))
           ;; Both look cheap.  Don't try to avoid anything.
           `(q-and-c2-fn ,x ,y))
          ((or (quotep y) (atom y))
           ;; Y looks cheap.  Try to avoid computing X.
           `(mbe :logic (q-and-c2-fn ,x ,y)
                 :exec (let ((q-and-c2-y-do-not-use-elsewhere ,y))
                         (if (eq t q-and-c2-y-do-not-use-elsewhere)
                             nil
                           (prog2$
                            (last-chance-wash-memory)
                            (q-and-c2-fn ,x q-and-c2-y-do-not-use-elsewhere))))))
          (t
           ;; Try to avoid computing Y.
           `(mbe :logic (q-and-c2-fn ,x ,y)
                 :exec (let ((q-and-c2-x-do-not-use-elsewhere ,x))
                         (if (not q-and-c2-x-do-not-use-elsewhere)
                             nil
                           (prog2$
                            (last-chance-wash-memory)
                            (q-and-c2-fn q-and-c2-x-do-not-use-elsewhere ,y))))))))

  (defmacro q-and-c2 (x y)
    (q-and-c2-macro-fn x y))

  (add-macro-alias q-and-c2 q-and-c2-fn)
  (local (in-theory (enable q-and-c2)))

  (defthm ubddp-of-q-and-c2
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-and-c2 x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-and-c2
    (equal (eval-bdd (q-and-c2 x y) values)
           (if (eval-bdd y values)
               nil
             (eval-bdd x values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-and-c2 x y))))

  (defthm canonicalize-q-and-c2
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-and-c2 x y)
                    (q-ite y nil x))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-and-c2))

  (defthm q-and-c2-of-nil-left
    (equal (q-and-c2 nil x) nil)
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm q-and-c2-of-nil-right-slow
    (equal (q-and-c2 x nil) (if (consp x) x (if x t nil))))

  (defthm q-and-c2-of-nil-right-aggressive
    (implies (force (ubddp x))
             (equal (q-and-c2 x nil) x)))

  (defthm q-and-c2-of-t
    (and (equal (q-and-c2 t x) (q-not x))
         (equal (q-and-c2 x t) nil))
    :hints(("Goal" :in-theory (disable (force)))))

  (local (in-theory (disable q-and-c2)))

  (local (defun test-q-and-c2 (a b)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-and-c2 a b)
                 (q-and-c2 a (q-not b))
                 (q-and-c2 (q-not a) b)
                 (q-and-c2 (q-not a) (q-not b))))))


(defsection q-iff
  :parents (ubdd-constructors)
  :short "@(call q-iff) constructs a UBDD representing an equality/iff-equivalence."
  :long "<p>In the logic, for instance,</p>

@({
  (q-iff x1 x2 x3 x4) = (q-and (q-binary-iff x1 x2)
                               (q-binary-iff x1 x3)
                               (q-binary-iff x1 x4))
})

<p>We do not see how to use short-circuiting to improve upon @('(q-binary-iff x
y)'), since the answer depends upon both inputs in all cases.  But when we
implement the multiple-input @('q-iff') macro, we can at least take advantage
of the short-circuiting provided by @(see q-and).  We also reorder the inputs
so that cheap ones come first, hoping that we can avoid evaluating expensive
arguments.</p>"

  (defund q-binary-iff (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x y (q-not y)))
          ((atom y)
           (if y x (q-not x)))
          ((hons-equal x y)
           t)
          (t
           (qcons (q-binary-iff (car x) (car y))
                  (q-binary-iff (cdr x) (cdr y))))))

  (memoize 'q-binary-iff     :condition '(and (consp x) (consp y)))

  (add-bdd-fn q-binary-iff)

  (defun q-iff-macro-guts (a x)
    ;; Produces (LIST (Q-BINARY-IFF A X1) (Q-BINARY-IFF A X2) ...)
    (declare (xargs :mode :program))
    (if (consp x)
        (cons `(q-binary-iff ,a ,(car x))
              (q-iff-macro-guts a (cdr x)))
      nil))

  (defun q-iff-macro-fn (args)
    (declare (xargs :mode :program))
    (if (equal (len args) 2)
        `(prog2$
          (last-chance-wash-memory)
          (q-binary-iff ,(car args) ,(cadr args)))
      (mv-let (cheap expensive)
              (cheap-and-expensive-arguments args)
              (let ((reordered-args (append cheap expensive)))
                `(let ((a-for-q-iff-do-not-use-elsewhere ,(car reordered-args)))
                   (prog2$
                    (last-chance-wash-memory)
                    (Q-AND . ,(q-iff-macro-guts 'a-for-q-iff-do-not-use-elsewhere
                                                (cdr reordered-args)))))))))

  (defmacro q-iff (a b &rest args)
    (declare (xargs :guard (true-listp args)))
    (q-iff-macro-fn (list* a b args)))

  (add-macro-alias q-iff q-binary-iff)
  (local (in-theory (enable q-iff)))

  (defthm ubddp-of-q-iff
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-iff x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-iff
    (equal (eval-bdd (q-iff x y) values)
           (iff (eval-bdd x values)
                (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-iff x y))))

  (defthm canonicalize-q-iff
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-iff x y)
                    (q-ite x y (q-ite y nil t)))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-iff))

  (local (in-theory (disable q-iff)))

  (local (defun test-q-iff (a b c d)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-iff a b)
                 (q-iff a b c (q-not b))
                 (q-iff (q-not a) (q-not b) c d)))))

(defsection q-nand
  :parents (ubdd-constructors)
  :short "@(call q-nand) constructs a UBDD representing the NAND of its arguments."
  :long "<p>For instance:</p>
@({
 (q-nand)         = nil
 (q-nand a)       = (q-not a)
 (q-nand a b ...) = (q-not (q-and a b ...))
})

@(def q-nand)"

  (defmacro q-nand (&rest args)
    `(q-not (q-and . ,args))))


(defsection q-nor
  :parents (ubdd-constructors)
  :short "@(call q-nor) constructs a UBDD representing the NOR of its arguments."
  :long "<p>For instance:</p>
@({
 (q-nor)         = t
 (q-nor a)       = (q-not a)
 (q-nor a b ...) = (q-not (q-or a b ...))
})

@(def q-nor)"

  (defmacro q-nor (&rest args)
    `(q-not (q-or . ,args))))



(defsection q-xor
  :parents (ubdd-constructors)
  :short "@(call q-xor) constructs a UBDD representing the exclusive OR of its
arguments."

  (defund q-binary-xor (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if x (q-not y) y))
          ((atom y)
           (if y (q-not x) x))
          ((hons-equal x y)
           nil)
          (t
           (qcons (q-binary-xor (car x) (car y))
                  (q-binary-xor (cdr x) (cdr y))))))

  (memoize 'q-binary-xor     :condition '(and (consp x) (consp y)))

  (add-bdd-fn q-binary-xor)

  ;; It needs all the bits, so I don't see how to make a lazy version.

  (defun q-xor-macro-fn (args)
    (declare (xargs :guard (consp args)))
    (if (atom (cdr args))
        (car args)
      `(prog2$
        (last-chance-wash-memory)
        (q-binary-xor ,(car args)
                      ,(q-xor-macro-fn (cdr args))))))

  (defmacro q-xor (a b &rest args)
    (q-xor-macro-fn (cons a (cons b args))))

  (add-macro-alias q-xor q-binary-xor)
  (add-binop q-xor q-binary-xor)
  (local (in-theory (enable q-xor)))

  (defthm ubddp-of-q-xor
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (ubddp (q-xor x y))
                    t))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-q-xor
    (equal (eval-bdd (q-xor x y) values)
           (if (eval-bdd x values)
               (not (eval-bdd y values))
             (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (e/d (eval-bdd)
                            (canonicalize-q-not))
            :induct (q-binop-induct x y values)
            :expand (q-xor x y))))

  (defthm q-xor-of-self
    (equal (q-xor x x)
           nil)
    :hints(("Goal" :in-theory (e/d (q-not)
                                   (equal-by-eval-bdds
                                    canonicalize-q-not)))))

  (defthm canonicalize-q-xor
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-xor x y)
                    (q-ite x (q-not y) y))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-xor)))


(defsection qv
  :parents (ubdd-constructors)
  :short "@(call qv) constructs a UBDD which evaluates to true exactly when the
@('i')th BDD variable is true."

  (defund qv (i)
    (declare (xargs :guard t))
    (if (posp i)
        (let ((prev (qv (1- i))))
          (hons prev prev))
      (hons t nil)))

  (memoize 'qv)
  (add-bdd-fn qv)

  (local (in-theory (enable qv)))

  (defthm ubddp-qv
    (ubddp (qv i))
    :hints(("goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-of-qv-and-nil
    (not (eval-bdd (qv i) nil))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (defthm eval-bdd-of-qv
    (equal (eval-bdd (qv i) lst)
           (if (nth i lst) t nil))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (local (defun qvs-ind (i j)
           (if (or (zp i) (zp j))
               i
             (qvs-ind (1- i) (1- j)))))

  (defthm qvs-equal
    (equal (equal (qv i) (qv j))
           (equal (nfix i) (nfix j)))
    :hints(("Goal" :induct (qvs-ind i j)))))



(defsection eval-bdd-list
  :parents (ubdds)
  :short "Apply @(see eval-bdd) to a list of UBDDs."
  :long "<p>The resulting list is @(see hons)ed together.</p>

<p>BOZO why do we hons the list, I suspect it makes no sense to do so...</p>"

  (defund eval-bdd-list (x values)
    (declare (xargs :guard t))
    (if (consp x)
        (hons (eval-bdd (car x) values)
              (eval-bdd-list (cdr x) values))
      nil))

  (local (in-theory (enable eval-bdd-list)))

  (defthm eval-bdd-list-when-not-consp
    (implies (not (consp x))
             (equal (eval-bdd-list x values)
                    nil)))

  (defthm eval-bdd-list-of-cons
    (equal (eval-bdd-list (cons a x) values)
           (cons (eval-bdd a values)
                 (eval-bdd-list x values))))

  (defthmd consp-eval-bdd-list
    (equal (consp (eval-bdd-list x env))
           (consp x))))



(defsection q-compose
  :parents (ubdd-constructors)
  :short "@(call q-compose) composes the UBDD @('x') with the list of UBDDs
@('l')."
  :long "<p>BOZO document what this is doing. Is it like sexpr compose?</p>"

  (defund q-compose (x l)
    (declare (xargs :guard t))
    (cond ((atom x)
           x)
          ((atom l)
           (q-compose (cdr x) nil))
          ((hons-equal (car x) (cdr x))
           (q-compose (car x) (cdr l)))
          (t
           (q-ite (car l)
                  (q-compose (car x) (cdr l))
                  (q-compose (cdr x) (cdr l))))))

  (add-bdd-fn q-compose)
  (local (in-theory (enable q-compose)))

  (defthm ubddp-of-q-compose
    (implies (and (force (ubddp x))
                  (force (ubdd-listp l)))
             (equal (ubddp (q-compose x l))
                    t))
    :hints(("Goal" :in-theory (enable ubddp)))))


(defsection q-compose-list
  :parents (ubdd-constructors)
  :short "@(call q-compose-list) composes each UBDD in @('xs') with the list of
UBDDs @('l'), i.e., it maps @(see q-compose) across @('xs')."

  (defund q-compose-list (xs l)
    (declare (xargs :guard t))
    (if (atom xs)
        nil
      (cons (q-compose (car xs) l)
            (q-compose-list (cdr xs) l))))

  (local (in-theory (enable q-compose-list)))

  (defthm q-compose-list-when-not-consp
    (implies (not (consp xs))
             (equal (q-compose-list xs l)
                    nil)))

  (defthm q-compose-list-of-cons
    (equal (q-compose-list (cons x xs) l)
           (cons (q-compose x l)
                 (q-compose-list xs l))))

  (defthm ubdd-listp-of-q-compose-list
    (implies (and (force (ubdd-listp xs))
                  (force (ubdd-listp l)))
             (equal (ubdd-listp (q-compose-list xs l))
                    t))))


(defsection q-and-is-nil
  :parents (ubdd-constructors)
  :short "@(call q-and-is-nil) determines whether @('(q-and x y)') is
always false."

  :long "<p>You could ask the same question in other ways, say for instance</p>

@({
 (not (q-and x y))
})

<p>But @('q-and-is-nil') is especially efficient and doesn't need to construct
an intermediate UBDD.</p>"

  (defund q-and-is-nil (x y)
    (declare (xargs :guard t))
    (cond ((eq x t) (eq y nil))
          ((atom x) t)
          ((eq y t) nil)
          ((atom y) t)
          (t (and (q-and-is-nil (qcar x) (qcar y))
                  (q-and-is-nil (qcdr x) (qcdr y))))))

  (memoize 'q-and-is-nil :condition '(and (consp x) (consp y)))

  (local (in-theory (enable q-and-is-nil)))

  (defthm q-and-is-nil-removal
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-and-is-nil x y)
                    (not (q-and x y))))
    :hints(("Goal"
            :induct (q-and-is-nil x y)
            :in-theory (e/d (q-and ubddp)
                            (canonicalize-q-and
                             equal-by-eval-bdds))))))


(defsection q-and-is-nilc2
  :parents (ubdd-constructors)
  :short "@(call q-and-is-nilc2) determines whether @('(q-and x (q-not y))') is
always false."
  :long "<p>This is like @(see q-and-is-nil).</p>"

  (defund q-and-is-nilc2 (x y)
    (declare (xargs :guard t))
    (cond ((eq x t) (eq y t))
          ((atom x) t)
          ((eq y t) t)
          ((atom y) nil)
          (t (and (q-and-is-nilc2 (qcar x) (qcar y))
                  (q-and-is-nilc2 (qcdr x) (qcdr y))))))

  (local (in-theory (enable q-and-is-nilc2)))

  (defthm q-and-is-nilc2-removal
    (implies (and (force (ubddp x))
                  (force (ubddp y)))
             (equal (q-and-is-nilc2 x y)
                    (not (q-and x (q-not y)))))
    :hints(("Goal"
            :induct (q-and-is-nilc2 x y)
            :in-theory (e/d (q-and-c2 q-and-is-nilc2 ubddp)
                            (canonicalize-q-and-c2 equal-by-eval-bdds
; Matt K. mod, 6/2020: Disable the following rule, which causes the proof to
; fail now that ACL2 is loosening its "being-openedp" heuristic restriction.
                                                   canonicalize-q-not))))))


(defund q-is-atomic (x)
  (declare (xargs :guard t))
  (if (atom x)
      (if x t nil)
    'not-atomic))

(defund q-not-is-atomic (x)
  (declare (xargs :guard t))
  ;; returns T, NIL, or NOT-ATOMIC
  (if (atom x)
      (not x)
    'not-atomic))

(defthm q-not-is-atomic-removal
  (implies (ubddp x)
           (equal (q-not-is-atomic x)
                  (q-is-atomic (q-not x))))
  :hints(("Goal"
          :in-theory (enable q-not-is-atomic
                             q-is-atomic
                             q-ite q-not ubddp))))


(defabbrev atom-fix (y)
  (if (atom y) y 'not-atomic))

(defund q-ite-is-atomic (x y z)
  ;; returns T, NIL, or NOT-ATOMIC
  (declare (xargs :guard t))
  (cond ((null x) (atom-fix z))
        ((atom x) (atom-fix y))
        (t (let ((y (if (hons-equal x y) t y))
                 (z (if (hons-equal x z) nil z)))
             (cond ((hons-equal y z) (atom-fix y))
                   ((and (eq y t) (eq z nil)) (atom-fix x))
                   ((and (eq y nil) (eq z t)) (q-not-is-atomic x))
                   (t (let ((a (q-ite-is-atomic (car x) (qcar y) (qcar z)))
                            (d (q-ite-is-atomic (cdr x) (qcdr y) (qcdr z))))
                        (cond ((or (eq a 'not-atomic)
                                   (eq d 'not-atomic))
                               'not-atomic)
                              ((equal a d) a)
                              (t 'not-atomic)))))))))

(encapsulate
  ()
  (local (defthm lemma
           (implies (ubddp x)
                    (equal (consp x)
                           (if (equal x t)
                               nil
                             (if (equal x nil)
                                 nil
                               t))))
           :hints(("Goal" :in-theory (enable ubddp)))))

  (local
   (defthm consp-q-ite
     (implies (and (ubddp x) (ubddp y) (ubddp z))
              (equal (consp (q-ite x y z))
                     (and (not (equal (q-ite x y z) t))
                          (not (equal (q-ite x y z) nil)))))))

  (local (defthm ubddp-consp-rws
           (implies (and (ubddp x) (consp x))
                    (and (ubddp (car x))
                         (ubddp (cdr x))))
           :hints(("Goal" :in-theory (enable ubddp)))))

  (with-output
   :off (prove warning) :gag-mode nil
   (defthm q-ite-is-atomic-removal
     (implies (and (ubddp x)
                   (ubddp y)
                   (ubddp z))
              (equal (q-ite-is-atomic x y z)
                     (q-is-atomic (q-ite x y z))))
     :hints(("Goal"
             :induct (q-ite-is-atomic x y z)
             :in-theory (e/d (q-is-atomic
                              ; ubddp
                              (:induction q-ite-is-atomic))
                             (canonicalize-q-not
                              ;;                               q-ite ubddp
                              equal-by-eval-bdds
                              equal-of-booleans-rewrite
                              |(q-ite non-nil y z)|
                              default-car
                              default-cdr
                              (:type-prescription booleanp)
                              (:type-prescription ubddp)
                              (:type-prescription q-ite-is-atomic)
                              (:type-prescription q-ite-fn)
                              (:type-prescription q-is-atomic)
                              q-not not lemma))
             :expand ((:free (y z) (q-ite x y z))
                      (:free (y z) (q-ite t y z))
                      (:free (y z) (q-ite nil y z))
                      (:free (y z) (q-ite-is-atomic x y z))
                      (:free (y z) (q-ite-is-atomic t y z))
                      (:free (y z) (q-ite-is-atomic nil y z)))
             :do-not-induct t
             :do-not '(generalize fertilize eliminate-destructors))
            ))))


(defun q-buf (x)
  ;; !!! BOZO this is stupid.  We should get rid of it.
  (declare (xargs :guard t))
  x)


;; JARED HACK.  I think we should turn off canonicalize-q-fns by
;; default given the new guard stuff.

(in-theory (disable* (:ruleset canonicalize-to-q-ite)))



;; !!! COMPATIBILITY WRAPPER.  I'd like to get rid of this stuff.

; We define additional BDD-operations that can sometime provide better
; efficiency than only using Q-ITE through the use of specific function
; memoization and other tricks.


;; COMPATIBILITY WRAPPER --- Trying to get rid of ITE functions entirely.

(defmacro q-and-ite (x y)
  `(q-and ,x ,y))

(defmacro q-or-ite (x y)
  `(q-or ,x ,y))

(defmacro q-not-ite (x)
  `(q-not ,x))

(defmacro q-implies-ite (x y)
  `(q-implies ,x ,y))

(defmacro q-or-c2-ite (x y)
  `(q-or-c2 ,x ,y))

(defmacro q-and-c1-ite (x y)
  `(q-and-c1 ,x ,y))

(defmacro q-and-c2-ite (x y)
  `(q-and-c2 ,x ,y))

(defmacro q-iff-ite (x y)
  `(q-iff ,x ,y))

(defmacro q-xor-ite (x y)
  `(q-xor ,x ,y))




; Finds a satisfying assignment for a BDD.

(defsection q-sat
  :parents (ubdds)
  :short "@(call q-sat) finds a satisfying assignment for the UBDD @('x'), if
one exists."

  :long "<p>Assuming @('x') is a well-formed UBDD, the only time there isn't
a satisfying assignment is when @('x') represents the constant false function,
i.e., when @('x') is @('nil').  In any other case it's easy to construct some
list of values for which @(see eval-bdd) returns true.</p>

<p>BOZO naming.  This shouldn't start with @('q-') since it's constructing a
list of values instead of a UBDD.</p>"

  (defund q-sat (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (eq (cdr x) nil)
          (cons t (q-sat (car x)))
        (cons nil (q-sat (cdr x))))))

  (local (in-theory (enable q-sat)))

  (defthm q-sat-correct
    (implies (and (ubddp x) x)
             (eval-bdd x (q-sat x)))
    :hints(("Goal" :in-theory (enable ubddp
                                      eval-bdd)))))


(defsection bdd-sat-dfs
  :parents (ubdds)
  :short "@(call bdd-sat-dfs) finds a satisfying assignment for the UBDD @('x'), if
one exists.  It works even if @('x') is not a well-formed UBDD, but it might be
slow in that case."

  (defund bdd-sat-dfs (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let* ((a (car x))
             (d (cdr x)))
        (cond ((and (atom a) a) '(t))
              ((and (atom d) d) '(nil))
              (t (let ((rec1 (bdd-sat-dfs a)))
                   (if rec1 (cons t rec1)
                     (let ((rec2 (bdd-sat-dfs d)))
                       (and rec2 (cons nil rec2))))))))))

  (local (in-theory (enable bdd-sat-dfs)))

  (defthmd bdd-sat-dfs-produces-satisfying-assign
    (implies (bdd-sat-dfs x)
             (eval-bdd x (bdd-sat-dfs x)))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (local (in-theory (enable bdd-sat-dfs-produces-satisfying-assign)))

  (defthmd bdd-sat-dfs-not-satisfying-when-nil
    (implies (and (consp x)
                  (not (bdd-sat-dfs x)))
             (not (eval-bdd x vars)))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (local (in-theory (enable bdd-sat-dfs-not-satisfying-when-nil)))

  (defthm bdd-sat-dfs-correct
    (implies (eval-bdd x vars)
             (eval-bdd x (bdd-sat-dfs x)))
    :hints(("Goal" :in-theory (enable eval-bdd)))))



(defsection q-sat-any
  :parents (ubdds)
  :short "@(call q-sat-any) finds an assignment that satisfies at least one
UBDD in the list of UBDDs @('x')."

  :long "<p>BOZO naming.  This shouldn't start with @('q-') since it's
constructing a list of values instead of a UBDD.</p>"

  (defund q-sat-any (a)
    (declare (xargs :guard t))
    (if (atom a)
        nil
      (if (eq (car a) nil)
          (q-sat-any (cdr a))
        (q-sat (car a))))))



(defsection ubdd-fix
  :parents (ubdds)
  :short "@(call ubdd-fix) constructs a valid @(see ubddp) that is treated
identically to @('x') under @(see eval-bdd)."

  :long "<p>This fixes up the tips of @('x') to be Booleans and handles any
collapsing of @('(t . t)') and @('(nil . nil)') nodes.  It is occasionally
useful in theorems to avoid @(see ubddp) hypotheses.</p>"

  (defund ubdd-fix (x)
    (declare (xargs :guard t))
    (if (atom x)
        (if x t nil)
      (if (and (atom (car x)) (atom (cdr x))
               (iff (car x) (cdr x)))
          (if (car x) t nil)
        (qcons (ubdd-fix (car x))
               (ubdd-fix (cdr x))))))

  (local (in-theory (enable ubdd-fix)))

  (memoize 'ubdd-fix :condition '(consp x))

  (defthm ubddp-ubdd-fix
    (ubddp (ubdd-fix x))
    :hints(("Goal" :in-theory (enable ubddp))))

  (defthm eval-bdd-ubdd-fix
    (equal (eval-bdd (ubdd-fix x) env)
           (eval-bdd x env))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (defthm ubdd-fix-x-is-x
    (implies (ubddp x)
             (equal (ubdd-fix x) x))
    :hints(("Goal" :in-theory (enable ubddp)))))

