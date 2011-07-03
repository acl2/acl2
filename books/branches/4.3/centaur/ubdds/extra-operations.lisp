; UBDD Library
; Copyright (C) 2008-2011 Warren Hunt and Bob Boyer
; Significantly revised in 2008 by Jared Davis and Sol Swords.
; Now maintained by Centaur Technology.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

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

  ;; This is sort of styled after other associative/commutative functions like
  ;; append and plus, where we begin by introducing an actual function to do the
  ;; "binary" version of the function.

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

  ;; Next, we are going to introduce the Q-AND macro which takes an arbitrary
  ;; number of arguments and ANDs them together.  In the logic, we have:
  ;;
  ;;   (Q-AND) = t
  ;;   (Q-AND X) = X
  ;;   (Q-AND X Y) = (Q-BINARY-AND X Y)
  ;;   (Q-AND X Y Z) = (Q-BINARY-AND X (Q-BINARY-AND Y Z))
  ;;    Etc.
  ;;
  ;; But as a special optimization in the :exec world when there is more than
  ;; one argument, we can sometimes "short-circuit" the computation and avoid
  ;; evaluating some arguments.
  ;;
  ;; We classify the arguments as cheap or expensive using classify-for-q-macros,
  ;; and then walk through the cheap arguments first to see if any of them is nil
  ;; so that we can stop early.  Then we continue through the expensive
  ;; arguments, again stopping early if any of them is nil.

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

  (defthm normp-of-q-and
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-and x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

  (defthm eval-bdd-of-q-and
    (equal (eval-bdd (q-and x y) values)
           (and (eval-bdd x values)
                (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (enable eval-bdd)
            :induct (q-binop-induct x y values)
            :expand (q-and x y))))

  (defthm canonicalize-q-and
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (q-and x y)
                    (q-ite x y nil))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-and))

  ;; One strategy is to canonicalize away q-and into q-ite whenever it is seen,
  ;; using canonicalize-q-and, above.  But if this strategy is not being
  ;; followed, weak-boolean-listp may find the following theorems useful.  It is important that
  ;; these theorems come after canonicalize-q-and, since in particular
  ;; q-and-of-nil is to verify the guards when the q-and macro is being used.

  (defthm q-and-of-nil
    (and (equal (q-and nil x) nil)
         (equal (q-and x nil) nil))
    :hints(("Goal" :in-theory (disable canonicalize-q-and))))

  (defthm q-and-of-t-slow
    (and (equal (q-and t x) (if (consp x) x (if x t nil)))
         (equal (q-and x t) (if (consp x) x (if x t nil))))
    :hints(("Goal" :in-theory (disable canonicalize-q-and))))

  (defthm q-and-of-t-aggressive
    (implies (force (normp x))
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
    (implies (force (normp x))
             (equal (q-and x x) x)))

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

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

  ;; In the logic:
  ;;
  ;; (Q-OR) = NIL
  ;; (Q-OR X) = X
  ;; (Q-OR X Y) = (Q-BINARY-OR X Y)
  ;; (Q-OR X Y Z) = (Q-BINARY-OR X (Q-BINARY-OR Y Z))
  ;;
  ;; In the exec world, we stop early if any argument evaluates to T and just
  ;; return T without evaluating the later arguments.

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
              ;; about performance on non-normp bdds?
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

  (defthm normp-of-q-or
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-or x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

  (defthm eval-bdd-of-q-or
    (equal (eval-bdd (q-or x y) values)
           (or (eval-bdd x values)
               (eval-bdd y values)))
    :hints(("Goal"
            :in-theory (enable eval-bdd)
            :induct (q-binop-induct x y values)
            :expand (q-or x y))))

  (defthm canonicalize-q-or
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (q-or x y)
                    (q-ite x t y))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-or))

  (defthm q-or-of-nil-slow
    (and (equal (q-or nil x) (if (consp x) x (if x t nil)))
         (equal (q-or x nil) (if (consp x) x (if x t nil)))))

  (defthm q-or-of-nil-aggressive
    (implies (force (normp x))
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
    (implies (force (normp x))
             (equal (q-or x x) x)))

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-or)))

  (local (defun test-q-or (a b c x y z)
           (declare (xargs :guard t))
           (list (q-or x y)
                 (q-or x (q-not y))
                 (q-or (q-not x) y)
                 (q-or x y (q-not x) a b (q-ite y z c))))))

(defsection q-implies

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

  (defthm normp-of-q-implies
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-implies x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
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
    (implies (force (normp x))
             (equal (q-implies t x) x))
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (defthm q-implies-of-t-right
    (equal (q-implies x t) t)
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))

  (defthm q-implies-of-self
    (equal (q-implies x x) t)
    :hints(("Goal" :in-theory (disable canonicalize-q-implies))))


  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-implies)))

  (local (defun test-q-implies (a b)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-implies a b)
                 (q-implies a (q-not b))
                 (q-implies (q-not b) a)
                 (q-implies (q-not a) (q-not b))))))


(defsection q-or-c2

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

  (defthm normp-of-q-or-c2
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-or-c2 x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
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

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-or-c2)))

  (local (defun test-q-or-c2 (a b)
           (declare (xargs :guard t))
           (list (q-or-c2 a b)
                 (q-or-c2 a (q-not b))
                 (q-or-c2 (q-not a) b)
                 (q-or-c2 (q-not a) (q-not b))))))


(defsection q-and-c1

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

  (defthm normp-of-q-and-c1
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-and-c1 x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
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

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-and-c1)))

  (local (defun test-q-and-c1 (a b)
           (declare (xargs :guard t))
           (list (q-and-c1 a b)
                 (q-and-c1 a (q-not b))
                 (q-and-c1 (q-not a) b)
                 (q-and-c1 (q-not a) (q-not b))))))


(defsection q-and-c2

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

  (defthm normp-of-q-and-c2
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-and-c2 x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (q-and-c2 x y)
                    (q-ite y nil x))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-and-c2))

  (defthm q-and-c2-of-nil-left
    (equal (q-and-c2 nil x) nil)
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm q-and-c2-of-nil-right-slow
    (equal (q-and-c2 x nil) (if (consp x) x (if x t nil))))

  (defthm q-and-c2-of-nil-right-aggressive
    (implies (force (normp x))
             (equal (q-and-c2 x nil) x)))

  (defthm q-and-c2-of-t
    (and (equal (q-and-c2 t x) (q-not x))
         (equal (q-and-c2 x t) nil))
    :hints(("Goal" :in-theory (disable (force)))))

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-and-c2)))

  (local (defun test-q-and-c2 (a b)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-and-c2 a b)
                 (q-and-c2 a (q-not b))
                 (q-and-c2 (q-not a) b)
                 (q-and-c2 (q-not a) (q-not b))))))


(defsection q-iff

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

  ;; We do not see how to use short-circuiting to improve upon (Q-BINARY-IFF X
  ;; Y), since the answer depends upon both inputs in all cases.
  ;;
  ;; However, when implementing the multiple-input Q-IFF macro, we can at least
  ;; take advantage of the short-circuiting provided by Q-AND for multiple-input
  ;; Q-IFF, e.g.,:
  ;;
  ;;    (Q-IFF X1 X2 X3 X4) == (Q-AND (Q-BINARY-IFF X1 X2)
  ;;                                  (Q-BINARY-IFF X1 X3)
  ;;                                  (Q-BINARY-IFF X1 X4))
  ;;
  ;; And we also reorder the inputs so that cheap ones come first, hoping that we
  ;; can avoid evaluating expensive Xi.

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

  (defthm normp-of-q-iff
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-iff x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (q-iff x y)
                    (q-ite x y (q-ite y nil t)))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-iff))

  ;; !!! What is the point of doing a LOCAL at the end of an
  ;; ENCAPSULATE?

  (local (in-theory (disable q-iff)))

  (local (defun test-q-iff (a b c d)
           (declare (xargs :guard t
                           :guard-hints (("Goal" :in-theory (disable (force))))))
           (list (q-iff a b)
                 (q-iff a b c (q-not b))
                 (q-iff (q-not a) (q-not b) c d)))))


(defmacro q-nand (&rest args)
  ;; (q-nand) = nil
  ;; (q-nand a) = (q-not a)
  ;; (q-nand a b ...) = (q-not (q-and a b ...))
  `(q-not (q-and . ,args)))

(defmacro q-nor (&rest args)
  ;; (q-nor) = t
  ;; (q-nor a) = (q-not a)
  ;; (q-nor a b ...) = (q-not (q-or a b ...))
  `(q-not (q-or . ,args)))


(defsection q-xor

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

  (defthm normp-of-q-xor
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (normp (q-xor x y))
                    t))
    :hints(("Goal" :in-theory (enable normp))))

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
    (implies (and (force (normp x))
                  (force (normp y)))
             (equal (q-xor x y)
                    (q-ite x (q-not y) y))))

  (add-to-ruleset canonicalize-to-q-ite '(canonicalize-q-xor)))


(defsection qv
  (defund qv (i)
    ;; Creates the (nfix i)th BDD variable.
    (declare (xargs :guard t))
    (if (posp i)
        (let ((prev (qv (1- i))))
          (hons prev prev))
      (hons t nil)))

  (memoize 'qv)

  (add-bdd-fn qv)

  (defthm normp-qv
    (normp (qv i))
    :hints(("goal" :in-theory (enable normp qv))))

  (defthm eval-bdd-of-qv-and-nil
    (not (eval-bdd (qv i) nil))
    :hints(("Goal" :in-theory (enable eval-bdd qv))))

  (defthm eval-bdd-of-qv
    (equal (eval-bdd (qv i) lst)
           (if (nth i lst) t nil))
    :hints(("Goal" :in-theory (enable eval-bdd qv))))

  (local (defun qvs-ind (i j)
           (if (or (zp i) (zp j))
               i
             (qvs-ind (1- i) (1- j)))))

  (defthm qvs-equal
    (equal (equal (qv i) (qv j))
           (equal (nfix i) (nfix j)))
    :hints(("Goal" :in-theory (enable qv)
            :induct (qvs-ind i j)))))


;; !!! BOZO organization is kind of haphazard after here.

(defsection norm-listp

  ;; [Jared]: I changed the name from normp-list
  (defund norm-listp (x)
    ":Doc-Section ubdds
     Recognizer for a list of ~il[normp]s.~/~/
     We do not require ~il[true-listp]."
    (declare (xargs :guard t))
    (if (consp x)
        (and (normp (car x))
             (norm-listp (cdr x)))
      t))

  (defthm norm-listp-when-not-consp
    (implies (not (consp x))
             (equal (norm-listp x)
                    t))
    :hints(("Goal" :in-theory (enable norm-listp))))

  (defthm norm-listp-of-cons
    (equal (norm-listp (cons a x))
           (and (normp a)
                (norm-listp x)))
    :hints(("Goal" :in-theory (enable norm-listp)))))



(defsection eval-bdd-list

  (defund eval-bdd-list (x values)
    ":Doc-Section ubdds
     Apply ~il[eval-bdd] to a list of bdds.~/~/
     The resulting list is ~il[hons]ed together."
    (declare (xargs :guard t))
    (if (consp x)
        (hons (eval-bdd (car x) values)
              (eval-bdd-list (cdr x) values))
      nil))

  (defthm eval-bdd-list-when-not-consp
    (implies (not (consp x))
             (equal (eval-bdd-list x values)
                    nil))
    :hints(("Goal" :in-theory (enable eval-bdd-list))))

  (defthm eval-bdd-list-of-cons
    (equal (eval-bdd-list (cons a x) values)
           (cons (eval-bdd a values)
                 (eval-bdd-list x values)))
    :hints(("Goal" :in-theory (enable eval-bdd-list))))

  (defthmd consp-eval-bdd-list
    (equal (consp (eval-bdd-list x env))
           (consp x))
    :hints(("Goal" :in-theory (enable eval-bdd-list)))))


(defund q-compose (x l)
  ;; Composes the Boolean function represented by BDD X with those
  ;; represented by BDDs in the list L.
  (declare (xargs :guard t))
  (if (atom x)
      x
    (if (atom l)
        (q-compose (cdr x) nil)
      (if (hons-equal (car x) (cdr x))
          (q-compose (car x) (cdr l))
        (q-ite (car l)
               (q-compose (car x) (cdr l))
               (q-compose (cdr x) (cdr l)))))))

(add-bdd-fn q-compose)

(defthm normp-of-q-compose
  (implies (and (force (normp x))
                (force (norm-listp l)))
           (equal (normp (q-compose x l))
                  t))
  :hints(("Goal" :in-theory (enable q-compose normp))))


(defund q-compose-list (xs l)
  (declare (xargs :guard t))
  (if (atom xs)
      nil
    (cons (q-compose (car xs) l)
          (q-compose-list (cdr xs) l))))

(defthm q-compose-list-when-not-consp
  (implies (not (consp xs))
           (equal (q-compose-list xs l)
                  nil))
  :hints(("Goal" :in-theory (enable q-compose-list))))

(defthm q-compose-list-of-cons
  (equal (q-compose-list (cons x xs) l)
         (cons (q-compose x l)
               (q-compose-list xs l)))
  :hints(("Goal" :in-theory (enable q-compose-list))))

(defthm norm-listp-of-q-compose-list
  (implies (and (force (norm-listp xs))
                (force (norm-listp l)))
           (equal (norm-listp (q-compose-list xs l))
                  t))
  :hints(("Goal" :induct (len xs))))


(defund q-and-is-nil (x y)
  (declare (xargs :guard t))
  (cond ((eq x t) (eq y nil))
        ((atom x) t)
        ((eq y t) nil)
        ((atom y) t)
        (t (and (q-and-is-nil (qcar x) (qcar y))
                (q-and-is-nil (qcdr x) (qcdr y))))))

(memoize 'q-and-is-nil   :condition '(and (consp x) (consp y)))

(defthm q-and-is-nil-removal
  (implies (and (force (normp x))
                (force (normp y)))
           (equal (q-and-is-nil x y)
                  (not (q-and x y))))
  :hints(("Goal"
          :induct (q-and-is-nil x y)
          :in-theory (e/d (q-and q-and-is-nil normp)
                          (canonicalize-q-and
                           equal-by-eval-bdds)))))


(defund q-and-is-nilc2 (x y)
  (declare (xargs :guard t))
  (cond ((eq x t) (eq y t))
        ((atom x) t)
        ((eq y t) t)
        ((atom y) nil)
        (t (and (q-and-is-nilc2 (qcar x) (qcar y))
                (q-and-is-nilc2 (qcdr x) (qcdr y))))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (normp y) (not (equal y t)))
                   (q-ite y nil t))
          :hints(("Goal" :in-theory (enable q-ite q-not normp)))))

 (defthm q-and-is-nilc2-removal
   (implies (and (force (normp x))
                 (force (normp y)))
            (equal (q-and-is-nilc2 x y)
                   (not (q-and-c2 x y))))
   :hints(("Goal"
           :induct (q-and-is-nilc2 x y)
           :in-theory (e/d (q-and-c2 q-and-is-nilc2 normp)
                           (canonicalize-q-and-c2 equal-by-eval-bdds))))))


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
  (implies (normp x)
           (equal (q-not-is-atomic x)
                  (q-is-atomic (q-not x))))
  :hints(("Goal"
          :in-theory (enable q-not-is-atomic
                             q-is-atomic
                             q-ite q-not normp))))


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
           (implies (normp x)
                    (equal (consp x)
                           (if (equal x t)
                               nil
                             (if (equal x nil)
                                 nil
                               t))))
           :hints(("Goal" :in-theory (enable normp)))))

  (local
   (defthm consp-q-ite
     (implies (and (normp x) (normp y) (normp z))
              (equal (consp (q-ite x y z))
                     (and (not (equal (q-ite x y z) t))
                          (not (equal (q-ite x y z) nil)))))))

  (local (defthm normp-consp-rws
           (implies (and (normp x) (consp x))
                    (and (normp (car x))
                         (normp (cdr x))))
           :hints(("Goal" :in-theory (enable normp)))))

  (with-output
   :off (prove warning) :gag-mode nil
   (defthm q-ite-is-atomic-removal
     (implies (and (normp x)
                   (normp y)
                   (normp z))
              (equal (q-ite-is-atomic x y z)
                     (q-is-atomic (q-ite x y z))))
     :hints(("Goal"
             :induct (q-ite-is-atomic x y z)
             :in-theory (e/d (q-is-atomic
                              ; normp
                              (:induction q-ite-is-atomic))
                             (canonicalize-q-not
                              ;;                               q-ite normp
                              equal-by-eval-bdds
                              equal-of-booleans-rewrite
                              |(q-ite non-nil y z)|
                              default-car
                              default-cdr
                              (:type-prescription booleanp)
                              (:type-prescription normp)
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

(defn q-sat (x)
  (if (atom x)
      nil
    (if (eq (cdr x) nil)
        (cons t (q-sat (car x)))
      (cons nil (q-sat (cdr x))))))

(in-theory (disable q-sat))

(defthm q-sat-correct
  (implies (and (normp x) x)
           (eval-bdd x (q-sat x)))
  :hints (("goal" :in-theory (enable eval-bdd q-sat normp))))


; Given a list of BDDs, finds an assignment that satisfies at least one of
; them.

(defn q-sat-any (a)
  (if (atom a)
      nil
    (if (eq (car a) nil)
        (q-sat-any (cdr a))
      (q-sat (car a)))))



(defsection norm-fix

  (defun norm-fix (x)
    (declare (xargs :guard t))
    (if (atom x)
        (if x t nil)
      (if (and (atom (car x)) (atom (cdr x))
               (iff (car x) (cdr x)))
          (if (car x) t nil)
        (acl2::qcons (norm-fix (car x))
                     (norm-fix (cdr x))))))

  (defthm normp-norm-fix
    (normp (norm-fix x))
    :hints(("Goal" :in-theory (enable normp))))

  (defthm eval-bdd-norm-fix
    (equal (eval-bdd (norm-fix x) env)
           (eval-bdd x env))
    :hints(("Goal" :in-theory (enable eval-bdd))))

  (defthm norm-fix-x-is-x
    (implies (normp x)
             (equal (norm-fix x) x))
    :hints(("Goal" :in-theory (enable normp))))

  (in-theory (disable norm-fix)))

