; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "definitions")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


; The syntax evaluator is the same as the generic evaluator, except we don't
; prove anything about it and it optimizes for logic.term-< and
; logic.constantp.  Having logic.term-< built-in is particularly important
; since we use that a lot in syntactically restricted rewrite rules, and it is
; a very slow function that has to call the various counting routines, which we
; want to have memoized, etc.

(defund rewrite.syntaxp-arity-table ()
  (declare (xargs :guard t))
  '((logic.term-< . 2)
    (logic.constantp . 1)
    (if . 3)
    (equal . 2)
    (consp . 1)
    (cons . 2)
    (car . 1)
    (cdr . 1)
    (symbolp . 1)
    (symbol-< . 2)
    (natp . 1)
    (< . 2)
    (+ . 2)
    (- . 2)))

(defthm logic.arity-tablep-of-rewrite.syntaxp-arity-table
  (equal (logic.arity-tablep (rewrite.syntaxp-arity-table))
         t))

(in-theory (disable (:executable-counterpart rewrite.syntaxp-arity-table)))



(defund rewrite.syntaxp-base-evaluablep (x)
  ;; We decide if a term is of the form (f c1 ... cn), where f is one of the
  ;; base functions, c1...cn are constants, and the arity of f is n.
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (let ((fn   (logic.function-name x))
             (args (logic.function-args x)))
         (let ((entry (lookup fn (rewrite.syntaxp-arity-table))))
           (and entry
                (logic.constant-listp args)
                (tuplep (cdr entry) args))))))

(defthm booleanp-of-rewrite.syntaxp-base-evaluablep
  (equal (booleanp (rewrite.syntaxp-base-evaluablep x))
         t)
  :hints(("Goal" :in-theory (e/d (rewrite.syntaxp-base-evaluablep)
                                 (forcing-lookup-of-logic.function-name
                                  forcing-true-listp-of-logic.function-args)))))

(defthm forcing-logic.functionp-when-rewrite.syntaxp-base-evaluablep
  (implies (and (rewrite.syntaxp-base-evaluablep x)
                (force (logic.termp x)))
           (equal (logic.functionp x)
                  t))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluablep))))

(defthm logic.constant-listp-of-logic.function-args-when-rewrite.syntaxp-base-evaluablep
  (implies (and (rewrite.syntaxp-base-evaluablep x)
                (force (logic.termp x)))
           (equal (logic.constant-listp (logic.function-args x))
                  t))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluablep logic.function-args))))

(defthm lookup-logic.function-name-in-rewrite.syntaxp-arity-table-when-rewrite.syntaxp-base-evaluablep
  (implies (and (rewrite.syntaxp-base-evaluablep x)
                (force (logic.termp x)))
           (equal (lookup (logic.function-name x) (rewrite.syntaxp-arity-table))
                  (cons (logic.function-name x)
                        (len (logic.function-args x)))))
  :hints(("Goal" :in-theory (e/d (rewrite.syntaxp-base-evaluablep)
                                 (forcing-lookup-of-logic.function-name)))))

(defthmd lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
  (implies (and (logic.function-namep fn)
                (memberp fn (domain (rewrite.syntaxp-arity-table)))
                (true-listp args)
                (logic.constant-listp args)
                (equal (len args) (cdr (lookup fn (rewrite.syntaxp-arity-table)))))
           (equal (logic.term-atblp (logic.function fn args) (rewrite.syntaxp-arity-table))
                  t)))

(defthm logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
  (implies (and (rewrite.syntaxp-base-evaluablep term)
                (force (logic.termp term)))
           (equal (logic.term-atblp term (rewrite.syntaxp-arity-table))
                  t))
  :hints(("Goal"
          :in-theory (enable rewrite.syntaxp-base-evaluablep
                             lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep)
          :use ((:instance lemma-for-logic.term-atblp-when-rewrite.syntaxp-base-evaluablep
                            (fn (logic.function-name term))
                            (args (logic.function-args term)))))))

(defthm rewrite.syntaxp-base-evaluablep-when-preliminary-fn-applied-to-constants
  (implies (and (logic.function-namep fn)
                (memberp fn (domain (rewrite.syntaxp-arity-table)))
                (true-listp args)
                (logic.constant-listp args)
                (equal (len args) (cdr (lookup fn (rewrite.syntaxp-arity-table)))))
           (equal (rewrite.syntaxp-base-evaluablep (logic.function fn args))
                  t))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluablep))))

(defthm rewrite.syntaxp-base-evaluablep-of-logic.function-equal
  (equal (rewrite.syntaxp-base-evaluablep (logic.function 'equal args))
         (and (tuplep 2 args)
              (logic.constant-listp args)))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluablep rewrite.syntaxp-arity-table))))



(defund rewrite.syntaxp-base-evaluator (x)
  ;; We run a base function on its arguments and return the result as a quoted
  ;; constant (i.e., a logic.constantp).
  (declare (xargs :guard (and (logic.termp x)
                              (rewrite.syntaxp-base-evaluablep x))
                  :guard-hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluablep
                                                          rewrite.syntaxp-arity-table)))))
  (let ((fn   (logic.function-name x))
        (vals (logic.unquote-list (logic.function-args x))))
    (list 'quote
          ;; yucky ec calls shouldn't be exported
          (cond ((equal fn 'logic.term-<)    (ACL2::ec-call (logic.term-< (first vals) (second vals))))
                ((equal fn 'logic.constantp) (ACL2::ec-call
                                              (logic.constantp (first vals))))
                ((equal fn 'if)              (if (first vals) (second vals) (third vals)))
                ((equal fn 'equal)           (equal (first vals) (second vals)))
                ((equal fn 'consp)           (consp (first vals)))
                ((equal fn 'cons)            (cons (first vals) (second vals)))
                ((equal fn 'car)             (car (first vals)))
                ((equal fn 'cdr)             (cdr (first vals)))
                ((equal fn 'symbolp)         (symbolp (first vals)))
                ((equal fn 'symbol-<)        (symbol-< (first vals) (second vals)))
                ((equal fn 'natp)            (natp (first vals)))
                ((equal fn '<)               (< (first vals) (second vals)))
                ((equal fn '+)               (+ (first vals) (second vals)))
                ((equal fn '-)               (- (first vals) (second vals)))
                ;((equal fn '*)           (* (first vals) (second vals)))
                ;((equal fn 'expt)        (expt (first vals) (second vals)))
                ;((equal fn 'floor)       (floor (first vals) (second vals)))
                ;((equal fn 'mod)         (mod (first vals) (second vals)))
                ;((equal fn 'bitwise-shl) (bitwise-shl (first vals) (second vals)))
                ;((equal fn 'bitwise-shr) (bitwise-shr (first vals) (second vals)))
                ;((equal fn 'bitwise-and) (bitwise-and (first vals) (second vals)))
                ;((equal fn 'bitwise-or)  (bitwise-or (first vals) (second vals)))
                ;((equal fn 'bitwise-xor) (bitwise-xor (first vals) (second vals)))
                ;((equal fn 'bitwise-nth) (bitwise-xor (first vals) (second vals)))
                (t nil)))))

(defthm forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator
  (equal (logic.constantp (rewrite.syntaxp-base-evaluator term))
         t)
  :hints(("Goal" :in-theory (enable logic.initial-arity-table rewrite.syntaxp-base-evaluator))))

(defthm forcing-logic.constantp-of-rewrite.syntaxp-base-evaluator-free
  ;; BOZO move to base evaluator
  (implies (equal free (rewrite.syntaxp-base-evaluator term))
           (equal (logic.constantp free)
                  t)))

(defthm rewrite.syntaxp-base-evaluator-of-logic.function-equal
  (equal (rewrite.syntaxp-base-evaluator (logic.function 'equal args))
         (list 'quote (equal (logic.unquote (first args))
                             (logic.unquote (second args)))))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-base-evaluator))))



(defund rewrite.flag-syntaxp-evaluator (flag x defs n)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (and (logic.termp x)
                                       (logic.groundp x))
                                (and (logic.term-listp x)
                                     (logic.ground-listp x)))
                              (definition-listp defs)
                              (natp n))
                  :measure (two-nats-measure n (rank x))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond
       ((zp n)
        (ACL2::prog2$ (ACL2::cw "Warning: insufficient n given to syntaxp-evaluator~%")
                      nil))
       ((logic.constantp x)
        ;; SUCCESS: Constants evaluate to themselves.
        x)
       ((logic.variablep x)
        ;; FAILURE: Not a ground term.
        nil)
       ((logic.functionp x)
        (let ((name (logic.function-name x))
              (args (logic.function-args x)))
          (if (and (equal name 'if)
                   (equal (len args) 3))
              ;; "if" must be handled specially with lazy evaluation.
              (let ((eval-test (rewrite.flag-syntaxp-evaluator 'term (first args) defs n)))
                (and eval-test
                     (if (logic.unquote eval-test)
                         (rewrite.flag-syntaxp-evaluator 'term (second args) defs n)
                       (rewrite.flag-syntaxp-evaluator 'term (third args) defs n))))
            ;; other functions are eagerly evaluated.
            (let ((eval-args (rewrite.flag-syntaxp-evaluator 'list args defs n)))
              (and eval-args
                   ;; eval-args is (t . ((quote val1) ... (quote valn)))
                   (let* ((values     (cdr eval-args))
                          (atbl-entry (lookup name (rewrite.syntaxp-arity-table))))
                     (if atbl-entry
                         ;; found a base function
                         (and (equal (cdr atbl-entry) (len values))
                              (rewrite.syntaxp-base-evaluator (logic.function name values)))

                       ;; found a non-base function
                       (let* ((def (definition-list-lookup name defs)))
                         (and def
                              (let ((formals (logic.function-args (logic.=lhs def)))
                                    (body    (logic.=rhs def)))
                                (and (equal (len formals) (len values))
                                     (rewrite.flag-syntaxp-evaluator 'term
                                                             (logic.substitute body (pair-lists formals values))
                                                             defs (- n 1)))))))))))))
       ((logic.lambdap x)
        ;; Eagerly evaluate the arguments to a lambda, then substitute them into
        ;; the lambda's body.
        (let ((formals (logic.lambda-formals x))
              (body    (logic.lambda-body x))
              (actuals (logic.lambda-actuals x)))
          (let ((eval-actuals (rewrite.flag-syntaxp-evaluator 'list actuals defs n)))
            (and eval-actuals
                 ;; eval-actuals is (t . ((quote val1) ... (quote valn)))
                 (let ((values (cdr eval-actuals)))
                   (rewrite.flag-syntaxp-evaluator 'term
                                           (logic.substitute body (pair-lists formals values))
                                           defs
                                           (- n 1)))))))
       (t
        ;; FAILURE: cannot evaluate malformed terms
        nil))
    (if (consp x)
        ;; Try to evaluate the first argument and then, recursively, the rest of
        ;; the arguments.
        (let ((first (rewrite.flag-syntaxp-evaluator 'term (car x) defs n))
              (rest  (rewrite.flag-syntaxp-evaluator 'list (cdr x) defs n)))
          (if (and first rest)
              ;; SUCCESS: evaluated the first and all other arguments.
              (cons t (cons first (cdr rest)))
            ;; FAILURE: couldn't evaluate some argument.
            nil))
      ;; SUCCESS: the empty list can always be evaluted.
      (cons t nil))))

(defund rewrite.syntaxp-evaluator (x defs n)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs)
                              (natp n))
                  :verify-guards nil))
  (rewrite.flag-syntaxp-evaluator 'term x defs n))

(defund rewrite.syntaxp-evaluator-list (x defs n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.ground-listp x)
                              (definition-listp defs)
                              (natp n))
                  :verify-guards nil))
  (rewrite.flag-syntaxp-evaluator 'list x defs n))

(defthmd definition-of-rewrite.syntaxp-evaluator
  (equal (rewrite.syntaxp-evaluator x defs n)
         (cond
          ((zp n)
           ;; FAILURE: Insufficient "n" to evaluate this term.
           nil)
          ((logic.constantp x)
           ;; SUCCESS: Constants evaluate to themselves.
           x)
          ((logic.variablep x)
           ;; FAILURE: Not a ground term.
           nil)
          ((logic.functionp x)
           (let ((name (logic.function-name x))
                 (args (logic.function-args x)))
             (if (and (equal name 'if)
                      (equal (len args) 3))
                 ;; "if" must be handled specially with lazy evaluation.
                 (let ((eval-test (rewrite.syntaxp-evaluator (first args) defs n)))
                   (and eval-test
                        (if (logic.unquote eval-test)
                            (rewrite.syntaxp-evaluator (second args) defs n)
                          (rewrite.syntaxp-evaluator (third args) defs n))))
               ;; other functions are eagerly evaluated.
               (let ((eval-args (rewrite.syntaxp-evaluator-list args defs n)))
                 (and eval-args
                      ;; eval-args is (t . ((quote val1) ... (quote valn)))
                      (let ((values (cdr eval-args)))
                        (if (lookup name (rewrite.syntaxp-arity-table))
                            ;; found a base function
                            (and (equal (cdr (lookup name (rewrite.syntaxp-arity-table))) (len values))
                                 (rewrite.syntaxp-base-evaluator (logic.function name values)))
                          ;; found a non-base function
                          (let* ((def (definition-list-lookup name defs)))
                            (and def
                                 (let ((formals (logic.function-args (logic.=lhs def)))
                                       (body    (logic.=rhs def)))
                                   (and (equal (len formals) (len values))
                                        (rewrite.syntaxp-evaluator (logic.substitute body (pair-lists formals values))
                                                           defs (- n 1)))))))))))))
          ((logic.lambdap x)
           ;; Eagerly evaluate the arguments to a lambda, then substitute them into
           ;; the lambda's body.
           (let ((formals (logic.lambda-formals x))
                 (body    (logic.lambda-body x))
                 (actuals (logic.lambda-actuals x)))
             (let ((eval-actuals (rewrite.syntaxp-evaluator-list actuals defs n)))
               (and eval-actuals
                    ;; eval-actuals is (t . ((quote val1) ... (quote valn)))
                    (let ((values (cdr eval-actuals)))
                      (rewrite.syntaxp-evaluator (logic.substitute body (pair-lists formals values)) defs (- n 1)))))))
          (t
           ;; FAILURE: cannot evaluate malformed terms
           nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-evaluator
                                    rewrite.syntaxp-evaluator-list
                                    rewrite.flag-syntaxp-evaluator)
          :expand (rewrite.flag-syntaxp-evaluator 'term x defs n))))

(defthmd definition-of-rewrite.syntaxp-evaluator-list
  (equal (rewrite.syntaxp-evaluator-list x defs n)
         (if (consp x)
             ;; Try to evaluate the first argument and then, recursively, the rest of
             ;; the arguments.
             (let ((first (rewrite.syntaxp-evaluator (car x) defs n))
                   (rest  (rewrite.syntaxp-evaluator-list (cdr x) defs n)))
               (if (and first rest)
                   ;; SUCCESS: evaluated the first and all other arguments.
                   (cons t (cons first (cdr rest)))
                 ;; FAILURE: couldn't evaluate some argument.
                 nil))
           ;; SUCCESS: the empty list can always be evaluted.
           (cons t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-evaluator
                                    rewrite.syntaxp-evaluator-list
                                    rewrite.flag-syntaxp-evaluator))))

(defthm rewrite.flag-syntaxp-evaluator-when-term
  (equal (rewrite.flag-syntaxp-evaluator 'term x defs n)
         (rewrite.syntaxp-evaluator x defs n))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-evaluator))))

(defthm rewrite.flag-syntaxp-evaluator-when-list
  (equal (rewrite.flag-syntaxp-evaluator 'list x defs n)
         (rewrite.syntaxp-evaluator-list x defs n))
  :hints(("Goal" :in-theory (enable rewrite.syntaxp-evaluator-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rewrite.syntaxp-evaluator))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rewrite.syntaxp-evaluator-list))))

(defthm rewrite.syntaxp-evaluator-list-when-not-consp
  (implies (not (consp x))
           (equal (rewrite.syntaxp-evaluator-list x defs n)
                  (cons t nil)))
  :hints(("Goal" :in-theory (enable definition-of-rewrite.syntaxp-evaluator-list))))

(defthm rewrite.syntaxp-evaluator-list-of-cons
  (equal (rewrite.syntaxp-evaluator-list (cons a x) defs n)
         (if (and (rewrite.syntaxp-evaluator a defs n)
                  (rewrite.syntaxp-evaluator-list x defs n))
             (cons t
                   (cons (rewrite.syntaxp-evaluator a defs n)
                         (cdr (rewrite.syntaxp-evaluator-list x defs n))))
           nil))
  :hints(("Goal" :in-theory (enable definition-of-rewrite.syntaxp-evaluator-list))))

(defthm true-listp-of-rewrite.syntaxp-evaluator-list
  (equal (true-listp (rewrite.syntaxp-evaluator-list x defs n))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-len-of-cdr-of-rewrite.syntaxp-evaluator-list
  (implies (force (rewrite.syntaxp-evaluator-list x defs n))
           (equal (len (cdr (rewrite.syntaxp-evaluator-list x defs n)))
                  (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-rewrite.syntaxp-evaluator-list
  (equal (consp (rewrite.syntaxp-evaluator-list x defs n))
         (if (rewrite.syntaxp-evaluator-list x defs n)
             t
           nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :shared-hyp (force (definition-listp defs))
  :thms ((term forcing-logic.constantp-of-cdr-of-rewrite.syntaxp-evaluator
               (implies (force (and (rewrite.syntaxp-evaluator x defs n)
                                    (logic.termp x)))
                        (equal (logic.constantp (rewrite.syntaxp-evaluator x defs n))
                               t)))
         (t forcing-logic.constant-listp-of-cdr-of-rewrite.syntaxp-evaluator-list
            (implies (force (and (logic.term-listp x)
                                 (rewrite.syntaxp-evaluator-list x defs n)))
                     (equal (logic.constant-listp (cdr (rewrite.syntaxp-evaluator-list x defs n)))
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-rewrite.syntaxp-evaluator
                              rewrite.flag-syntaxp-evaluator)
           :expand ((rewrite.syntaxp-evaluator x defs n))
           :induct (rewrite.flag-syntaxp-evaluator flag x defs n))))

(verify-guards rewrite.flag-syntaxp-evaluator
               :hints(("Goal" :in-theory (disable forcing-lookup-of-logic.function-name))))

(verify-guards rewrite.syntaxp-evaluator)
(verify-guards rewrite.syntaxp-evaluator-list)

