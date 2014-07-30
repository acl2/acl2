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



;; Below we introduce a generic evaluator function, and its mutually recursive
;; counterpart.  There are three arguments:
;;
;;   term(-list)   A ground term(-list) that we want to evaluate
;;   db            A database of definitions that we will use
;;   n             An "artificial" counter to ensure termination
;;
;; Like any other Milawa function, our evaluator is total and is defined for
;; all combinations of these inputs.  When the arguments are invalid in certain
;; ways, these functions "fail".  For example, what does it mean to evaluate
;; (f 1 2) if f is a function of arity 3?  Or suppose that our counter is too
;; small to successfully complete a computation.
;;
;; If we cannot evaluate a term successfully, then our term evaluator returns
;; nil.  In the list case, if *any* of our input terms cannot be evaluated
;; successfully, we return nil to signal failure for the whole list.
;;
;; Otherwise, if we are able to successfully evaluate a term, we return the
;; pair a (quoted) constant which represents this term's value.  For successful
;; list cases, we return (t . [x1 ... xn]), where x1...xn are the values
;; obtained by successively evaluating each term in the list.

(defund flag-generic-evaluator (flag x defs n)
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
        (ACL2::prog2$ (ACL2::cw "Warning: insufficient n given to generic-evaluator~%")
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
              (let ((eval-test (flag-generic-evaluator 'term (first args) defs n)))
                (and eval-test
                     (if (logic.unquote eval-test)
                         (flag-generic-evaluator 'term (second args) defs n)
                       (flag-generic-evaluator 'term (third args) defs n))))
            ;; other functions are eagerly evaluated.
            (let ((eval-args (flag-generic-evaluator 'list args defs n)))
              (and eval-args
                   ;; eval-args is (t . ((quote val1) ... (quote valn)))
                   (let* ((values     (cdr eval-args))
                          (atbl-entry (lookup name (logic.initial-arity-table))))
                     (if atbl-entry
                         ;; found a base function
                         (and (equal (cdr atbl-entry) (len values))
                              (logic.base-evaluator (logic.function name values)))

                       ;; found a non-base function
                       (let* ((def (definition-list-lookup name defs)))
                         (and def
                              (let ((formals (logic.function-args (logic.=lhs def)))
                                    (body    (logic.=rhs def)))
                                (and (equal (len formals) (len values))
                                     (flag-generic-evaluator 'term
                                                             (logic.substitute body (pair-lists formals values))
                                                             defs (- n 1)))))))))))))
       ((logic.lambdap x)
        ;; Eagerly evaluate the arguments to a lambda, then substitute them into
        ;; the lambda's body.
        (let ((formals (logic.lambda-formals x))
              (body    (logic.lambda-body x))
              (actuals (logic.lambda-actuals x)))
          (let ((eval-actuals (flag-generic-evaluator 'list actuals defs n)))
            (and eval-actuals
                 ;; eval-actuals is (t . ((quote val1) ... (quote valn)))
                 (let ((values (cdr eval-actuals)))
                   (flag-generic-evaluator 'term
                                           (logic.substitute body (pair-lists formals values))
                                           defs
                                           (- n 1)))))))
       (t
        ;; FAILURE: cannot evaluate malformed terms
        nil))
    (if (consp x)
        ;; Try to evaluate the first argument and then, recursively, the rest of
        ;; the arguments.
        (let ((first (flag-generic-evaluator 'term (car x) defs n))
              (rest  (flag-generic-evaluator 'list (cdr x) defs n)))
          (if (and first rest)
              ;; SUCCESS: evaluated the first and all other arguments.
              (cons t (cons first (cdr rest)))
            ;; FAILURE: couldn't evaluate some argument.
            nil))
      ;; SUCCESS: the empty list can always be evaluted.
      (cons t nil))))

(defund generic-evaluator (x defs n)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs)
                              (natp n))
                  :verify-guards nil))
  (flag-generic-evaluator 'term x defs n))

(defund generic-evaluator-list (x defs n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.ground-listp x)
                              (definition-listp defs)
                              (natp n))
                  :verify-guards nil))
  (flag-generic-evaluator 'list x defs n))

(defthmd definition-of-generic-evaluator
  (equal (generic-evaluator x defs n)
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
                 (let ((eval-test (generic-evaluator (first args) defs n)))
                   (and eval-test
                        (if (logic.unquote eval-test)
                            (generic-evaluator (second args) defs n)
                          (generic-evaluator (third args) defs n))))
               ;; other functions are eagerly evaluated.
               (let ((eval-args (generic-evaluator-list args defs n)))
                 (and eval-args
                      ;; eval-args is (t . ((quote val1) ... (quote valn)))
                      (let ((values (cdr eval-args)))
                        (if (lookup name (logic.initial-arity-table))
                            ;; found a base function
                            (and (equal (cdr (lookup name (logic.initial-arity-table))) (len values))
                                 (logic.base-evaluator (logic.function name values)))
                          ;; found a non-base function
                          (let* ((def (definition-list-lookup name defs)))
                            (and def
                                 (let ((formals (logic.function-args (logic.=lhs def)))
                                       (body    (logic.=rhs def)))
                                   (and (equal (len formals) (len values))
                                        (generic-evaluator (logic.substitute body (pair-lists formals values))
                                                           defs (- n 1)))))))))))))
          ((logic.lambdap x)
           ;; Eagerly evaluate the arguments to a lambda, then substitute them into
           ;; the lambda's body.
           (let ((formals (logic.lambda-formals x))
                 (body    (logic.lambda-body x))
                 (actuals (logic.lambda-actuals x)))
             (let ((eval-actuals (generic-evaluator-list actuals defs n)))
               (and eval-actuals
                    ;; eval-actuals is (t . ((quote val1) ... (quote valn)))
                    (let ((values (cdr eval-actuals)))
                      (generic-evaluator (logic.substitute body (pair-lists formals values)) defs (- n 1)))))))
          (t
           ;; FAILURE: cannot evaluate malformed terms
           nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable generic-evaluator
                                    generic-evaluator-list
                                    flag-generic-evaluator)
          :expand (flag-generic-evaluator 'term x defs n))))

(defthmd definition-of-generic-evaluator-list
  (equal (generic-evaluator-list x defs n)
         (if (consp x)
             ;; Try to evaluate the first argument and then, recursively, the rest of
             ;; the arguments.
             (let ((first (generic-evaluator (car x) defs n))
                   (rest  (generic-evaluator-list (cdr x) defs n)))
               (if (and first rest)
                   ;; SUCCESS: evaluated the first and all other arguments.
                   (cons t (cons first (cdr rest)))
                 ;; FAILURE: couldn't evaluate some argument.
                 nil))
           ;; SUCCESS: the empty list can always be evaluted.
           (cons t nil)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable generic-evaluator
                                    generic-evaluator-list
                                    flag-generic-evaluator))))

(defthm flag-generic-evaluator-when-term
  (equal (flag-generic-evaluator 'term x defs n)
         (generic-evaluator x defs n))
  :hints(("Goal" :in-theory (enable generic-evaluator))))

(defthm flag-generic-evaluator-when-list
  (equal (flag-generic-evaluator 'list x defs n)
         (generic-evaluator-list x defs n))
  :hints(("Goal" :in-theory (enable generic-evaluator-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition generic-evaluator))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition generic-evaluator-list))))

(defthm generic-evaluator-list-when-not-consp
  (implies (not (consp x))
           (equal (generic-evaluator-list x defs n)
                  (cons t nil)))
  :hints(("Goal" :in-theory (enable definition-of-generic-evaluator-list))))

(defthm generic-evaluator-list-of-cons
  (equal (generic-evaluator-list (cons a x) defs n)
         (if (and (generic-evaluator a defs n)
                  (generic-evaluator-list x defs n))
             (cons t
                   (cons (generic-evaluator a defs n)
                         (cdr (generic-evaluator-list x defs n))))
           nil))
  :hints(("Goal" :in-theory (enable definition-of-generic-evaluator-list))))

(defthm true-listp-of-generic-evaluator-list
  (equal (true-listp (generic-evaluator-list x defs n))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-len-of-cdr-of-generic-evaluator-list
  (implies (force (generic-evaluator-list x defs n))
           (equal (len (cdr (generic-evaluator-list x defs n)))
                  (len x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm consp-of-generic-evaluator-list
  (equal (consp (generic-evaluator-list x defs n))
         (if (generic-evaluator-list x defs n)
             t
           nil))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :shared-hyp (force (definition-listp defs))
  :thms ((term forcing-logic.constantp-of-cdr-of-generic-evaluator
               (implies (force (and (generic-evaluator x defs n)
                                    (logic.termp x)))
                        (equal (logic.constantp (generic-evaluator x defs n))
                               t)))
         (t forcing-logic.constant-listp-of-cdr-of-generic-evaluator-list
            (implies (force (and (logic.term-listp x)
                                 (generic-evaluator-list x defs n)))
                     (equal (logic.constant-listp (cdr (generic-evaluator-list x defs n)))
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-generic-evaluator
                              flag-generic-evaluator)
           :expand ((generic-evaluator x defs n))
           :induct (flag-generic-evaluator flag x defs n))))

(verify-guards flag-generic-evaluator
               :hints(("Goal" :in-theory (disable forcing-lookup-of-logic.function-name))))

(verify-guards generic-evaluator)
(verify-guards generic-evaluator-list)

