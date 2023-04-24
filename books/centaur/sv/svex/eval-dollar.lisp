
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>

;; Same as svex-eval but this one calls apply$ on unrecognized function symbols
;; Some functions are copied from eval.lisp and gently modified..

(in-package "SV")

(include-book "eval")

(defmacro svex-apply$-cases (fn args)
  `(case ,fn
     ,@(take (len *svex-op-table*) (svex-apply-cases-fn args *svex-op-table*))
     (otherwise
      (b* ((res (apply$ ,fn ,args)))
        (if (4vec-p res)
            res
          (or (raise "Attempting to apply a function that doesn't return a 4vec ~x0~%" ,fn)
              (4vec-x)))))))

;; Same as svex-apply but calls svex-apply$-cases instead
(define svex-apply$
  :short "Apply an @(see svex) function to some @(see 4vec) arguments. If an unrecognized svex function is given, call apply$."
  ((fn   fnsym-p    "Name of the function to apply.")
   (args 4veclist-p "Arguments to apply it to."))
  :returns (result 4vec-p "Result of applying the function.")
  (let* ((fn (mbe  :exec fn :logic (fnsym-fix fn)))
         (args (mbe :logic (4veclist-fix args) :exec args)))
    (svex-apply$-cases fn args))
  ///
  (deffixequiv svex-apply$)
  )

;; same as svex-eval but calls svex-apply$ instead.
(defines svex-eval$
  :parents (evaluation)
  :short "Evaluate an @(see svex) in some environment that calls apply$ on unrecognized ops."

  :long "Same as @(see svex-eval) but this one calls apply$ of the expression contains an unrecognized operator."

  :flag svex-eval$-flag
  :flag-local nil
  :verify-guards nil

  (define svex-eval$ ((x   svex-p     "Expression to evaluate.")
                      (env svex-env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :measure (svex-count x)
    :flag expr
    :returns (val 4vec-p "Value of @('x') under this environment."
                  :hints ((and stable-under-simplificationp
                               '(:expand ((4vec-p x))))))
    (svex-case x
               :quote x.val
               :var   (svex-env-fastlookup x.name env)
               :call  (mbe :logic
                           (svex-apply$ x.fn (svexlist-eval$ x.args env))
                           :exec
                           ;; Shortcuts for ?, bit?, bitand, bitor
                           (case x.fn
                             ((? ?*)
                              (b* (((unless (eql (len x.args) 3))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (3vec-fix (svex-eval$ (first x.args) env)))
                                   ((4vec test))
                                   ((when (eql test.upper 0))
                                    (svex-eval$ (third x.args) env))
                                   ((when (not (eql test.lower 0)))
                                    (svex-eval$ (second x.args) env))
                                   (then (svex-eval$ (second x.args) env))
                                   (else (svex-eval$ (third x.args) env)))
                                (case x.fn
                                  (? (4vec-? test then else))
                                  (?* (4vec-?* test then else)))))
                             (?!
                              (b* (((unless (eql (len x.args) 3))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (svex-eval$ (first x.args) env))
                                   ((4vec test))
                                   (testvec (logand test.upper test.lower))
                                   ((when (eql testvec 0))
                                    (svex-eval$ (third x.args) env)))
                                (svex-eval$ (second x.args) env)))
                             (bit?
                              (b* (((unless (eql (len x.args) 3))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (svex-eval$ (first x.args) env))
                                   ((when (eql test 0))
                                    (svex-eval$ (third x.args) env))
                                   ((when (eql test -1))
                                    (svex-eval$ (second x.args) env)))
                                (4vec-bit? test
                                           (svex-eval$ (second x.args) env)
                                           (svex-eval$ (third x.args) env))))
                             (bit?!
                              (b* (((unless (eql (len x.args) 3))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (4vec-1mask (svex-eval$ (first x.args) env)))
                                   ((when (eql test -1))
                                    (svex-eval$ (second x.args) env))
                                   ((when (eql test 0))
                                    (svex-eval$ (third x.args) env)))
                                (4vec-bitmux test
                                             (svex-eval$ (second x.args) env)
                                             (svex-eval$ (third x.args) env))))
                             (bitand
                              (b* (((unless (eql (len x.args) 2))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (svex-eval$ (first x.args) env))
                                   ((when (eql test 0)) 0))
                                (4vec-bitand test
                                             (svex-eval$ (second x.args) env))))
                             (bitor
                              (b* (((unless (eql (len x.args) 2))
                                    (svex-apply$ x.fn (svexlist-eval$ x.args env)))
                                   (test (svex-eval$ (first x.args) env))
                                   ((when (eql test -1)) -1))
                                (4vec-bitor test
                                            (svex-eval$ (second x.args) env))))
                             (otherwise
                              (svex-apply$ x.fn (svexlist-eval$ x.args env)))))))

  (define svexlist-eval$
    :parents (evaluation)
    :short "Evaluate each @(see svex) in a list under the same environment."
    ((x   svexlist-p "List of expressions to evaluate.")
     (env svex-env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :returns (vals 4veclist-p "Values of the expressions in @('x') under this environment.")
    :measure (svexlist-count x)
    :flag list

    (if (atom x)
        nil
      (cons (svex-eval$ (car x) env)
            (svexlist-eval$ (cdr x) env))))
  ///

  (local (defthm consp-of-svexlist-eval$
           (equal (consp (svexlist-eval$ x env))
                  (consp x))
           :hints (("goal" :expand ((svexlist-eval$ x env))))))

  (local (defthm upper-lower-of-3vec-fix
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm 4vec-?-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-? test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (equal test 0)
                         (equal (4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit?)))))

  (local (defthm 4vec-bit?!-cases
           (and (implies (equal test 0)
                         (equal (4vec-bitmux test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (4vec-bitmux test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bitmux logite)))))

  (local (in-theory (enable 4vec-bit?!)))
  
  (local (defthm 4vec-?*-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))

  (local (defthm 4vec-bitand-case
           (implies (equal test 0)
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand)))))

  (local (defthm 4vec-bitor-case
           (implies (equal test -1)
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor)))))

  (verify-guards svex-eval$
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (svex-apply$ len 4veclist-nth-safe nth 4vec-?!)
                                  (svex-eval$))
                             :expand ((svexlist-eval$ (svex-call->args x) env)
                                      (svexlist-eval$ (cdr (svex-call->args x)) env)
                                      (svexlist-eval$ (cddr (svex-call->args x)) env))))))

  (memoize 'svex-eval$ :condition '(eq (svex-kind x) :call)))

(defsection svexlist-eval$-basics
  :parents (svexlist-eval$)
  :short "Very basic list lemmas for @(see svexlist-eval$)."

  (local (in-theory (enable svex-eval$
                            svexlist-eval$)))

  (defthm svexlist-eval$-when-atom-cheap
    (implies (atom x)
             (equal (svexlist-eval$ x env) nil))
    :hints(("Goal" :in-theory (enable svexlist-eval$)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svexlist-eval$-nil
    (equal (svexlist-eval$ nil env)
           nil))

  (defthm car-of-svexlist-eval$
    (4vec-equiv (car (svexlist-eval$ x env))
                (svex-eval$ (car x) env)))

  (defthm cdr-of-svexlist-eval$
    (4veclist-equiv (cdr (svexlist-eval$ x env))
                    (svexlist-eval$ (cdr x) env)))

  (defthm svexlist-eval$-of-cons
    (equal (svexlist-eval$ (cons a b) env)
           (cons (svex-eval$ a env)
                 (svexlist-eval$ b env))))

  (defthm consp-of-svexlist-eval$
    (equal (consp (svexlist-eval$ x env))
           (consp x))
    :hints(("Goal" :expand (svexlist-eval$ x env))))

  (defthm svexlist-eval$-under-iff
    (iff (svexlist-eval$ x env)
         (consp x))
    :hints(("Goal" :expand (svexlist-eval$ x env))))

  (defthm len-of-svexlist-eval$
    (equal (len (svexlist-eval$ x env))
           (len x)))

  (defthm svexlist-eval$-of-append
    (equal (svexlist-eval$ (append a b) env)
           (append (svexlist-eval$ a env)
                   (svexlist-eval$ b env))))

  (defthm svex-eval$-of-nth
    (4vec-equiv (nth n (svexlist-eval$ x env))
                (svex-eval$ (nth n x) env)))

  (defthm nthcdr-of-svexlist-eval$
    (equal (nthcdr n (sv::svexlist-eval$ x env))
           (sv::svexlist-eval$ (nthcdr n x) env))
    :hints (("Goal" :in-theory (e/d (nthcdr))
             :induct (nthcdr n x)))))

(defsection svex-eval$-basics
  :parents (svex-eval$)
  :short "Very basic lemmas about @(see svex-eval$)."

  (local (in-theory (enable svex-eval$
                            svexlist-eval$)))

  "<h3>Congruence rules</h3>"

  (deffixequiv-mutual svex-eval$
    :hints (("goal" :expand ((svexlist-fix x)))))

  "<h3>svex-eval$ of constants/constructors</h3>"

  (make-event
   `(encapsulate nil
      (set-ignore-ok t)
      (defthm svex-eval$-of-quoted
        (implies (syntaxp (quotep x))
                 (equal (svex-eval$ x env)
                        ,(acl2::body 'svex-eval$ nil (w state))))
        :hints(("Goal" :in-theory (enable svex-eval$))))))

  (defthm svex-eval$-of-svex-call
    (equal (svex-eval$ (svex-call fn args) env)
           (svex-apply$ fn (svexlist-eval$ args env)))
    :hints(("Goal" :expand ((svex-eval$ (svex-call fn args) env)))))

  (defthm svex-eval$-when-fncall
    (implies (equal (svex-kind x) :call)
             (equal (svex-eval$ x env)
                    (svex-apply$ (svex-call->fn x)
                                 (svexlist-eval$ (svex-call->args x) env))))
    :hints(("Goal" :in-theory (enable svex-eval$))))

  (defthm svex-eval$-when-quote
    (implies (eq (svex-kind x) :quote)
             (equal (svex-eval$ x env)
                    (svex-quote->val x)))
    :hints(("Goal" :in-theory (enable svex-eval$)))))

(define svex-alist-eval$-aux ((x   svex-alist-p)
                              (env svex-env-p))
  :parents (svex-alist-eval$)
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (xx svex-env-p :hints(("Goal" :in-theory (enable svex-env-p))))
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (cons (caar x)
                    (svex-eval$ (cdar x) env))
              (svex-alist-eval$-aux (cdr x) env))
      (svex-alist-eval$-aux (cdr x) env))))

(define svex-alist-eval$
  :parents (evaluation svex-alist)
  :short "Evaluate every expression in an @(see svex-alist) under the same environment. If there is an unrecognized svex-op, then call apply$."
  :long "Same as @(see svex-alist-eval) but this one calls apply$ of the expression contains an unrecognized operator."

  ((x   svex-alist-p "Alist of variables to @(see svex) expressions to evaluate.
                      Need not be fast.")
   (env svex-env-p   "Environment to evaluate the expressions under.  Should
                      be a @(see fast-alist)."))
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (result svex-env-p
                   "New (slow) alist, binds the variables to their expressions'
                    values."
                   :hints(("Goal" :in-theory (enable svex-env-p))))
  :Verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (if (mbt (and (consp (car x)) (svar-p (caar x))))
             (cons (cons (caar x)
                         (svex-eval$ (cdar x) env))
                   (svex-alist-eval$ (cdr x) env))
           (svex-alist-eval$ (cdr x) env)))
       :exec (with-fast-alist env (svex-alist-eval$-aux x env)))
  ///
  (deffixequiv svex-alist-eval$)

  (local (defthm svex-alist-eval$-aux-elim
           (equal (svex-alist-eval$-aux x env)
                  (svex-alist-eval$ x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval$-aux)))))

  (verify-guards svex-alist-eval$)

  (defthm svex-env-lookup-of-svex-alist-eval$
    (equal (svex-env-lookup k (svex-alist-eval$ x env))
           (let ((xk (svex-lookup k x)))
             (if xk (svex-eval$ xk env) (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defthm svex-env-boundp-of-svex-alist-eval$
    (iff (svex-env-boundp k (svex-alist-eval$ x env))
         (svex-lookup k x))
    :hints(("Goal" :in-theory (enable svex-env-boundp svex-lookup))))

  (defthm svex-alist-eval$-of-append
    (equal (svex-alist-eval$ (append a b) env)
           (append (svex-alist-eval$ a env)
                   (svex-alist-eval$ b env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval$ append))))

  (defthm alist-keys-of-svex-alist-eval$
    (equal (alist-keys (svex-alist-eval$ x env))
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval$ alist-keys)))))

;;;;;; Now sanity checks ;;;;;;

(defines svex-no-foreign-op-p
  :parents (evaluation)
  :short "Check if a given expression includes any operator that is included in *svex-op-table*"
  (define svex-no-foreign-op-p-aux ((x svex-p)
                                    &optional
                                    (op-table '(make-fast-alist *svex-op-table*)))
    :returns (result booleanp)
    :flag expr
    :measure (svex-count x)
    (svex-case x
               :quote t
               :var   t
               :call (and (hons-get x.fn op-table)
                          (svexlist-no-foreign-op-p-aux x.args op-table))))
  (define svexlist-no-foreign-op-p-aux ((x   svexlist-p)
                                        &optional
                                        (op-table '(make-fast-alist *svex-op-table*)))
    :parents (evaluation)
    :measure (svexlist-count x)
    :returns (result booleanp)
    :flag list
    (if (atom x)
        t
      (and (svex-no-foreign-op-p-aux (car x) op-table)
           (svexlist-no-foreign-op-p-aux (cdr x) op-table))))
  ///
  (memoize 'svex-no-foreign-op-p-aux-fn :condition '(eq (svex-kind x) :call))

  (define svex-no-foreign-op-p ((x svex-p))
    (b* ((op-table *svex-op-table*))
      (with-fast-alist op-table
        (svex-no-foreign-op-p-aux x op-table))))
  (define svexlist-no-foreign-op-p ((x svexlist-p))
    (b* ((op-table *svex-op-table*))
      (with-fast-alist op-table
        (svexlist-no-foreign-op-p-aux x op-table))))
  (define svex-alist-no-foreign-op-p ((x svex-alist-p))
    (and (mbt (svex-alist-p x))
         (svexlist-no-foreign-op-p (strip-cdrs x))))
  )

(defthm svex-apply$-is-svex-apply
  (implies (assoc-equal fn *svex-op-table*)
           (equal (svex-apply$ fn args)
                  (svex-apply fn args)))
  :hints (("Goal"
           :in-theory (e/d (svex-apply$
                            svex-apply)
                           ()))))

(std::defret-mutual svex-eval$-is-svex-eval
  (defret svex-eval$-is-svex-eval
    (implies (svex-no-foreign-op-p x)
             (equal (svex-eval$ x env)
                    (svex-eval x env)))
    :fn svex-eval$)
  (defret svexlist-eval$-is-svexlist-eval
    (implies (svexlist-no-foreign-op-p x)
             (equal (svexlist-eval$ x env)
                    (svexlist-eval x env)))
    :fn svexlist-eval$)
  :mutual-recursion svex-eval$
  :hints (("Goal"
           :in-theory (e/d (svex-no-foreign-op-p
                            svex-no-foreign-op-p-aux
                            svexlist-no-foreign-op-p
                            svexlist-no-foreign-op-p-aux
                            svex-eval$
                            svex-eval
                            svexlist-eval$
                            svexlist-eval)
                           ()))))

(defthm svex-alist-eval$-is-svex-alist-eval
    (implies (svex-alist-no-foreign-op-p x)
             (equal (svex-alist-eval$ x env)
                    (svex-alist-eval x env)))
    :hints (("Goal"
             :expand ((:free (x y)
                             (SVEXLIST-NO-FOREIGN-OP-P (CONS x y)))
                      (:free (x y z)
                             (SVEXLIST-NO-FOREIGN-OP-P-AUX (cons x y) z)))
             :do-not-induct t
             :induct (svex-alist-eval x env)
             :in-theory (e/d (SVEX-ALIST-P
                              SVEX-NO-FOREIGN-OP-P
                              SVEXLIST-NO-FOREIGN-OP-P
                              svex-alist-no-foreign-op-p
                              svex-alist-eval
                              SVEX-ALIST-EVAL$)
                             ())))
    )
