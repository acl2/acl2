; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2018 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "s4vec")
(include-book "xeval")
(local (std::add-default-post-define-hook :fix))

(fty::defmap svex-s4env
  :key-type svar
  :val-type s4vec
  :true-listp t
  :short "An alist mapping @(see svar)s to @(see 4vec)s.  Often used as an
environment that gives variables their values in @(see svex-eval)."
  ///
  (defthm svex-s4env-p-of-append
    (implies (and (svex-s4env-p x)
                  (svex-s4env-p y))
             (svex-s4env-p (append x y)))
    :hints(("Goal" :in-theory (enable svex-s4env-p)))))

(define svex-s4env-acons ((var svar-p) (val s4vec-p) (env svex-s4env-p))
  :returns (new-s4env svex-s4env-p)
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  (mbe :logic (cons (cons (svar-fix var)
                          (s4vec-fix val))
                    (svex-s4env-fix env))
       :exec (cons (cons var val) env))
  ///
  (deffixequiv svex-s4env-acons))


(define svex-s4env->svex-env ((x svex-s4env-p))
  :returns (env svex-env-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x)
                    (s4vec->4vec (cdar x)))
              (svex-s4env->svex-env (cdr x)))
      (svex-s4env->svex-env (cdr x))))
  ///
  (deffixequiv svex-s4env->svex-env :hints(("Goal" :in-theory (enable svex-s4env-fix)))))

(define svex-s4env-lookup ((var svar-p) (env svex-s4env-p))
  :returns (val s4vec-p)
  :prepwork ((local (defthm assoc-is-hons-assoc-equal-when-svex-s4env-p
                      (implies (svex-s4env-p env)
                               (equal (assoc var env)
                                      (hons-assoc-equal var env)))
                      :hints(("Goal" :in-theory (enable svex-s4env-p))))))
  (mbe :logic
       (s4vec-fix (cdr (hons-get (svar-fix var) env)))
       :exec
       (let ((look (hons-get var env)))
;; (assoc-equal var env)))
         (if look
             (cdr look)
           (s4vec-x))))
  ///
  (deffixequiv svex-s4env-lookup)

  (defthm svex-s4env-lookup-in-empty
    (equal (svex-s4env-lookup var nil) (s4vec-x)))

  (defthm svex-s4env-lookup-in-svex-s4env-acons
    (equal (svex-s4env-lookup var1 (svex-s4env-acons var2 val env))
           (if (svar-equiv var1 var2)
               (s4vec-fix val)
             (svex-s4env-lookup var1 env)))
    :hints(("Goal" :in-theory (enable svex-s4env-acons))))

  (defthm s4vec->4vec-of-svex-s4env-lookup
    (equal (s4vec->4vec (svex-s4env-lookup var env))
           (svex-env-lookup var (svex-s4env->svex-env env)))
    :hints(("Goal" :in-theory (enable svex-s4env->svex-env svex-s4env-lookup
                                      svex-env-lookup)))))



(define s4veclist-nth-safe ((n natp) (x s4veclist-p))
  :parents (s4veclist)
  :short "Like @(see nth) but, with proper @(see fty-discipline) for @(see
s4veclist)s.  ``Safely'' causes a run-time error if @('n') is out of bounds."
  :returns (elt s4vec-p)
  (mbe :logic (s4vec-fix (nth n x))
       :exec (or (nth n x)
                 (raise "Index ~x0 too large for s4veclist of length ~x1." n (len x))
                 (s4vec-x)))
  ///
  (deffixequiv s4veclist-nth-safe
    :hints(("Goal" :in-theory (enable s4veclist-fix))))

  (defthm s4veclist-nth-safe-of-nil
    (equal (s4veclist-nth-safe n nil)
           (s4vec-x)))

  (defthm s4veclist-nth-safe-of-cons
    (implies (syntaxp (quotep n))
             (equal (s4veclist-nth-safe n (cons a b))
                    (if (zp n)
                        (s4vec-fix a)
                      (s4veclist-nth-safe (1- n) b)))))

  (defthm len-of-s4veclist-fix
    (equal (len (s4veclist-fix x))
           (len x)))

  (defthm s4veclist-nth-safe-out-of-bounds
    (implies (<= (len x) (nfix n))
             (equal (s4veclist-nth-safe n x) (s4vec-x)))))


(defsection svex-s4apply-cases

  (defun svex-s4apply-collect-args (n max argsvar)
    (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
    (let* ((n   (nfix n))
           (max (nfix max)))
      (if (zp (- max n))
          nil
        (cons `(s4veclist-nth-safe ,n ,argsvar)
              (svex-s4apply-collect-args (+ 1 n) max argsvar)))))

  (defun svex-s4apply-cases-fn (argsvar optable)
    (b* (((when (atom optable))
          ;; Not a recognized function -- result is all Xes.
          '((otherwise
             (or (raise "Attempting to apply unknown function ~x0~%" fn)
                 (s4vec-x)))))
         ((list sym fn args) (car optable))
         (sfn (intern$ (concatenate 'string "S" (symbol-name fn)) "SV"))
         (call `(mbe :logic
                     (,sfn . ,(svex-s4apply-collect-args 0 (len args) argsvar))
                     :exec
                     (let ((arity-check (or (eql (len args) ,(len args))
                                            (raise "Improper arity for ~x0: expected ~x1 arguments but found ~x2.~%"
                                                   ',sym ',(len args) (len args)))))
                       (declare (ignore arity-check))
                       (,sfn . ,(svex-s4apply-collect-args 0 (len args) argsvar))))))
      (cons `(,sym ,call)
            (svex-s4apply-cases-fn argsvar (cdr optable)))))

  (defmacro svex-s4apply-cases (fn args)
    `(case ,fn
       . ,(svex-s4apply-cases-fn args *svex-op-table*))))

(define s4veclist->4veclist ((x s4veclist-p))
  :returns (4vecs 4veclist-p)
  (if (atom x)
      nil
    (cons (s4vec->4vec (car x))
          (s4veclist->4veclist (cdr x))))
  ///
  (defret s4vec->4vec-of-s4veclist-nth-safe
    (equal (s4vec->4vec (s4veclist-nth-safe n x))
           (4veclist-nth-safe n 4vecs))
    :hints(("Goal" :in-theory (enable s4veclist-nth-safe 4veclist-nth-safe)))))


(define svex-s4apply
  :parents (s4vecs)
  :short "Apply an @(see svex) function to some @(see s4vec) arguments."
  ((fn   fnsym-p    "Name of the function to apply.")
   (args s4veclist-p "Arguments to apply it to."))
  :returns (result s4vec-p "Result of applying the function.")
  :long "<p>Like @(see svex-apply), but applies to s4vecs instead of 4vecs.</p>"

  (let* ((fn (mbe  :exec fn :logic (fnsym-fix fn)))
         (args (mbe :logic (s4veclist-fix args) :exec args)))
    (svex-s4apply-cases fn args))
  ///
  (defret <fn>-correct
    (equal (s4vec->4vec result)
           (svex-apply fn (s4veclist->4veclist args)))
    :hints(("Goal" :in-theory (enable svex-apply)))))



(defines svex-s4eval
  :parents (evaluation)
  :short "Evaluate an @(see svex) in some s4vec environment."
  
  :long "<p>Like @(see svex-eval) but uses s4vec operations instead of 4vec ones.</p>"

  :verify-guards nil

  (define svex-s4eval ((x   svex-p     "Expression to evaluate.")
                       (env svex-s4env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :measure (svex-count x)
    :flag expr
    :returns (val s4vec-p "Value of @('x') under this environment.")
    (svex-case x
      :quote (4vec->s4vec x.val)
      :var   (svex-s4env-lookup x.name env)
      :call  (case x.fn
               ((? ?*)
                (b* (((unless (eql (len x.args) 3))
                      (svex-s4apply x.fn (svexlist-s4eval x.args env)))
                     (test (s3vec-fix (svex-s4eval (first x.args) env)))
                     ((s4vec test))
                     ((when (sparseint-equal test.upper 0))
                      (svex-s4eval (third x.args) env))
                     ((when (not (sparseint-equal test.lower 0)))
                      (svex-s4eval (second x.args) env))
                     (then (svex-s4eval (second x.args) env))
                     (else (svex-s4eval (third x.args) env)))
                  (case x.fn
                    (? (s4vec-? test then else))
                    (?* (s4vec-?* test then else)))))
               (bit?
                (b* (((unless (eql (len x.args) 3))
                      (svex-s4apply x.fn (svexlist-s4eval x.args env)))
                     (test (svex-s4eval (first x.args) env))
                     ((unless (s4vec-2vec-p test))
                      (s4vec-bit? test
                                  (svex-s4eval (second x.args) env)
                                  (svex-s4eval (third x.args) env)))
                     ((s4vec test))
                     ((when (sparseint-equal test.upper 0))
                      (svex-s4eval (third x.args) env))
                     ((when (sparseint-equal test.lower -1))
                      (svex-s4eval (second x.args) env)))
                  (s4vec-bit? test
                              (svex-s4eval (second x.args) env)
                              (svex-s4eval (third x.args) env))))
               (bit?!
                (b* (((unless (eql (len x.args) 3))
                      (svex-s4apply x.fn (svexlist-s4eval x.args env)))
                     (test (svex-s4eval (first x.args) env))
                     ((s4vec test))
                     ((when (and (sparseint-equal test.upper -1)
                                 (sparseint-equal test.lower -1)))
                      (svex-s4eval (second x.args) env))
                     ((when (sparseint-equal (sparseint-bitand test.upper test.lower) 0))
                      (svex-s4eval (third x.args) env)))
                  (s4vec-bit?! test
                               (svex-s4eval (second x.args) env)
                               (svex-s4eval (third x.args) env))))
               (bitand
                (b* (((unless (eql (len x.args) 2))
                      (svex-s4apply x.fn (svexlist-s4eval x.args env)))
                     (test (svex-s4eval (first x.args) env))
                     ((unless (s4vec-2vec-p test))
                      (s4vec-bitand test
                                    (svex-s4eval (second x.args) env)))
                     ((s4vec test))
                     ((when (sparseint-equal test.upper 0)) 0))
                  (s4vec-bitand test
                                (svex-s4eval (second x.args) env))))
               (bitor
                (b* (((unless (eql (len x.args) 2))
                      (svex-s4apply x.fn (svexlist-s4eval x.args env)))
                     (test (svex-s4eval (first x.args) env))
                     ((unless (s4vec-2vec-p test))
                      (s4vec-bitor test
                                   (svex-s4eval (second x.args) env)))
                     ((s4vec test))
                     ((when (sparseint-equal test.upper -1)) -1))
                  (s4vec-bitor test
                               (svex-s4eval (second x.args) env))))
               (otherwise
                (svex-s4apply x.fn (svexlist-s4eval x.args env))))))

  (define svexlist-s4eval
    :parents (evaluation)
    :short "Evaluate each @(see svex) in a list under the same environment."
    ((x   svexlist-p "List of expressions to evaluate.")
     (env svex-s4env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :returns (vals s4veclist-p "Values of the expressions in @('x') under this environment.")
    :measure (svexlist-count x)
    :flag list

    (if (atom x)
        nil
      (cons (svex-s4eval (car x) env)
            (svexlist-s4eval (cdr x) env))))
  ///
  (local (include-book "std/lists/len" :dir :system))

  (local (in-theory (disable default-car
                             default-cdr
                             4vec->lower-when-2vec-p
                             acl2::len-when-atom
                             svex-s4eval
                             svexlist-s4eval)))

  (local (defthm consp-of-svexlist-eval
           (equal (consp (svexlist-eval x env))
                  (consp x))
           :hints (("goal" :expand ((svexlist-eval x env))))))

  (local (defthm upper-lower-of-s3vec-fix
           (implies (and (3vec-p x)
                         (not (equal (4vec->lower x) 0)))
                    (not (equal (4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable 3vec-p)))))

  (local (defthm s4vec->accs-of-s3vec-fix
           (and (Equal (sparseint-val (s4vec->upper (s3vec-fix x)))
                       (4vec->upper (3vec-fix (s4vec->4vec x))))
                (Equal (sparseint-val (s4vec->lower (s3vec-fix x)))
                       (4vec->lower (3vec-fix (s4vec->4vec x)))))
           :hints (("goal" :use ((:instance s3vec-fix-correct))
                    :in-theory (e/d (s4vec->4vec)
                                    (s3vec-fix-correct))))))

  (local (defthm s4vec-?-cases
           (and (implies (equal (sparseint-val (s4vec->upper (s3vec-fix test))) 0)
                         (equal (4vec-? (s4vec->4vec test) then else)
                                (4vec-fix else)))
                (implies (not (equal (sparseint-val (s4vec->lower (s3vec-fix test))) 0))
                         (equal (4vec-? (s4vec->4vec test) then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?)))))

  (local (defthm s4vec-?*-cases
           (and (implies (equal (sparseint-val (s4vec->upper (s3vec-fix test))) 0)
                         (equal (4vec-?* (s4vec->4vec test) then else)
                                (4vec-fix else)))
                (implies (not (equal (sparseint-val (s4vec->lower (s3vec-fix test))) 0))
                         (equal (4vec-?* (s4vec->4vec test) then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))


  ;; (local (defthm s4vec-?*-cases
  ;;          (and (implies (equal (s4vec->upper (s3vec-fix test)) 0)
  ;;                        (equal (s4vec-?* test then else)
  ;;                               (s4vec-fix else)))
  ;;               (implies (not (equal (s4vec->lower (s3vec-fix test)) 0))
  ;;                        (equal (s4vec-?* test then else)
  ;;                               (s4vec-fix then))))
  ;;          :hints(("Goal" :in-theory (enable s4vec-?* s3vec-?*)))))

  (local (defthm s4vec-bitand-case
           (implies (and (equal (sparseint-val (s4vec->upper test)) 0)
                         (equal (sparseint-val (s4vec->lower test)) 0))
                    (equal (4vec-bitand (s4vec->4vec test) x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand s4vec->4vec)))))

  (local (defthm s4vec-bitor-case
           (implies (and (equal (sparseint-val (s4vec->upper test)) -1)
                         (equal (sparseint-val (s4vec->lower test)) -1))
                    (equal (4vec-bitor (s4vec->4vec test) x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor s4vec->4vec)))))

  (local (defthm s4vec-bit?-cases
           (and (implies (and (equal (sparseint-val (s4vec->upper test)) 0)
                              (equal (sparseint-val (s4vec->lower test)) 0))
                         (equal (4vec-bit? (s4vec->4vec test) then else)
                                (4vec-fix else)))
                (implies (and (equal (sparseint-val (s4vec->upper test)) -1)
                              (equal (sparseint-val (s4vec->lower test)) -1))
                         (equal (4vec-bit? (s4vec->4vec test) then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit? s4vec->4vec)))))

  (local (defthm s4vec-bit?!-cases
           (and (implies  (equal (logand (sparseint-val (s4vec->upper test))
                                         (sparseint-val (s4vec->lower test)))
                                 0)
                          (equal (4vec-bit?! (s4vec->4vec test) then else)
                                 (4vec-fix else)))
                (implies (and (equal (sparseint-val (s4vec->upper test)) -1)
                              (equal (sparseint-val (s4vec->lower test)) -1))
                         (equal (4vec-bit?! (s4vec->4vec test) then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit?! s4vec->4vec)))))



  ;; (local (defthm s4vec-bitor-case
  ;;          (implies (equal test -1)
  ;;                   (equal (s4vec-bitor test x)
  ;;                          -1))
  ;;          :hints(("Goal" :in-theory (enable s4vec-bitor s3vec-bitor)))))

  (verify-guards svex-s4eval)

  (memoize 'svex-s4eval :condition '(eq (svex-kind x) :call))

  ;; (local (in-theory (disable 4veclist-nth-safe-of-cons)))

  (local (defthm open-svexlist-eval
           (implies (consp args)
                    (equal (svexlist-eval args env)
                           (cons (svex-eval (car args) env)
                                 (svexlist-eval (Cdr args) env))))
           :hints(("Goal" :in-theory (enable svexlist-eval)))))

  (local (defthm len-plus-1-equal-const
           (implies (and (syntaxp (and (quotep n)
                                       (quotep m)))
                         (posp n)
                         (posp m))
                    (equal (equal (+ n (len x)) m)
                           (equal (len x) (- m n))))))

  (local (defthm s4veclist->4veclist-of-cons
           (equal (s4veclist->4veclist (cons a b))
                  (cons (s4vec->4vec a) (s4veclist->4veclist b)))
           :hints(("Goal" :in-theory (enable s4veclist->4veclist)))))


  (std::defret-mutual svex-s4eval-correct
    (defret <fn>-correct
      (equal (s4vec->4vec val)
             (svex-eval x (svex-s4env->svex-env env)))
      :hints ('(:expand (<call>
                         (svex-eval x (svex-s4env->svex-env env)))
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-apply)))
              (and stable-under-simplificationp
                   '(:in-theory (enable s4vec->4vec))))
      :fn svex-s4eval)

    (defret <fn>-correct
      (equal (s4veclist->4veclist vals)
             (svexlist-eval x (svex-s4env->svex-env env)))
      :hints ('(:expand (<call>)))
      :fn svexlist-s4eval)))


(defines svex-s4xeval
  :parents (svex-s4eval)
  (define svex-s4xeval ((x svex-p "Expression to evaluate."))
    :returns (val s4vec-p "Indication of always-constant bits (see below).")
    :measure (svex-count x)
    :short "Evaluate an svex using s4vecs in an all-X environment."
    :verify-guards nil
    (svex-case x
      :quote (4vec->s4vec x.val)
      :var (s4vec-x)
      :call
      (let ((x.fn (case x.fn
                       (=== '==)
                       (==? 'safer-==?)
                       (bit?! 'bit?)
                       (otherwise x.fn))))
        ;; Shortcuts for ?, bit?, bitand, bitor
        (case x.fn
          ((? ?*)
           (b* (((unless (eql (len x.args) 3))
                 (svex-s4apply x.fn (svexlist-s4xeval x.args)))
                (test (s3vec-fix (svex-s4xeval (first x.args))))
                ((s4vec test))
                ((when (sparseint-equal test.upper 0))
                 (svex-s4xeval (third x.args)))
                ((when (not (sparseint-equal test.lower 0)))
                 (svex-s4xeval (second x.args)))
                (then (svex-s4xeval (second x.args)))
                (else (svex-s4xeval (third x.args))))
             (case x.fn
               (? (s4vec-? test then else))
               (?* (s4vec-?* test then else)))))
          (bit?
           (b* (((unless (eql (len x.args) 3))
                 (svex-s4apply x.fn (svexlist-s4xeval x.args)))
                (test (svex-s4xeval (first x.args)))
                ((unless (s4vec-2vec-p test))
                 (s4vec-bit? test
                        (svex-s4xeval (second x.args))
                        (svex-s4xeval (third x.args))))
                (testval (s4vec->upper test))
                ((when (sparseint-equal testval 0))
                 (svex-s4xeval (third x.args)))
                ((when (sparseint-equal testval -1))
                 (svex-s4xeval (second x.args))))
             (s4vec-bit? test
                         (svex-s4xeval (second x.args))
                         (svex-s4xeval (third x.args)))))
          (bitand
           (b* (((unless (eql (len x.args) 2))
                 (svex-s4apply x.fn (svexlist-s4xeval x.args)))
                (test (svex-s4xeval (first x.args)))
                ((when (and (s4vec-2vec-p test)
                            (sparseint-equal (s4vec->upper test) 0))) 0))
             (s4vec-bitand test
                          (svex-s4xeval (second x.args)))))
          (bitor
           (b* (((unless (eql (len x.args) 2))
                 (svex-s4apply x.fn (svexlist-s4xeval x.args)))
                (test (svex-s4xeval (first x.args)))
                ((when (and (s4vec-2vec-p test)
                            (sparseint-equal (s4vec->upper test) -1))) -1))
             (s4vec-bitor test
                         (svex-s4xeval (second x.args)))))
          (otherwise
           (svex-s4apply x.fn (svexlist-s4xeval x.args)))))))

  (define svexlist-s4xeval ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (val s4veclist-p)
    :short "Maps @(see svex-s4xeval) over an @(see svex) list."
    (if (atom x)
        nil
      (cons (svex-s4xeval (car x))
            (svexlist-s4xeval (cdr x)))))
  ///
  (local (include-book "std/lists/len" :dir :system))

  (local (in-theory (disable default-car
                             default-cdr
                             4vec->lower-when-2vec-p
                             acl2::len-when-atom
                             svex-s4xeval
                             svexlist-s4xeval)))

  (local (defthm consp-of-svexlist-s4xeval
           (equal (consp (svexlist-s4xeval x))
                  (consp x))
           :hints (("goal" :expand ((svexlist-s4xeval x))))))

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

  (local (defthm 4vec-?*-cases
           (and (implies (equal (4vec->upper (3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (4vec->lower (3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (b* (((4vec test)))
                           (and (equal test.upper 0)
                                (equal test.lower 0)))
                         (equal (4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (b* (((4vec test)))
                           (and (equal test.upper -1)
                                (equal test.lower -1)))
                         (equal (4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-bit? 3vec-bit? 3vec-fix)))))

  (local (defthm 4vec-bitand-case
           (implies (b* (((4vec test)))
                      (and (equal test.upper 0)
                           (equal test.lower 0)))
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand 3vec-fix)))))

  (local (defthm 4vec-bitor-case
           (implies (b* (((4vec test)))
                      (and (equal test.upper -1)
                           (equal test.lower -1)))
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor 3vec-bitor 3vec-fix)))))

  (verify-guards svex-s4xeval
    :hints((and stable-under-simplificationp
                '(:in-theory (e/d (svex-s4apply len 4veclist-nth-safe nth)
                                  (svex-s4xeval))
                  :expand ((svexlist-s4xeval (svex-call->args x))
                           (svexlist-s4xeval (cdr (svex-call->args x)))
                           (svexlist-s4xeval (cddr (svex-call->args x))))))))

  (memoize 'svex-s4xeval :condition '(eq (svex-kind x) :call))

  (deffixequiv-mutual svex-s4xeval)

  (defthm svexlist-s4xeval-nil
    (equal (svexlist-s4xeval nil) nil))

  (defthm car-of-svexlist-s4xeval
    (s4vec-equiv (car (svexlist-s4xeval x))
                (svex-s4xeval (car x)))
    :hints(("Goal" :expand ((svexlist-s4xeval x))
            :in-theory (enable default-car))))

  (defthm cdr-of-svexlist-s4xeval
    (s4veclist-equiv (cdr (svexlist-s4xeval x))
                    (svexlist-s4xeval (cdr x)))
    :hints(("Goal" :expand ((svexlist-s4xeval x))
            :in-theory (enable default-cdr))))

  (defthm len-of-svexlist-s4xeval
    (equal (len (svexlist-s4xeval x))
           (len x))
    :hints(("Goal" :expand ((svexlist-s4xeval x)))))

  (defthm svexlist-s4xeval-of-append
    (equal (svexlist-s4xeval (append a b))
           (append (svexlist-s4xeval a)
                   (svexlist-s4xeval b)))
    :hints(("Goal" :in-theory (enable append svexlist-s4xeval))))

  
  (local (defthm open-svexlist-xeval
           (implies (consp args)
                    (equal (svexlist-xeval args)
                           (cons (svex-xeval (car args))
                                 (svexlist-xeval (Cdr args)))))
           :hints(("Goal" :in-theory (enable svexlist-xeval)))))

  (local (defthm len-plus-1-equal-const
           (implies (and (syntaxp (and (quotep n)
                                       (quotep m)))
                         (posp n)
                         (posp m))
                    (equal (equal (+ n (len x)) m)
                           (equal (len x) (- m n))))))

  (local (defthm s4veclist->4veclist-of-cons
           (equal (s4veclist->4veclist (cons a b))
                  (cons (s4vec->4vec a) (s4veclist->4veclist b)))
           :hints(("Goal" :in-theory (enable s4veclist->4veclist)))))

  (local (defthm sparseint-val-of-s4vec->lower
           (equal (sparseint-val (s4vec->lower x))
                  (4vec->lower (s4vec->4vec x)))
           :hints(("Goal" :in-theory (enable s4vec->4vec)))))
  (local (defthm sparseint-val-of-s4vec->upper
           (equal (sparseint-val (s4vec->upper x))
                  (4vec->upper (s4vec->4vec x)))
           :hints(("Goal" :in-theory (enable s4vec->4vec)))))

  (local (in-theory (disable 4VEC->UPPER-OF-S4VEC->4VEC
                             4VEC->LOWER-OF-S4VEC->4VEC)))

  (std::defret-mutual svex-s4xeval-is-svex-xeval
    (defret svex-s4xeval-is-svex-xeval
      (equal (s4vec->4vec val)
             (svex-xeval x))
      :hints ('(:expand (<call>
                         (svex-xeval x))
                :do-not '(preprocess))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-apply))))
      :fn svex-s4xeval)
    (defret svexlist-s4xeval-is-svexlist-xeval
      (equal (s4veclist->4veclist val)
             (svexlist-xeval x))
      :hints ('(:expand (<call>
                         (svexlist-xeval x))))
      :fn svexlist-s4xeval)))

