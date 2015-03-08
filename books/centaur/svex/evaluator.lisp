; SVEX - Symbolic, Vector-Level Hardware Description Library
; Copyright (C) 2014 Centaur Technology
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

(in-package "SVEX")
(include-book "4vec")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (in-theory (disable acl2::nth-when-zp)))

(defxdoc evaluator.lisp :parents (svex-eval))
(local (xdoc::set-default-parents evaluator.lisp))

(fty::deflist 4veclist :elt-type 4vec :true-listp t :parents (4vec))
(define 4veclist-nth ((n natp) (x 4veclist-p))
  :returns (elt 4vec-p)
  (mbe :logic (4vec-fix (nth n x))
       :exec (or (nth n x) (4vec-x)))
  ///
  (fty::deffixequiv 4veclist-nth
    :hints(("Goal" :in-theory (enable 4veclist-fix))))
  (defthm 4veclist-nth-of-nil
    (equal (4veclist-nth n nil) (4vec-x))))

(fty::defalist svex-env :key-type svar :val-type 4vec :true-listp t)

(defthm svex-env-p-of-append
  (implies (and (Svex-env-p x)
                (svex-env-p y))
           (svex-env-p (append x y)))
  :hints(("Goal" :in-theory (enable svex-env-p))))

(define svex-env-acons ((var svar-p) (v 4vec-p) (a svex-env-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (aa svex-env-p)
  (mbe :logic (cons (cons (svar-fix var)
                          (4vec-fix v))
                    (svex-env-fix a))
       :exec (cons (cons var v) a))
  ///
  (fty::deffixequiv svex-env-acons))

(define svex-env-lookup ((k svar-p) (env svex-env-p))
  :returns (v 4vec-p)
  :prepwork ((local (defthm assoc-is-hons-assoc-equal-when-svex-env-p
                      (implies (svex-env-p x)
                               (equal (assoc k x)
                                      (hons-assoc-equal k x)))
                      :hints(("Goal" :in-theory (enable svex-env-p))))))
  (mbe :logic (4vec-fix (cdr (hons-assoc-equal (svar-fix k) (svex-env-fix env))))
       :exec (let ((look (assoc-equal k env)))
               (if look
                   (cdr look)
                 (4vec-x))))
  ///
  (fty::deffixequiv svex-env-lookup)

  (defthm svex-env-lookup-in-empty
    (equal (svex-env-lookup k nil) (4vec-x)))

  (defthm svex-env-lookup-in-svex-env-acons
    (equal (svex-env-lookup k1 (svex-env-acons k2 v x))
           (if (svar-equiv k1 k2)
               (4vec-fix v)
             (svex-env-lookup k1 x)))
    :hints(("Goal" :in-theory (enable svex-env-acons)))))

(define svex-env-boundp ((k svar-p) (env svex-env-p))
  :returns (boundp)
  :prepwork ((local (defthm assoc-is-hons-assoc-equal-when-svex-env-p
                      (implies (svex-env-p x)
                               (equal (assoc k x)
                                      (hons-assoc-equal k x)))
                      :hints(("Goal" :in-theory (enable svex-env-p))))))
  (mbe :logic (consp (hons-assoc-equal (svar-fix k) (svex-env-fix env)))
       :exec (consp (assoc-equal k env))))

(define svex-env-fastlookup ((k svar-p) (env svex-env-p))
  :enabled t
  :guard-hints (("goal" :in-theory (enable svex-env-lookup)))
  (mbe :logic (svex-env-lookup k env)
       :exec (let ((look (hons-get k env)))
               (if look
                   (cdr look)
                 (4vec-x)))))


;; Svex symbol maps to actual function called followed by element types
(defconst *svex-op-table*
  '((id        4vec-fix            (x)                 "identity function")
    (bitsel    4vec-bit-extract    (index x)           "bit select")
    (unfloat   3vec-fix            (x)                 "change Z bits to Xes")
    (bitnot    4vec-bitnot         (x)                 "bitwise negation")
    (bitand    4vec-bitand         (x y)               "bitwise AND")
    (bitor     4vec-bitor          (x y)               "bitwise OR")
    (bitxor    4vec-bitxor         (x y)               "bitwise XOR")
    (res       4vec-res            (x y)               "resolve (short together)")
    (resand    4vec-resand         (x y)               "resolve wired AND")
    (resor     4vec-resor          (x y)               "resolve wired OR")
    (override  4vec-override       (x y)               "resolve different strengths")
    (onp       4vec-onset          (x)                 "identity, except Z becomes 0")
    (offp      4vec-offset         (x)                 "negation, except Z becomes 0")
    (uand      4vec-reduction-and  (x)                 "unary (reduction) AND")
    (uor       4vec-reduction-or   (x)                 "unary (reduction) OR")
    (uxor      4vec-parity         (x)                 "reduction XOR, i.e. parity")
    (zerox     4vec-zero-ext       (width x)           "zero extend")
    (signx     4vec-sign-ext       (width x)           "sign extend")
    (concat    4vec-concat         (width x y)         "concatenate at a given bit width")
    (blkrev    4vec-rev-blocks     (width bsz x)       "reverse order of blocks")
    (rsh       4vec-rsh            (shift x)           "right shift")
    (lsh       4vec-lsh            (shift x)           "left shift")
    (+         4vec-plus           (x y)               "addition")
    (b-        4vec-minus          (x y)               "subtraction")
    (u-        4vec-uminus         (x)                 "unary minus")
    (*         4vec-times          (x y)               "multiplication")
    (/         4vec-quotient       (x y)               "division")
    (%         4vec-remainder      (x y)               "modulus")
    (<         4vec-<              (x y)               "less than")
    (==        4vec-==             (x y)               "equality")
    (==?       4vec-wildeq         (x y)               "wildcard equality")
    (?         4vec-?              (test then else)    "if-then-else")
    (bit?      4vec-bit?           (test then else)    "bitwise if-then-else")))


(defun svex-apply-collect-args (n max argsvar)
  (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
  (let* ((n (nfix n))
         (max (nfix max)))
    (if (zp (- max n))
        nil
      (cons `(4veclist-nth ,n ,argsvar)
            (svex-apply-collect-args (+ 1 n) max argsvar)))))


(defun svex-apply-cases-fn (argsvar optable)
  (b* (((when (atom optable)) '((otherwise (4vec-x))))
       ((list sym fn args) (car optable))
       (call `(,fn . ,(svex-apply-collect-args 0 (len args) argsvar))))
    (cons `(,sym ,call)
          (svex-apply-cases-fn argsvar (cdr optable)))))

(defun svcall-fn (fn args)
  (declare (xargs :guard t))
  (b* ((look (assoc fn *svex-op-table*))
       ((unless look)
        (er hard? 'svcall "Svex function doesn't exist: ~x0" fn))
       (formals (third look))
       ((unless (eql (len formals) (len args)))
        (er hard? 'svcall "Wrong arity for call of ~x0" fn)))
    `(svex-call ',fn (list . ,args))))

(defmacro svcall (fn &rest args)
  (svcall-fn fn args))


(defmacro svex-apply-cases (fn args)
  `(case ,fn
     . ,(svex-apply-cases-fn args *svex-op-table*)))

;; (defthm svobj-p-when-4vec-p
;;   (implies (4vec-p x)
;;            (svobj-p x))
;;   :hints(("Goal" :in-theory (enable svobj-p))))

(define svex-apply ((fn fnsym-p) (args 4veclist-p))
  :parents (svex-eval)
  :short "Apply an svex function to a list of @(see 4vec) arguments"
  :long "<p>See @(see svex-functions) for the list of functions recognized.</p>"
  :returns (res 4vec-p)
  (let* ((fn (mbe :logic (fnsym-fix fn) :exec fn))
         (args (mbe :logic (4veclist-fix args) :exec args)))
    (svex-apply-cases fn args))
  ///
  (fty::deffixequiv svex-apply))


(local (defun syms->strings (x)
         (if (atom (cdr x))
             (list (symbol-name (car x)))
           (cons (symbol-name (car x))
                 (cons " "
                       (syms->strings (cdr x)))))))

(local (defun optable-to-xdoc-aux (optable acc)
         ;; collects a reversed list of strings
         (b* (((when (atom optable)) acc)
              ((list name fn args descrip) (car optable))
              (entry `("<tr><td>@('("
                       ,@(syms->strings (cons name args))
                       ")')</td><td>@(see " ,(symbol-name fn)
                       ")</td><td>" ,descrip "</td></tr>" "
")))
           (optable-to-xdoc-aux (cdr optable) (revappend entry acc)))))

(local (defun optable-to-xdoc ()
         (declare (xargs :mode :program))
         (str::fast-string-append-lst
          `("<p>The following table shows the function symbols (all
in the SVEX package) and their meanings.</p>
<table>
<tr><th>SVEX form</th><th>4vec function</th><th>Description</th></tr>
"
            ,@(reverse (optable-to-xdoc-aux *svex-op-table* nil))
            "</table>"))))

(make-event
 `(defxdoc svex-functions
    :parents (svex)
    :short "Svex function symbols and their meanings"
    :long ,(optable-to-xdoc)))
(defines svex-eval
  :parents (svex)
  :short "Concrete evaluation of svex formulas"
  :long "<p>Svex-eval is a straightforward evaluator for svex formulas.  It
takes an svex object and an environment mapping variables (@(see svar) objects)
to @(see 4vec) values, and returns the 4vec value of the formula under that
assignment in the obvious way.  Functions are applied using @(see svex-apply).
Also see @(see svex-functions) for the list of recognized svex function symbols
and their meanings.</p>"
  :flag svex-eval-flag
  :flag-local nil
  :verify-guards nil
  (define svex-eval ((x svex-p)
                     (env svex-env-p))
    ;; :guard (svex-aok x *svex-arity-table*)
    :measure (svex-count x)
    :flag expr
    :returns (val 4vec-p :hints ((and stable-under-simplificationp
                                       '(:expand ((4vec-p x))))))
    (svex-case x
      :quote x.val
      :var (svex-env-fastlookup x.name env)
      :call (svex-apply x.fn (svexlist-eval x.args env))))

  (define svexlist-eval ((x svexlist-p)
                         (env svex-env-p))
    ;; :guard (svex-aok-list x *svex-arity-table*)
    :measure (svexlist-count x)
    :flag list
    :returns (vals 4veclist-p)
    (if (atom x)
        nil
      (cons (svex-eval (car x) env)
            (svexlist-eval (cdr x) env))))
  ///

  (verify-guards svex-eval)

  (fty::deffixequiv-mutual svex-eval
    :hints (("goal" :expand ((svexlist-fix x)))))

  (defthm len-of-svexlist-eval
    (equal (len (svexlist-eval x env))
           (len x))
    :hints(("Goal" :in-theory (enable svexlist-eval))))


  (defthm car-of-svexlist-eval
    (4vec-equiv (car (svexlist-eval x env))
                 (svex-eval (car x) env))
    :hints(("Goal" :in-theory (enable svexlist-eval))))

  (defthm cdr-of-svexlist-eval
    (4veclist-equiv (cdr (svexlist-eval x env))
                     (svexlist-eval (cdr x) env))
    :hints(("Goal" :in-theory (enable svexlist-eval))))

  (defthm svexlist-eval-nil
    (equal (svexlist-eval nil env) nil))

  (defthm svexlist-eval-of-append
    (equal (svexlist-eval (append a b) env)
           (append (svexlist-eval a env)
                   (svexlist-eval b env)))
    :hints(("Goal" :in-theory (enable append))))

  (memoize 'svex-eval :condition '(eq (svex-kind x) :call)))


(defines svex-xeval
  :parents (svex-eval)
  :short "Evaluate an svex under the empty (all-X) environment"
  :long "<p>@('(svex-xeval x)') is the same as @('(svex-eval x nil)').  We
provide a separate function for this special case because having a single
argument improves memoization performance, and this function is commonly used
in @(see svex-rewriting) to check whether a given expression only has one
possible value.</p>"
  :verify-guards nil
  (define svex-xeval ((x svex-p))
    :measure (svex-count x)
    :returns (val (equal val (svex-eval x nil))
                  :hints ('(:expand ((svex-eval x nil)))))
    (svex-case x
      :quote x.val
      :var (4vec-x)
      :call (svex-apply x.fn (svexlist-xeval x.args))))
  (define svexlist-xeval ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (val (equal val (svexlist-eval x nil))
                  :hints ('(:expand ((svexlist-eval x nil)))))
    (if (atom x)
        nil
      (cons (svex-xeval (car x))
            (svexlist-xeval (cdr x)))))
  ///
  (verify-guards svex-xeval)

  (memoize 'svex-xeval :condition '(eq (svex-kind x) :call)))



(define svex-alist-eval-aux ((x svex-alist-p) (env svex-env-p))
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (xx svex-env-p :hints(("Goal" :in-theory (enable svex-env-p))))
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cons (mbe :logic (svar-fix (caar x))
                         :exec (caar x))
                    (svex-eval (cdar x) env))
              (svex-alist-eval-aux (cdr x) env))
      (svex-alist-eval-aux (cdr x) env))))



(define svex-alist-eval ((x svex-alist-p) (env svex-env-p))
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (xx svex-env-p :hints(("Goal" :in-theory (enable svex-env-p))))
  :Verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (if (mbt (consp (car x)))
             (cons (cons (mbe :logic (svar-fix (caar x))
                              :exec (caar x))
                         (svex-eval (cdar x) env))
                   (svex-alist-eval (cdr x) env))
           (svex-alist-eval (cdr x) env)))
       :exec (with-fast-alist env (svex-alist-eval-aux x env)))
  ///
  (fty::deffixequiv svex-alist-eval)

  (local (defthm svex-alist-eval-aux-elim
           (equal (svex-alist-eval-aux x env)
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval-aux)))))

  (verify-guards svex-alist-eval)

  (defthm svex-env-lookup-of-svex-alist-eval
    (equal (svex-env-lookup k (svex-alist-eval x env))
           (let ((xk (svex-lookup k x)))
             (if xk (svex-eval xk env) (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defthm svex-alist-eval-of-append
    (equal (svex-alist-eval (append a b) env)
           (append (svex-alist-eval a env)
                   (svex-alist-eval b env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval append)))))


(defalist svex-memotable :key-type svex :val-type 4vec)

(defthm 4vec-p-lookup-in-svex-memotable
  (implies (and (svex-memotable-p x)
                (hons-assoc-equal k x))
           (4vec-p (cdr (hons-assoc-equal k x)))))

(defines svex-eval-memo
  ;; Self-memoized version of svex-eval, for GL
  :verify-guards nil
  (define svex-eval-memo ((x svex-p)
                          (env svex-env-p)
                          (memo svex-memotable-p))
    :returns (mv (res 4vec-p)
                 (memo1 svex-memotable-p))
    :measure (svex-count x)
    (b* ((memo (svex-memotable-fix memo)))
      (svex-case x
        :quote (mv x.val memo)
        :var (mv (svex-env-fastlookup x.name env) memo)
        :call (b* ((x (svex-fix x))
                   (look (hons-get x memo))
                   ((when look) (mv (cdr look) memo))
                   ((mv args memo) (svexlist-eval-memo x.args env memo))
                   (res (svex-apply x.fn args))
                   (memo (hons-acons x res memo)))
                (mv res memo)))))
  (define svexlist-eval-memo ((x svexlist-p)
                              (env svex-env-p)
                              (memo svex-memotable-p))
    :returns (mv (res 4veclist-p)
                 (memo1 svex-memotable-p))
    :measure (svexlist-count x)
    (b* ((memo (svex-memotable-fix memo))
         ((when (atom x)) (mv nil memo))
         ((mv first memo) (svex-eval-memo (car x) env memo))
         ((mv rest memo) (svexlist-eval-memo (cdr x) env memo)))
      (mv (cons first rest) memo)))
  ///
  (deffixequiv-mutual svex-eval-memo)
  (verify-guards svex-eval-memo)

  (defun-sk svex-eval-memotable-ok (memo env)
    (forall x
            (implies (hons-assoc-equal x (svex-memotable-fix memo))
                     (equal (cdr (hons-assoc-equal x (svex-memotable-fix memo)))
                            (svex-eval x env))))
    :rewrite :direct)

  (in-theory (disable svex-eval-memotable-ok
                      svex-eval-memotable-ok-necc))
  (local (in-theory (enable svex-eval-memotable-ok-necc)))

  (defthm svex-eval-memotable-ok-empty
    (svex-eval-memotable-ok nil env)
    :hints(("Goal" :in-theory (enable svex-eval-memotable-ok))))

  (defthm svex-eval-memotable-ok-fix
    (implies (svex-eval-memotable-ok memo env)
             (svex-eval-memotable-ok (svex-memotable-fix memo) env))
    :hints(("Goal" :expand ((svex-eval-memotable-ok (svex-memotable-fix memo) env)))))

  (defthm svex-eval-memotable-ok-extend
    (implies (and (svex-eval-memotable-ok memo env)
                  (equal val (svex-eval x env)))
             (svex-eval-memotable-ok
              (cons (cons x val) memo) env))
    :hints (("goal" :expand ((svex-eval-memotable-ok
                              (cons (cons x (svex-eval x env)) memo) env)))))

  (local (in-theory (disable svex-eval-memo svexlist-eval-memo)))

  (defthm-svex-eval-memo-flag
    (defthm svex-eval-memo-correct
      (b* (((mv res memo1) (svex-eval-memo x env memo)))
        (implies (svex-eval-memotable-ok memo env)
                 (and (svex-eval-memotable-ok memo1 env)
                      (equal res (svex-eval x env)))))
      :hints ('(:expand ((svex-eval-memo x env memo)
                         (svex-eval x env))))
      :flag svex-eval-memo)
    (defthm svexlist-eval-memo-correct
      (b* (((mv res memo1) (svexlist-eval-memo x env memo)))
        (implies (svex-eval-memotable-ok memo env)
                 (and (svex-eval-memotable-ok memo1 env)
                      (equal res (svexlist-eval x env)))))
      :hints ('(:expand ((svexlist-eval-memo x env memo)
                         (svexlist-eval x env))))
      :flag svexlist-eval-memo)))



(defalist svar-boolmasks :key-type svar :val-type integerp)

(define svar-boolmasks-lookup ((v svar-p) (boolmasks svar-boolmasks-p))
  :returns (boolmask integerp :rule-classes :type-prescription)
  (ifix (cdr (hons-get (mbe :logic (svar-fix v) :exec v)
                       (svar-boolmasks-fix boolmasks))))
  ///
  (deffixequiv svar-boolmasks-lookup))



;; Placeholder: this is used by svtvs, b/c it is advantageous in symbolic
;; evaluation to hold constant a set of variables that are expected to possibly
;; be bound in the environment.  Logically, these are irrelevant.
(define svexlist-eval-with-vars ((x svexlist-p)
                                 (vars svarlist-p)
                                 (boolmasks svar-boolmasks-p)
                                 (env svex-env-p))
  :ignore-ok t
  :enabled t
  (svexlist-eval x env))

(define svex-alist-eval-with-vars ((x svex-alist-p)
                                   (vars svarlist-p)
                                   (boolmasks svar-boolmasks-p)
                                   (env svex-env-p))
  :returns (res (equal res (svex-alist-eval x env))
                :hints(("Goal" :in-theory (enable svex-alist-eval pairlis$ svex-alist-keys
                                                  svex-alist-vals svexlist-eval))))
  (pairlis$ (svex-alist-keys x)
            (svexlist-eval-with-vars (hons-copy (svex-alist-vals x)) vars boolmasks env)))



(make-event
 `(encapsulate nil
    (set-ignore-ok t)
    (defthm svex-eval-of-quoted
      (implies (syntaxp (quotep x))
               (equal (svex-eval x env)
                      ,(acl2::body 'svex-eval nil (w state))))
      :hints(("Goal" :in-theory (enable svex-eval))))))

(defthm svex-eval-of-svex-call
  (equal (svex-eval (svex-call fn args) env)
         (svex-apply fn (svexlist-eval args env)))
  :hints(("Goal" :expand ((svex-eval (svex-call fn args) env)))))

(defthm svex-eval-when-fncall
  (implies (equal (svex-kind x) :call)
           (equal (svex-eval x env)
                  (svex-apply (svex-call->fn x)
                              (svexlist-eval (svex-call->args x) env))))
  :hints(("Goal" :in-theory (enable svex-eval))))

(defthm svex-eval-when-quote
  (implies (eq (svex-kind x) :quote)
           (equal (svex-eval x env)
                  (svex-quote->val x)))
  :hints(("Goal" :in-theory (enable svex-eval))))


(defthm svexlist-eval-of-cons
  (equal (svexlist-eval (cons a b) env)
         (cons (svex-eval a env)
               (svexlist-eval b env)))
  :hints(("Goal" :in-theory (enable svexlist-eval))))


(defthm 4veclist-nth-of-cons
  (implies (syntaxp (quotep n))
           (equal (4veclist-nth n (cons a b))
                  (if (zp n)
                      (4vec-fix a)
                    (4veclist-nth (1- n) b))))
  :hints(("Goal" :in-theory (enable 4veclist-nth))))
