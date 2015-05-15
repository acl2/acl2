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
(include-book "evaluator")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "bits"))

(defxdoc lattice.lisp :parents (4vec-[=))
(local (xdoc::set-default-parents lattice.lisp))

(define 4vec-[= ((a 4vec-p) (b 4vec-p))
  :parents (4vec)
  :short "Lattice relation (information order) on 4vecs."
  :long "<p>@('(4vec-[= a b)') is true iff on every bit where @('a') and @('b')
differ, @('a')'s is X.</p>

<p>All 4vec functions in the svex language satisfy a monotonicity property wrt
this relation, i.e.:</p>

@({
 (implies (4vec-[= a b)
          (4vec-[= (f a) (f b)))
 })
"
  (b* (((4vec a) a)
       ((4vec b) b))
    (eql -1 (logior
             ;; either a and b do not differ...
             (logand (logeqv a.upper b.upper)
                     (logeqv a.lower b.lower))
             ;; or a is X.
             (logand a.upper (lognot a.lower)))))
  ///
  (fty::deffixequiv 4vec-[=)

  (defthm 4vec-[=-self
    (4vec-[= x x))

  (defthm 4vec-[=-x
    (4vec-[= (4vec-x) y))

  (defthmd 4vec-[=-transitive-1
    (implies (and (4vec-[= a b)
                  (4vec-[= b c))
             (4vec-[= a c))
    :hints ((acl2::logbitp-reasoning)))

  (defthmd 4vec-[=-transitive-2
    (implies (and (4vec-[= b c)
                  (4vec-[= a b))
             (4vec-[= a c))
    :hints(("Goal" :in-theory (e/d (4vec-[=-transitive-1) (4vec-[=)))))

  (local (defthm equal-of-4vec-fix
           (equal (equal (4vec-fix x) y)
                  (and (4vec-p y)
                       (equal (4vec->upper x) (4vec->upper y))
                       (equal (4vec->lower x) (4vec->lower y))))
           :hints(("Goal" :in-theory (enable 4vec-fix 4vec-p
                                             4vec->upper 4vec->lower)))))

  (defthm 4vec-[=-2vec
    (implies (2vec-p n)
             (equal (4vec-[= n n1)
                    (4vec-equiv n n1)))
    :hints(("goal" :in-theory (enable 4vec-equiv))
           (acl2::logbitp-reasoning))))




(defsection 4vec-monotonicity
  (set-state-ok t)
  (local (in-theory (disable bitops::logior-natp-type
                             bitops::logior-<-0-linear-2
                             bitops::logand-natp-type-2
                             bitops::logand->=-0-linear-2
                             bitops::upper-bound-of-logand
                             bitops::lognot-negp
                             bitops::lognot-<-const
                             bitops::logxor-natp-type-2
                             bitops::logior->=-0-linear
                             bitops::logior-<-0-linear-1
                             bitops::lognot-natp
                             BITOPS::LOGAND->=-0-LINEAR-1
                             BITOPS::LOGAND-<-0-LINEAR
                             BITOPS::UPPER-BOUND-OF-LOGAND
                             acl2::IFIX-WHEN-NOT-INTEGERP
                             bitops::logbitp-when-bitmaskp
                             bitops::logbitp-nonzero-of-bit
                             3vec-p-implies-bits
                             DEFAULT-<-1
                             BITOPS::LOGXOR-NATP-TYPE-1
                             BITOPS::LOGAND-NATP-TYPE-1
                             ;; 4VEC->LOWER-WHEN-2VEC-P
                             BITOPS::LOGBITP-WHEN-BIT
                             2VEC-P$INLINE
                             (:t logbitp)
                             acl2::bit-functions-type
                             bitops::logbitp-of-mask
                             acl2::bfix-when-not-1
                             bitops::logand-with-bitmask
                             bitops::logand-with-negated-bitmask
                             bitops::logbitp-of-negative-const
                             bitops::logbitp-of-const
                             ;; Disabling NOT is REALLY important here!
                             not)))



  (local
   (progn
     (def-ruleset 4vec-mono-defs nil)

     (defun symbols-suffix-1 (x)
       (if (atom x)
           nil
         (cons (intern-in-package-of-symbol
                (concatenate 'string (symbol-name (car x)) "1")
                'svex::foo)
               (symbols-suffix-1 (cdr x)))))

     (defun formals-[= (formals formals1)
       (if (atom formals)
           nil
         (cons `(4vec-[= ,(car formals) ,(car formals1))
               (formals-[= (cdr formals) (cdr formals1)))))

     (defun def-4vec-monotonicity-fn (fn state)
       (b* ((realfn (or (cdr (assoc fn (macro-aliases (w state)))) fn))
            (formals (getprop realfn 'acl2::formals :none 'current-acl2-world (w state)))
            ((when (eq formals :none))
             (er hard? 'def-4vec-monotonicity "not defined: ~x0" fn))
            (formals1 (symbols-suffix-1 formals))
            (thmname (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name fn) "-MONOTONIC")
                      'svex::foo)))
         `(progn
            (defthm ,thmname
              (implies (and . ,(formals-[= formals formals1))
                       (4vec-[= (,fn . ,formals)
                                (,fn . ,formals1)))
              :hints (("goal" :in-theory (enable ,fn))
                      (and stable-under-simplificationp
                           '(:in-theory (enable* 4vec-[=
                                                 4vec-mono-defs
                                                 bool->bit)))
                      (acl2::logbitp-reasoning
                       :prune-examples nil
                       :add-hints (:in-theory (enable* acl2::logbitp-case-splits)))
                      (and stable-under-simplificationp
                           '(:bdd (:vars nil) :in-theory (enable bool->bit)))))
            (local (add-to-ruleset 4vec-mono-defs ,fn)))))))

  (defmacro def-4vec-monotonicity (fn)
    `(make-event (def-4vec-monotonicity-fn ',fn state)))

  (local (in-theory (enable 4vec-bit-index bool->vec
                            3vec-bitnot
                            3vec-bitand
                            3vec-bitor
                            3vec-bitxor
                            3vec-reduction-or
                            3vec-reduction-and
                            3vec-?
                            3vec-bit?
                            3vec-==
                            4vec-onset
                            4vec-offset
                            4vec-rev-blocks)))

  (def-4vec-monotonicity 4vec-fix)
  (def-4vec-monotonicity 3vec-fix)
  ;; (def-4vec-monotonicity 3vec-bitnot)
  (def-4vec-monotonicity 4vec-bitnot)
  (def-4vec-monotonicity 4vec-onset)
  (def-4vec-monotonicity 4vec-offset)
  ;; (def-4vec-monotonicity 3vec-bitand)
  (def-4vec-monotonicity 4vec-bitand)
  ;; (def-4vec-monotonicity 3vec-bitor)
  (def-4vec-monotonicity 4vec-bitor)
  (def-4vec-monotonicity 4vec-bitxor)
  (def-4vec-monotonicity 4vec-res)
  (def-4vec-monotonicity 4vec-resand)
  (def-4vec-monotonicity 4vec-resor)
  (def-4vec-monotonicity 4vec-override)
  ;; (def-4vec-monotonicity 3vec-reduction-and)
  (def-4vec-monotonicity 4vec-reduction-and)
  ;; (def-4vec-monotonicity 3vec-reduction-or)
  (def-4vec-monotonicity 4vec-reduction-or)
  (def-4vec-monotonicity 4vec-zero-ext)
  (def-4vec-monotonicity 4vec-sign-ext)
  (def-4vec-monotonicity 2vecx-fix)
  (def-4vec-monotonicity 2vecnatx-fix)
  (def-4vec-monotonicity 4vec-concat)
  (def-4vec-monotonicity 4vec-rsh)
  (def-4vec-monotonicity 4vec-lsh)
  (def-4vec-monotonicity 4vec-parity)
  (def-4vec-monotonicity 4vec-plus)
  (def-4vec-monotonicity 4vec-minus)
  (def-4vec-monotonicity 4vec-uminus)
  (def-4vec-monotonicity 4vec-xdet)
  (def-4vec-monotonicity 4vec-times)
  (def-4vec-monotonicity 4vec-quotient)
  (def-4vec-monotonicity 4vec-remainder)
  (def-4vec-monotonicity 4vec-<)
  (def-4vec-monotonicity 4vec-==)
  (def-4vec-monotonicity 4vec-?)
  (def-4vec-monotonicity 4vec-bit?)
  (def-4vec-monotonicity 4vec-bit-extract)
  (def-4vec-monotonicity 4vec-rev-blocks)
  (def-4vec-monotonicity 4vec-wildeq)
  (def-4vec-monotonicity 4vec-symwildeq)
  (def-4vec-monotonicity 4vec-clog2)

  ;; (local (defthm equal-of-booleans
  ;;          (implies (and (booleanp a) (booleanp b))
  ;;                   (equal (equal a b) (iff a b)))))
  (local (defthm booleanp-of-logbitp
           (booleanp (logbitp n a))
           :rule-classes :type-prescription))

  (defthm 4vec-==-[=-===
    (4vec-[= (4vec-== a b) (4vec-=== a b))
    :hints(("Goal" :in-theory (enable 4vec-=== 4vec-== 3vec-== 3vec-fix
                                      4vec-fix-is-4vec-of-fields))
           (acl2::logbitp-reasoning))))

(defsection 4veclist-[=
  (acl2::defquant 4veclist-[= (x y)
    (forall idx
            (4vec-[= (4veclist-nth idx x)
                     (4veclist-nth idx y)))
    :rewrite :direct)

  (in-theory (enable 4veclist-[=-necc))

  (acl2::defexample 4vec-alist-[=-example
    :pattern (4veclist-nth idx x)
    :templates (idx)
    :instance-rulename 4veclist-[=-instancing)

  (fty::deffixequiv 4veclist-[=
    :args ((x 4veclist) (y 4veclist))
    :hints (("goal" :cases ((4veclist-[= x y)))
            (acl2::witness)))

  (defthm 4veclist-[=-empty
    (4veclist-[= nil x)
    :hints ((acl2::witness)))

  (defthm 4veclist-[=-of-cons
    (iff (4veclist-[= (cons a b) c)
         (and (4vec-[= a (car c))
              (4veclist-[= b (cdr c))))
    :hints ((acl2::witness :ruleset 4veclist-[=-witnessing)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (4veclist-nth)
                                   (4veclist-[=-necc))))
            (and stable-under-simplificationp
                 '(:use ((:instance 4veclist-[=-necc
                          (x b) (y (cdr c)) (idx (1- idx0)))
                         (:instance 4veclist-[=-necc
                          (x (cons a b)) (y c) (idx 0))
                         (:instance 4veclist-[=-necc
                          (x (cons a b)) (y c) (idx (+ 1 (nfix idx0))))))))))

(defsection svex-env-[=

  (acl2::defquant svex-env-[= (x y)
    (forall var
            (4vec-[= (svex-env-lookup var x)
                     (svex-env-lookup var y)))
    :rewrite :direct)

  (in-theory (enable svex-env-[=-necc))

  (acl2::defexample svex-env-[=-example
    :pattern (svex-env-lookup var x)
    :templates (var)
    :instance-rulename svex-env-[=-instancing)

  (fty::deffixequiv svex-env-[=
    :args ((x svex-env) (y svex-env))
    :hints (("goal" :cases ((svex-env-[= x y)))
            (acl2::witness)))

  (defthm svex-env-[=-empty
    (svex-env-[= nil x)
    :hints ((acl2::witness))))

(defthm svex-apply-monotonic
  (implies (and (4veclist-[= x y)
                (not (eq (fnsym-fix fn) '===)))
           (4vec-[= (svex-apply fn x) (svex-apply fn y)))
  :hints(("Goal" :in-theory (e/d (svex-apply) (2vec-p 2vec->val)))))


(defthm-svex-eval-flag
  (defthm svex-eval-gte-xeval
    (4vec-[= (svex-xeval x) (svex-eval x env))
    :hints ('(:expand ((svex-eval x env)
                       (svex-xeval x)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-apply 4vec-[=-transitive-2)
                                   (4vec-==-[=-===))
                   :use ((:instance 4vec-==-[=-===
                          (a (4veclist-nth 0 (svexlist-eval (svex-call->args x) env)))
                          (b (4veclist-nth 1 (svexlist-eval (svex-call->args x) env)))))
                   :do-not-induct t)))
    :flag expr)
  (defthm svexlist-eval-gte-xeval
    (4veclist-[= (svexlist-xeval x) (svexlist-eval x env))
  :hints ('(:expand ((svexlist-eval x env)
                     (svexlist-xeval x))))
    :flag list))

(defthmd svex-eval-when-2vec-p-of-minval
  (implies (and (syntaxp (not (equal env ''nil)))
                (2vec-p (svex-xeval n)))
           (equal (svex-eval n env)
                  (svex-xeval n)))
  :hints (("goal" :use ((:instance svex-eval-gte-xeval (x n)))
           :in-theory (e/d ( 4vec-equiv)
                           (svex-eval-gte-xeval))
           :expand ((4vec-[= (svex-xeval n) (svex-eval n env)))))
  :otf-flg t)


(defund bit-n (n x)
  (logbitp n x))

(local
 (encapsulate nil
   (local (defthmd logbitp-when-4vec-[=
            (implies (and (4vec-[= a b)
                          (or (not (logbitp n (4vec->upper a)))
                              (logbitp n (4vec->lower a))))
                     (and (equal (logbitp n (4vec->upper b))
                                 (logbitp n (4vec->upper a)))
                          (equal (logbitp n (4vec->lower b))
                                 (logbitp n (4vec->lower a)))))
            :hints(("Goal" :in-theory (e/d (4vec-[=) (not)))
                   '(:cases ((logbitp n (4vec->upper b))))
                   '(:cases ((logbitp n (4vec->lower b))))
                   (acl2::logbitp-reasoning)
                   (and stable-under-simplificationp
                        '(:in-theory (enable bool->bit))))))
   (defthmd logbitp-when-4vec-[=-svex-eval
     (implies (and (syntaxp (not (equal env ''nil)))
                   (or (not (logbitp n (4vec->upper (svex-xeval b))))
                       (logbitp n (4vec->lower (svex-xeval b)))))
              (and (equal (logbitp n (4vec->upper (svex-eval b env)))
                          (logbitp n (4vec->upper (svex-xeval b))))
                   (equal (logbitp n (4vec->lower (svex-eval b env)))
                          (logbitp n (4vec->lower (svex-xeval b))))))
     :hints(("Goal" :use ((:instance logbitp-when-4vec-[=
                           (b (svex-eval b env))
                           (a (svex-xeval b)))))))))


(defthmd logbitp-when-4vec-[=-svex-eval-strong
  (implies (syntaxp (not (equal env ''nil)))
           (and (equal (logbitp n (4vec->upper (svex-eval b env)))
                       (if (acl2::bit->bool
                            (acl2::b-ior (acl2::b-not (acl2::logbit n (4vec->upper (svex-xeval b))))
                                         (acl2::logbit n (4vec->lower (svex-xeval b)))))
                           (logbitp n (4vec->upper (svex-xeval b)))
                         (bit-n n (4vec->upper (svex-eval b env)))))
                (equal (logbitp n (4vec->lower (svex-eval b env)))
                       (if (acl2::bit->bool
                            (acl2::b-ior (acl2::b-not (acl2::logbit n (4vec->upper (svex-xeval b))))
                                         (acl2::logbit n (4vec->lower (svex-xeval b)))))
                           (logbitp n (4vec->lower (svex-xeval b)))
                         (bit-n n (4vec->lower (svex-eval b env)))))))
  :hints(("Goal" :in-theory (enable bit-n logbitp-when-4vec-[=-svex-eval acl2::b-ior))))



(define 4vec-xfree-p ((x 4vec-p))
  (b* (((4vec x) x))
    (eql -1 (logior (lognot x.upper) x.lower)))
  ///
  (local (defthm equal-of-4vecs
           (implies (and (4vec-p a)
                         (4vec-p b))
                    (equal (equal a b)
                           (and (equal (4vec->upper a) (4vec->upper b))
                                (equal (4vec->lower a) (4vec->lower b)))))))

  (defthmd svex-eval-when-4vec-xfree-of-minval
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-p (svex-xeval n)))
             (equal (svex-eval n env)
                    (svex-xeval n)))
    :hints (("goal" :use ((:instance svex-eval-gte-xeval (x n)))
             :in-theory (e/d ( 4vec-equiv)
                             (svex-eval-gte-xeval))
             :expand ((4vec-[= (svex-xeval n) (svex-eval n env))))
            (bitops::logbitp-reasoning)))
  
  (defthmd svex-eval-when-4vec-xfree-of-minval-apply
    (implies (and (syntaxp (not (equal env ''nil)))
                  (not (eq (fnsym-fix fn) '===))
                  (4vec-xfree-p (svex-apply fn (svexlist-xeval args))))
             (equal (svex-apply fn (svexlist-eval args env))
                    (svex-apply fn (svexlist-xeval args))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-of-minval
                           (n (svex-call fn args))))
             :in-theory (disable svex-eval-when-4vec-xfree-of-minval
                                 equal-of-4vecs 4vec-xfree-p)
             :expand ((svex-xeval (svex-call fn args))))))

  (defthmd svex-eval-when-4vec-xfree-of-minval-apply-===
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-p (svex-apply '== (svexlist-xeval args))))
             (equal (svex-apply '=== (svexlist-eval args env))
                    (svex-apply '== (svexlist-xeval args))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-of-minval
                           (n (svex-call '=== args))))
             :in-theory (disable svex-eval-when-4vec-xfree-of-minval
                                 equal-of-4vecs 4vec-xfree-p)
             :expand ((svex-xeval (svex-call '=== args)))))))
