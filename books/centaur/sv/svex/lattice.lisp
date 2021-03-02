; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
(include-book "eval")
(include-book "xeval")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(define 4vec-[= ((a 4vec-p) (b 4vec-p))
  :returns approxp
  :parents (values)
  :short "Lattice relation (information order) on @(see 4vec) values."

  :long "<p>@('(4vec-[= a b)') is true when @('a') is a ``conservative
approximation'' of @('b').  That is, when every pair of corresponding bits,
@($a_i$) from @($a$) and @($b_i$) from @($b$), are the same unless @($a_i$) is
X.</p>

<p>Almost all @(see svex) @(see functions) satisfy a monotonicity property with
respect to this relation, i.e., if @('f') is a one-argument function, it will
satisfy:</p>

@({
    (implies (4vec-[= a b)
             (4vec-[= (f a) (f b)))
})

<p>Intuitively, this property essentially means that each operator properly
treats X bits as unknown.</p>

<p>A notable exception is the @('===') operator, i.e., @(see 4vec-===), which
is a ``bad'' operator that can non-conservatively treat X bits as being equal
to other X bits.  This operator is included in @(see sv) for better
compatibility with hardware description languages like Verilog, but should
generally be avoided when possible.</p>

<p>@('4vec-[=') is essentially a bitwise/vector analogue of the similar @(see
acl2::4v) function called @(see acl2::4v-<=); see also @(see
acl2::4v-monotonicity).</p>"
  (b* (((4vec a) a)
       ((4vec b) b))
    (eql -1 (logior
             ;; either a and b do not differ...
             (logand (logeqv a.upper b.upper)
                     (logeqv a.lower b.lower))
             ;; or a is X.
             (logand a.upper (lognot a.lower)))))
  ///
  (deffixequiv 4vec-[=)

  (defthm 4vec-[=-self
    (4vec-[= x x))

  (defthm 4vec-[=-x
    (4vec-[= (4vec-x) y))

  (defthmd 4vec-[=-transitive-1
    (implies (and (4vec-[= a b)
                  (4vec-[= b c))
             (4vec-[= a c))
    :hints ((bitops::logbitp-reasoning)))

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
           (bitops::logbitp-reasoning))))


(defsection 4vec-monotonicity
  :parents (4vec-[=)
  :short "Monotonicity properties for the basic @(see svex) @(see functions)."
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
                             ;acl2::bit-functions-type
                             bitops::logbitp-of-mask
                             acl2::bfix-when-not-1
                             bitops::logand-with-bitmask
                             bitops::logand-with-negated-bitmask
                             bitops::logbitp-of-negative-const
                             bitops::logbitp-of-const
                             BITOPS::LOGIOR-EQUAL-0
                             ;; Disabling NOT is REALLY important here!
                             not)))

  (local (in-theory (disable acl2::zip-open
                             acl2::zp-open
                             signed-byte-p
                             unsigned-byte-p
                             default-<-1
                             default-<-2
                             acl2::bfix-when-bitp
                             acl2::bfix-when-not-bitp
                             ACL2::BFIX-WHEN-NOT-BIT->BOOL
                             ACL2::BFIX-WHEN-BIT->BOOL
                             ACL2::NFIX-WHEN-NOT-NATP
                             acl2::natp-when-integerp
                             bit->bool
                             BITOPS::LOGBITP-OF-CONST-SPLIT
                             BITOPS::ASH-NATP-TYPE
                             BITOPS::LOGBITP-WHEN-BIT
                             (:e tau-system)

                             )))

  (local
   (progn
     (def-ruleset 4vec-mono-defs nil)

     (defun symbols-suffix-1 (x)
       (if (atom x)
           nil
         (cons (intern-in-package-of-symbol
                (concatenate 'string (symbol-name (car x)) "1")
                'sv::foo)
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
                      'sv::foo)))
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
                      (bitops::logbitp-reasoning
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
                            3vec-?*
                            3vec-==
                            4vec-onset
                            4vec-offset
                            4vec-rev-blocks
                            4vec-part-select
                            4vec-part-install
                            4vec-shift-core)))

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
  (def-4vec-monotonicity 4vec-countones)
  (def-4vec-monotonicity 4vec-onehot)
  (def-4vec-monotonicity 4vec-onehot0)
  (def-4vec-monotonicity 4vec-times)
  (def-4vec-monotonicity 4vec-quotient)
  (def-4vec-monotonicity 4vec-remainder)
  (def-4vec-monotonicity 4vec-<)
  (def-4vec-monotonicity 4vec-==)
  (def-4vec-monotonicity 4vec-?)
  (def-4vec-monotonicity 4vec-bit?)
  (def-4vec-monotonicity 4vec-?*)
  (def-4vec-monotonicity 4vec-bit-extract)
  (def-4vec-monotonicity 4vec-rev-blocks)
  (def-4vec-monotonicity 4vec-wildeq-safe)
  (def-4vec-monotonicity 4vec-symwildeq)
  (def-4vec-monotonicity 4vec-clog2)
  (def-4vec-monotonicity 4vec-pow)
  (def-4vec-monotonicity 4vec-part-select)
  (def-4vec-monotonicity 4vec-part-install)

  (local (in-theory (enable (:t logbitp)
                             bit->bool)))

  (defthm 4vec-==-[=-===
    (4vec-[= (4vec-== a b) (4vec-=== a b))
    :hints(("Goal" :in-theory (enable 4vec-=== 4vec-== 3vec-== 3vec-fix
                                      4vec-fix-is-4vec-of-fields))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-wildeq-safe-[=-wildeq
    (4vec-[= (4vec-wildeq-safe a b) (4vec-wildeq a b))
    :hints(("Goal" :in-theory (enable 4vec-wildeq 4vec-wildeq-safe
                                      4vec-fix-is-4vec-of-fields
                                      4vec-bitxor))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))))
  (defthm 4vec-wildeq-monotonic-when-second-const
    (implies (4vec-[= a b)
             (4vec-[= (4vec-wildeq a c)
                      (4vec-wildeq b c)))
    :hints(("Goal" :in-theory (enable 4vec-wildeq
                                      4vec-bitxor
                                      4vec-[=))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))))

  (defthm 4vec-bit?!-monotonic-on-nontest-args
    (implies (and (4vec-[= then1 then2)
                  (4vec-[= else1 else2))
             (4vec-[= (4vec-bit?! test then1 else1)
                      (4vec-bit?! test then2 else2)))
    :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-[=))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))))

  (defthm 4vec-bit?-[=-bit?!
    (4vec-[= (4vec-bit? test then else)
             (4vec-bit?! test then else))
    :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bit? 3vec-bit? 3vec-fix 4vec-[=))
           (bitops::logbitp-reasoning)
           (and stable-under-simplificationp
                '(:bdd (:vars nil)))
           )))

(defsection 4veclist-[=
  :parents (4vec-[= 4veclist)
  :short "Nth-wise lattice ordering for @(see 4veclist)s."

  (defquant 4veclist-[= (x y)
    (forall idx
            (4vec-[= (4veclist-nth-safe idx x)
                     (4veclist-nth-safe idx y)))
    :rewrite :direct)

  (in-theory (enable 4veclist-[=-necc))

  (defexample 4vec-alist-[=-example
    :pattern (4veclist-nth-safe idx x)
    :templates (idx)
    :instance-rulename 4veclist-[=-instancing)

  (deffixequiv 4veclist-[=
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
    :hints ((witness :ruleset 4veclist-[=-witnessing)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (4veclist-nth-safe)
                                   (4veclist-[=-necc))))
            (and stable-under-simplificationp
                 '(:use ((:instance 4veclist-[=-necc
                          (x b) (y (cdr c)) (idx (1- idx0)))
                         (:instance 4veclist-[=-necc
                          (x (cons a b)) (y c) (idx 0))
                         (:instance 4veclist-[=-necc
                          (x (cons a b)) (y c) (idx (+ 1 (nfix idx0))))))))))


(defsection svex-env-[=
  :parents (4vec-[= svex-env)
  :short "@(call svex-env-[=) checks whether an entire @(see svex-env)
conservatively approximates another: i.e., is every variable's value in @('x')
an approximation of its value in @('y')?"

  (defquant svex-env-[= (x y)
    (forall var
            (4vec-[= (svex-env-lookup var x)
                     (svex-env-lookup var y)))
    :rewrite :direct)

  (in-theory (enable svex-env-[=-necc))

  (defexample svex-env-[=-example
    :pattern (svex-env-lookup var x)
    :templates (var)
    :instance-rulename svex-env-[=-instancing)

  (deffixequiv svex-env-[=
    :args ((x svex-env) (y svex-env))
    :hints (("goal" :cases ((svex-env-[= x y)))
            (witness)))

  (defthm svex-env-[=-empty
    (svex-env-[= nil x)
    :hints ((witness))))


(defsection svex-apply-monotonocity
  :parents (svex-apply 4vec-[=)
  :short "@(see svex-apply) is almost always monotonic :-("

  

  (defthm svex-apply-monotonic
    (implies (and (4veclist-[= x y)
                  (not (eq (fnsym-fix fn) '===))
                  (or (not (eq (fnsym-fix fn) '==?))
                      (equal (4veclist-nth-safe 1 x) (4veclist-nth-safe 1 y)))
                  (or (not (eq (fnsym-fix fn) 'bit?!))
                      (equal (4veclist-nth-safe 0 x) (4veclist-nth-safe 0 y))))
             (4vec-[= (svex-apply fn x) (svex-apply fn y)))
    :hints(("Goal" :in-theory (e/d (svex-apply)
                                   (2vec-p 2vec->val))))))


(defund bit-n (n x)
  ;; This is just a function that secretly equals logbitp.  It exists so we can
  ;; rewrite logbitp to it in some bad cases and not have the rewriter loop.
  (logbitp n x))


(defsection svex-xeval-monotonicity
  :parents (svex-xeval 4vec-monotonicity)
  :short "@('(svex-xeval x)') always approximates @('(svex-eval x env)'), for
any environment."

  (defthm-svex-eval-flag
    (defthm svex-eval-gte-xeval
      (4vec-[= (svex-xeval x)
               (svex-eval x env))
      :hints ('(:expand ((svex-eval x env)
                         (svex-xeval x)))
              (and stable-under-simplificationp
                   (cond ((member-equal '(not (EQUAL (SVEX-CALL->FN$INLINE X) 'BIT?!)) clause)
                          '(:in-theory (e/d (svex-apply 4vec-[=-transitive-2)
                                            (4vec-bit?-[=-bit?!))
                            :use ((:instance 4vec-bit?-[=-bit?!
                                   (test (4veclist-nth-safe 0 (svexlist-eval (svex-call->args x) env)))
                                   (then (4veclist-nth-safe 1 (svexlist-eval (svex-call->args x) env)))
                                   (else (4veclist-nth-safe 2 (svexlist-eval (svex-call->args x) env)))))))
                         (t
                          '(:in-theory (e/d (svex-apply 4vec-[=-transitive-2)
                                            (4vec-==-[=-===
                                             4vec-wildeq-safe-[=-wildeq))
                            :use ((:instance 4vec-==-[=-===
                                   (a (4veclist-nth-safe 0 (svexlist-eval (svex-call->args x) env)))
                                   (b (4veclist-nth-safe 1 (svexlist-eval (svex-call->args x) env))))
                                  (:instance 4vec-wildeq-safe-[=-wildeq
                                   (a (4veclist-nth-safe 0 (svexlist-eval (svex-call->args x) env)))
                                   (b (4veclist-nth-safe 1 (svexlist-eval (svex-call->args x) env)))))
                            :do-not-induct t)))))
      :flag expr)
    (defthm svexlist-eval-gte-xeval
      (4veclist-[= (svexlist-xeval x)
                   (svexlist-eval x env))
      :hints ('(:expand ((svexlist-eval x env)
                         (svexlist-xeval x))))
      :flag list))

  "<p>Accordingly, we can often use @(see svex-xeval) in place of @(see
  svex-eval).</p>"

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
                     (bitops::logbitp-reasoning)
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
                         (if (bit->bool
                              (b-ior (b-not (logbit n (4vec->upper (svex-xeval b))))
                                     (logbit n (4vec->lower (svex-xeval b)))))
                             (logbitp n (4vec->upper (svex-xeval b)))
                           (bit-n n (4vec->upper (svex-eval b env)))))
                  (equal (logbitp n (4vec->lower (svex-eval b env)))
                         (if (bit->bool
                              (b-ior (b-not (logbit n (4vec->upper (svex-xeval b))))
                                     (logbit n (4vec->lower (svex-xeval b)))))
                             (logbitp n (4vec->lower (svex-xeval b)))
                           (bit-n n (4vec->lower (svex-eval b env)))))))
    :hints(("Goal" :in-theory (enable bit-n logbitp-when-4vec-[=-svex-eval b-ior)))))



(defsection 4vec-xfree-p-basics
  :parents (4vec-xfree-p)
  :short "Some lemmas about @(see 4vec-xfree-p) in the
  @('sv/svex/lattice.lisp') book."

  (local (in-theory (enable 4vec-xfree-p)))

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
             :in-theory (e/d (4vec-equiv)
                             (svex-eval-gte-xeval))
             :expand ((4vec-[= (svex-xeval n) (svex-eval n env))))
            (bitops::logbitp-reasoning)))

  (defthmd svex-eval-when-4vec-xfree-of-minval-apply
    (implies (and (syntaxp (not (equal env ''nil)))
                  (not (eq (fnsym-fix fn) '===))
                  (not (eq (fnsym-fix fn) '==?))
                  (not (eq (fnsym-fix fn) 'bit?!))
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
             :expand ((svex-xeval (svex-call '=== args))))))

  (defthmd svex-eval-when-4vec-xfree-of-minval-apply-==?
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-p (svex-apply 'safer-==? (svexlist-xeval args))))
             (equal (svex-apply '==? (svexlist-eval args env))
                    (svex-apply 'safer-==? (svexlist-xeval args))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-of-minval
                           (n (svex-call '==? args))))
             :in-theory (disable svex-eval-when-4vec-xfree-of-minval
                                 equal-of-4vecs 4vec-xfree-p)
             :expand ((svex-xeval (svex-call '==? args))))))

  (defthmd svex-eval-when-4vec-xfree-of-minval-apply-bit?!
    (implies (and (syntaxp (not (equal env ''nil)))
                  (4vec-xfree-p (svex-apply 'bit? (svexlist-xeval args))))
             (equal (svex-apply 'bit?! (svexlist-eval args env))
                    (svex-apply 'bit? (svexlist-xeval args))))
    :hints (("goal" :use ((:instance svex-eval-when-4vec-xfree-of-minval
                           (n (svex-call 'bit?! args))))
             :in-theory (disable svex-eval-when-4vec-xfree-of-minval
                                 equal-of-4vecs 4vec-xfree-p)
             :expand ((svex-xeval (svex-call 'bit?! args)))))))



(defines svex-monotonic-p
  (define svex-monotonic-p ((x svex-p))
    :measure (svex-count x)
    :hints ((and stable-under-simplificationp '(:expand ((svex-count x)))))
    :returns (monotonicp)
    :verify-guards nil
    (svex-case x
      :var t
      :quote t
      :call (and (or (and (not (eq x.fn '===))
                          (or (not (eq x.fn 'bit?!))
                              (b* ((test (nth 0 x.args)))
                                (or (not test)
                                    (svex-case test :quote))))
                          (or (not (eq x.fn '==?))
                              (b* ((b (nth 1 x.args)))
                                (or (not b)
                                    (svex-case b :quote)))))
                     (cw "Nonmonotonic operator: ~x0~%" x))
                 (svexlist-monotonic-p x.args))))
  (define svexlist-monotonic-p ((x svexlist-p))
    :measure (svexlist-count x)
    :returns (monotonicp)
    (if (Atom x)
        t
      (and (svex-monotonic-p (car x))
           (svexlist-monotonic-p (cdr x)))))
  ///

  (defthm-svex-monotonic-p-flag
    (defthm svex-eval-monontonic-when-svex-monotonic
      (implies (and (svex-env-[= env1 env2)
                    (svex-monotonic-p x))
               (4vec-[= (svex-eval x env1) (svex-eval x env2)))
      :hints ('(:expand ((svex-monotonic-p x)
                         (:free (env) (svex-eval x env))))
              (and stable-under-simplificationp
                   '(:expand ((nth 1 (svex-call->args x))
                              (:free (env) (svexlist-eval (svex-call->args x) env))))))
      :flag svex-monotonic-p)

    (defthm svexlist-eval-monontonic-when-svexlist-monotonic
      (implies (and (svex-env-[= env1 env2)
                    (svexlist-monotonic-p x))
               (4veclist-[= (svexlist-eval x env1) (svexlist-eval x env2)))
      :hints ('(:expand ((svexlist-monotonic-p x)
                         (:free (env) (svexlist-eval x env)))))
      :flag svexlist-monotonic-p))

  (verify-guards svex-monotonic-p
    :hints(("Goal" :expand ((nth 1 (svex-call->args x))))))

  (memoize 'svex-monotonic-p :condition '(svex-case x :call)))
