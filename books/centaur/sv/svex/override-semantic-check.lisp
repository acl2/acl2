; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "override-transparency")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/alist-thms"))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (std::add-default-post-define-hook :fix))
;; The theorem we want is similar to
;; eval-when-muxes-agree-and-svexlist-check-overridetriples (in
;; fsm-overrides.lisp).

;; I.e., we want some easy-to-check condition that if true, and
;;  - (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
;;  - (svex-envs-agree-except override-vars override-env spec-env)
;;  - (svex-env-muxtests-subsetp test-vars spec-env override-env)

;; then the evaluation of our list of svexes (x) under spec-env and override-env are equal.

;; We want to formulate this as an equivalence check between two lists of
;; svexes.  Suppose the original x represents the evaluation with spec-env.
;; We'll try and formulate a composition of x with some substitution such that
;; the result can represent any evaluation with an override-env satisfying the
;; criteria above.

;; - (svex-envs-agree-except override-vars override-env spec-env) means that we
;; can only replace the override-test and override-value vars from our triples.
;; So our substitution's domain will be those override-test/override-value
;; vars.

;;  - (svex-env-muxtests-subsetp test-vars spec-env override-env) means for
;;  each test var, the binding in override-env is a superset of that in
;;  spec-env.  So we'll replace each test-var with an OR of that test var and a
;;  new variable test-var2. The condition under which override-env overrides a
;;  bit and spec-env doesn't is test-var2 & ~test-var.

;;  - (svar-override-triplelist-muxes-agree svar-triples override-env spec-env
;; spec-values) (assuming also the muxtests-subsetp condition) says that the
;; override values of bits overridden in both spec-env and override-env match,
;; and the override values in override-env of bits overridden there but not in
;; spec-env match the reference values.  This gives us a binding for a given
;; override-val var: if the corresponding test-var2 & ~test-var, then
;; spec-ref-val, else spec-override-val.




(define svar-prime ((x svar-p))
  :returns (new-x svar-p)
  (b* (((svar x)))
    (change-svar x :bits (logior 4 x.bits)))
  ///

  (local (defthm logior-4-equal-when-loghead-3-equal
           (implies (and (equal (loghead 3 x) head)
                         (equal (loghead 3 y) head2)
                         (not (logbitp 2 head))
                         (not (logbitp 2 head2)))
                    (equal (equal (logior 4 x) (logior 4 y))
                           (Equal (ifix x) (ifix y))))
           :hints ((logbitp-reasoning
                    :add-hints (:in-theory (enable bool->bit))))))
  
  (defthm svar-prime-unique-when-svar-override-okp
    (implies (and (svar-override-okp x)
                  (svar-override-okp y))
             (equal (equal (svar-prime x) (svar-prime y))
                    (svar-equiv x y)))
    :hints(("Goal" :in-theory (enable svar-override-okp svar-override-p
                                      svar-fix-redef))))

  (local (defthm logior-4-equal-x-when-loghead-3
           (implies (and (equal (loghead 3 x) head)
                         (not (logbitp 2 head)))
                    (not (equal (logior 4 x) x)))
           :hints ((logbitp-reasoning
                    :add-hints (:in-theory (enable bool->bit))))))

  (local (defthm logior-4-equal
           (implies (not (logbitp 2 y))
                    (not (equal (logior 4 x) y)))
           :hints ((logbitp-reasoning))))

  (defthm svar-prime-not-override-okp
    (not (svar-override-okp (svar-prime x)))
    :hints(("Goal" :in-theory (enable svar-override-okp
                                      svar-override-p))))
  
  (defthm svar-prime-not-equal-when-override-okp
    (implies (svar-override-okp y)
             (not (equal (svar-prime x) y)))
    :hints(("Goal" :in-theory (disable svar-prime))))

  (defthm svar-prime-not-member-when-svarlist-override-okp
    (implies (svarlist-override-okp vars)
             (not (member-equal (svar-prime x) vars)))
    :hints(("Goal" :in-theory (e/d (svarlist-override-okp)
                                   (svar-prime))))))


(define svar-unprime ((x svar-p))
  :returns (new-x svar-p)
  (b* (((svar x)))
    (change-svar x :bits (logandc1 4 x.bits)))
  ///
  (defthm svar-unprime-of-svar-prime
    (equal (svar-unprime (svar-prime x))
           (svar-unprime x))
    :hints(("Goal" :in-theory (enable svar-prime))
           (bitops::logbitp-reasoning)))

  (defthm svar-prime-of-svar-unprime
    (equal (svar-prime (svar-unprime x))
           (svar-prime x))
    :hints(("Goal" :in-theory (enable svar-prime))
           (bitops::logbitp-reasoning)))
    

  (defthm svar-unprime-when-override-okp
    (implies (svar-override-okp x)
             (equal (svar-unprime x) (svar-fix x)))
    :hints(("Goal" :in-theory (enable svar-override-okp
                                      svar-override-p))
           (bitops::logbitp-reasoning))))

(define svarlist-prime ((x svarlist-p))
  :returns (new-x svarlist-p)
  (if (atom x)
      nil
    (cons (svar-prime (car x))
          (svarlist-prime (cdr x))))
  ///
  (defthm svar-prime-member-equal-svarlist-prime
    (implies (and (svar-override-okp x)
                  (svarlist-override-okp y))
             (iff (member-equal (svar-prime x) (svarlist-prime y))
                  (member-equal (svar-fix x) (svarlist-fix y))))
    :hints(("Goal" :in-theory (enable svarlist-fix
                                      svarlist-override-okp))))

  (defthm svarlist-prime-not-intersect-when-svarlist-override-okp
    (implies (svarlist-override-okp vars)
             (and (not (intersectp-equal (svarlist-prime x) vars))
                  (not (intersectp-equal vars (svarlist-prime x)))))))


(local
  (defcong set-equiv equal (svarlist-override-okp x) 1
    :hints (("goal" :use ((:instance (:functional-instance acl2::element-list-p-set-equiv-congruence
                                      (acl2::element-p (lambda (x) (svar-override-okp x)))
                                      (acl2::element-list-final-cdr-p (lambda (x) t))
                                      (acl2::element-list-p (lambda (x) (svarlist-override-okp x))))
                           (x x) (y x-equiv)))
             :in-theory (enable svarlist-override-okp)))))







(define svar-overridekey-semantic-check-subst ((x svar-p)
                                               (values svex-alist-p))
  :returns (subst svex-alist-p)
  ;; Returns the substitution to apply to the original list of svexes, to
  ;; create the new ones to be equivalence checked against them.  Two new
  ;; variables are used: the svar-primes of the testvar and the valvar.
  ;; The former indicates whether the testvar is set in the override-env
  ;; in the case where it's not set in the spec-env.  The latter indicates the
  ;; value of the valvar in the override-env when it's not relevant because
  ;; it's not overridden.
  (b* ((x.testvar (svar-change-override x :test))
       (x.valvar  (svar-change-override x :val))
       (refvar (svar-change-override x nil))
       (x.valexpr (or (svex-lookup refvar values) (svex-x)))
       (new-test-var (svar-prime x.testvar))
       (test-expr (svcall bit?! (svex-var x.testvar) -1 (svex-var new-test-var)))
       (val-expr (svcall bit?!
                         (svex-var x.testvar)
                         (svex-var x.valvar)
                         (svcall bit?!
                                 (svex-var new-test-var)
                                 x.valexpr
                                 (svex-var (svar-prime x.valvar))))))
    (list (cons x.testvar test-expr)
          (cons x.valvar val-expr)))
  ///
  (defret keys-of-<fn>
    (equal (svex-alist-keys subst)
           (list (svar-change-override x :test)
                 (svar-change-override x :val)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defret vars-of-<fn>
    (implies (and (not (equal v (svar-change-override x :test)))
                  (not (equal v (svar-change-override x :val)))
                  (not (equal v (svar-prime (svar-change-override x :test))))
                  (not (equal v (svar-prime (svar-change-override x :val))))
                  (not (member-equal v (svex-vars (svex-lookup (svar-change-override x nil) values)))))
             (not (member-equal v (svex-alist-vars subst))))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (defretd lookup-of-<fn>
    (equal (svex-lookup v subst)
           (b* ((x.testvar (svar-change-override x :test))
                (x.valvar  (svar-change-override x :val))
                (refvar (svar-change-override x nil))
                (x.valexpr (or (svex-lookup refvar values) (svex-x)))
                (new-test-var (svar-prime x.testvar))
                (test-expr (svcall bit?! (svex-var x.testvar) -1 (svex-var new-test-var)))
                (val-expr (svcall bit?!
                                  (svex-var x.testvar)
                                  (svex-var x.valvar)
                                  (svcall bit?!
                                          (svex-var new-test-var)
                                          x.valexpr
                                          (svex-var (svar-prime x.valvar))))))
             (cond ((svar-equiv v x.testvar) test-expr)
                   ((svar-equiv v x.valvar) val-expr)
                   (t nil))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret <fn>-of-svar-change-override
    (equal (let ((x (svar-change-override x type))) <call>)
           subst)))




(local (defthm logite-of-bitmux-same-test
         (equal (logite test (logite test x y) z)
                (logite test x z))
         :hints ((logbitp-reasoning :add-hints (:in-theory (enable bool->bit))))))

(local (defthm 4vec-bitmux-of-bitmux-same-test
         (equal (4vec-bitmux test (4vec-bitmux test x y) z)
                (4vec-bitmux test x z))
         :hints(("Goal" :in-theory (enable 4vec-bitmux)))))


(local (defthm logite-of-else-bitmux-same-test
         (equal (logite test x (logite test y z))
                (logite test x z))
         :hints ((logbitp-reasoning :add-hints (:in-theory (enable bool->bit))))))

(local (defthm 4vec-bitmux-else-bitmux-same-test
         (equal (4vec-bitmux test x (4vec-bitmux test y z))
                (4vec-bitmux test x z))
         :hints(("Goal" :in-theory (enable 4vec-bitmux)))))


(local (defthm 4vec-bitmux-subset-then-neg1-else-x-equal-x
         (implies (4vec-muxtest-subsetp a b)
                  (equal (4vec-bitmux (4vec-1mask a) -1 b)
                         (4vec-fix b)))
         :hints(("Goal" :in-theory (enable 4vec-muxtest-subsetp
                                           4vec-bitmux)
                 :expand ((4vec-1mask b)))
                (logbitp-reasoning))))


(local (defthm logite-equal-implies-logite-of-logite-equal
         (implies (and (equal (logite override-test
                                      override-val
                                      (logite spec-test
                                              spec-val
                                              ref-val))
                              (logite spec-test spec-val ref-val))
                       (equal (logandc2 spec-test override-test) 0))
                  (equal (logite spec-test
                                 spec-val
                                 (logite override-test
                                         ref-val
                                         override-val))
                         (ifix override-val)))
         :hints ((logbitp-reasoning))))

(local (defthm 4vec-bitmux-equal-implies-bitmyx-of-bitmux-equal
         (implies (and (equal (4vec-bitmux (4vec-1mask override-test)
                                           override-val
                                           (4vec-bitmux (4vec-1mask spec-test)
                                                        spec-val
                                                        ref-val))
                              (4vec-bitmux (4vec-1mask spec-test) spec-val ref-val))
                       (4vec-muxtest-subsetp spec-test override-test))
                  (equal (4vec-bitmux (4vec-1mask spec-test)
                                      spec-val
                                      (4vec-bitmux (4vec-1mask override-test)
                                                   ref-val
                                                   override-val))
                         (4vec-fix override-val)))
         :hints(("Goal" :in-theory (enable 4vec-bitmux 4vec-muxtest-subsetp)))))




(local (defthm svex-vars-override-okp-of-lookup
         (implies (svarlist-override-okp (svex-alist-vars x))
                  (svarlist-override-okp (svex-vars (svex-lookup k x))))
         :hints(("Goal" :in-theory (enable svex-alist-vars svex-lookup)))))



(local (defthm equal-of-logapp
         (equal (equal (logapp n x y) z)
                (and (integerp z)
                     (equal (loghead n x) (loghead n z))
                     (equal (ifix y) (logtail n z))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(defthm equal-of-svar-change-overrides
  (equal (equal (svar-change-override x type1)
                (svar-change-override x type2))
         (svar-overridetype-equiv type1 type2))
  :hints(("Goal" :in-theory (enable svar-change-override
                                    svar-overridetype-fix-possibilities))))

(define svar-overridekey-semantic-check-subst-env ((x svar-p)
                                                   (override-env svex-env-p))
  :returns (env svex-env-p)
  ;; makes an env under which if you evaluate the semantic-check-subst above,
  ;; its values match those of override-env provided the conditions relating
  ;; override-env and spec-env hold.

  ;; actually the env needs to include spec-env as well; this env only includes
  ;; the additional variables that weren't in x to begin with.
  (b* ((x.testvar (svar-change-override x :test))
       (x.valvar  (svar-change-override x :val)))
    (list (cons (svar-prime x.testvar)
                (svex-env-lookup x.testvar override-env))
          (cons (svar-prime x.valvar)
                (svex-env-lookup x.valvar override-env))))
  ///

  (local (defthm svex-env-extract-override-okp-of-cons-prime
           (implies (svarlist-override-okp vars)
                    (equal (svex-env-extract vars (cons (cons (svar-prime v) val) env))
                           (svex-env-extract vars env)))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-env-lookup-of-cons
                                             svarlist-override-okp)))))
  
  (local (defthm svex-eval-of-cons-prime
           (implies (svarlist-override-okp (svex-vars x))
                    (equal (svex-eval x (cons (cons (svar-prime v) val) env))
                           (svex-eval x env)))
           :hints(("Goal" :in-theory (enable svex-eval-equal-when-extract-vars-similar
                                             svex-envs-similar)))))

  (local (defthm svex-vars-override-okp-of-lookup
           (implies (svarlist-override-okp (svex-alist-vars x))
                    (svarlist-override-okp (svex-vars (svex-lookup k x))))
           :hints(("Goal" :in-theory (enable svex-alist-vars svex-lookup)))))



  (defret svex-env-boundp-of-<fn>
    (implies (and (not (equal (svar-fix v) (svar-prime (svar-change-override x :test))))
                  (not (equal (svar-fix v) (svar-prime (svar-change-override x :val)))))
             (not (svex-env-boundp v env)))
    :hints(("Goal" :in-theory (enable svex-env-boundp-of-cons))))

  (defretd svex-env-boundp-of-<fn>-under-iff
    (iff (svex-env-boundp v env)
         (or (equal (svar-fix v) (svar-prime (svar-change-override x :test)))
             (equal (svar-fix v) (svar-prime (svar-change-override x :val)))))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defretd svex-env-lookup-of-<fn>
    (equal (svex-env-lookup v env)
           (cond ((equal (svar-fix v) (svar-prime (svar-change-override x :test)))
                  (svex-env-lookup (svar-change-override x :test) override-env))
                 ((equal (svar-fix v) (svar-prime (svar-change-override x :val)))
                  (svex-env-lookup (svar-change-override x :val)  override-env))
                 (t (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))

  (defret alist-keys-of-<fn>
    (Equal (alist-keys env)
           (list (svar-prime (svar-change-override x :test))
                 (svar-prime (svar-change-override x :val))))
    :hints(("Goal" :in-theory (enable alist-keys))))

  (defthm svar-overridekey-semantic-check-subst-env-correct
    (b* ((new-env (svar-overridekey-semantic-check-subst-env x override-env))
         (subst (svar-overridekey-semantic-check-subst x values))
         (subst-eval (svex-alist-eval subst (append new-env spec-env)))
         (spec-values (svex-alist-eval values spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys override-env spec-env spec-values)
                    (member-equal (svar-change-override x nil)
                                  (svarlist-change-override overridekeys nil))
                    (svarlist-override-okp (svex-alist-vars values)))
               (equal subst-eval
                      (svex-env-extract (list (svar-change-override x :test)
                                              (svar-change-override x :val))
                                        override-env))))
    :hints(("Goal" :in-theory (e/d (svar-overridekey-semantic-check-subst
                                    ;; svex-alist-eval
                                      svex-env-extract
                                      svex-apply
                                      svex-eval
                                      svex-env-lookup-of-cons
                                      svar-overridekeys-envs-agree
                                      4vec-override-mux-agrees
                                      4vec-bit?!)
                                   (overridekeys-envs-agree-implies
                                    len))
            :use ((:instance overridekeys-envs-agree-implies
                   (impl-env override-env)
                   (spec-outs (svex-alist-eval values spec-env))
                   (v (svar-change-override x nil)))
                  (:instance overridekeys-envs-agree-implies
                   (impl-env override-env)
                   (spec-outs (svex-alist-eval values spec-env))
                   (v (svar-change-override x :test)))
                  (:instance overridekeys-envs-agree-implies
                   (impl-env override-env)
                   (spec-outs (svex-alist-eval values spec-env))
                   (v (svar-change-override x :val))))
            :expand ((:free (a b env) (svex-alist-eval (cons a b) env))
                     (:free (env) (svex-alist-eval nil env)))
            :do-not-induct t))
    :otf-flg t)

  (defret <fn>-of-change-override
    (equal (let ((x (svar-change-override x type))) <call>)
           env))
  
  )

(defsection set-equiv-of-overridekeys->override-vars
  (defcong set-equiv set-equiv (overridekeys->override-vars x) 1
    :hints(("Goal" :in-theory (enable overridekeys->override-vars-under-set-equiv)))))

(defsection set-equiv-of-svarlist-prime
  (local (defund find-unprime (v x)
           (if (atom x)
               nil
             (if (equal v (svar-prime (car x)))
                 (car x)
               (find-unprime v (cdr x))))))
  (local (defthmd member-of-svarlist-prime-when-prime-exists
           (implies (and (member-equal unprime x)
                         (equal v (svar-prime unprime)))
                    (member-equal v (svarlist-prime x)))
           :hints(("Goal" :in-theory (enable svarlist-prime)))))
  (local (defthm no-member-of-svarlist-prime-when-not-find-unprime
           (b* ((unprime (find-unprime v x)))
             (implies (not (and (member-equal unprime x)
                                (equal v (svar-prime unprime))))
                      (not (member-equal v (svarlist-prime x)))))
           :hints(("Goal" :in-theory (enable svarlist-prime find-unprime)))))
  
  (defcong set-equiv set-equiv (svarlist-prime x) 1
    :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)
            :do-not-induct t)
           (and stable-under-simplificationp
                (b* ((lit (assoc-equal 'member-equal clause))
                     (witness (second lit))
                     (x (second (third lit)))
                     (x-equiv (if (eq x 'x) 'x-equiv 'x)))
                  `(:use ((:instance member-of-svarlist-prime-when-prime-exists
                           (v ,witness)
                           (x ,x)
                           (unprime (find-unprime ,witness ,x-equiv))))))))
    :otf-flg t))

(define svarlist-overridekeys-semantic-check-subst ((x svarlist-p)
                                                    (values svex-alist-p))
  :returns (subst svex-alist-p)
  ;; Returns the substitution to apply to the original list of svexes, to
  ;; create the new ones to be equivalence checked against them.  Two new
  ;; variables are used: the :bad override type of the testvar, i.e. with both
  ;; its override-test/override-val bits set, and the valvar with :nonblocking
  ;; set.  The former indicates whether the testvar is set in the override-env
  ;; in the case where it's not set in the spec-env.  The latter indicates the
  ;; value of the valvar in the override-env when it's not relevant because
  ;; it's not overridden.
  (if (atom x)
      nil
    (append (svar-overridekey-semantic-check-subst (car x) values)
            (svarlist-overridekeys-semantic-check-subst (cdr x) values)))
  ///
  (defret keys-of-<fn>
    (equal (svex-alist-keys subst)
           (overridekeys->override-vars x))
    :hints(("Goal" :in-theory (enable svex-alist-keys
                                      overridekeys->override-vars))))

  

  (defret vars-of-<fn>
    (implies (and (not (member-equal v (overridekeys->override-vars x)))
                  (not (member-equal v (svarlist-prime (overridekeys->override-vars x))))
                  (not (member-equal v (svex-alist-vars values))))
             (not (member-equal v (svex-alist-vars subst))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svarlist-change-override
                                      overridekeys->override-vars
                                      svarlist-prime))))

  (defretd lookup-of-<fn>
    (equal (svex-lookup v subst)
           (and (member-equal (svar-fix v) (overridekeys->override-vars x))
                (b* ((x.testvar (svar-change-override v :test))
                     (x.valvar  (svar-change-override v :val))
                     (refvar (svar-change-override v nil))
                     (x.valexpr (or (svex-lookup refvar values) (svex-x)))
                     (new-test-var (svar-prime x.testvar))
                     (test-expr (svcall bit?! (svex-var x.testvar) -1 (svex-var new-test-var)))
                     (val-expr (svcall bit?!
                                       (svex-var x.testvar)
                                       (svex-var x.valvar)
                                       (svcall bit?!
                                               (svex-var new-test-var)
                                               x.valexpr
                                               (svex-var (svar-prime x.valvar))))))
                  (if (svar-override-p v :test)
                      test-expr
                    val-expr))))
    :hints(("Goal" :in-theory (enable lookup-of-svar-overridekey-semantic-check-subst
                                      equal-of-svar-change-override
                                      overridekeys->override-vars))))

  (defcong set-equiv svex-alist-eval-equiv (svarlist-overridekeys-semantic-check-subst x values) 1
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                      lookup-of-svarlist-overridekeys-semantic-check-subst)
            :do-not-induct t)))

  (defret <fn>-of-svar-change-override
    (equal (let ((x (svarlist-change-override x type))) <call>)
           subst)
    :hints(("Goal" :in-theory (enable svarlist-change-override)))))


(local (defthm svex-env-extract-append-not-intersect-second
         (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix b))))
                  (equal (svex-env-extract vars (append a b c))
                         (svex-env-extract vars (append a c))))
         :hints(("Goal" :in-theory (enable svex-env-extract
                                           intersectp-equal
                                           svex-env-boundp-iff-member-alist-keys)
                 :induct (len vars)))))

(local (defthm svex-alist-eval-of-append-not-intersect-second
         (implies (not (intersectp-equal (svex-alist-vars x)
                                         (alist-keys (svex-env-fix b))))
                  (equal (svex-alist-eval x (append a b c))
                         (svex-alist-eval x (append a c))))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))

(local (defthm svexlist-eval-of-append-not-intersect-second
         (implies (not (intersectp-equal (svexlist-vars x)
                                         (alist-keys (svex-env-fix b))))
                  (equal (svexlist-eval x (append a b c))
                         (svexlist-eval x (append a c))))
         :hints(("Goal" :in-theory (enable svexlist-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))

(local (defthm svex-eval-of-append-not-intersect-second
         (implies (not (intersectp-equal (svex-vars x)
                                         (alist-keys (svex-env-fix b))))
                  (equal (svex-eval x (append a b c))
                         (svex-eval x (append a c))))
         :hints(("Goal" :in-theory (enable svex-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))



(local (defthm svex-env-extract-append-not-intersect-first
         (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix a))))
                  (equal (svex-env-extract vars (append a b))
                         (svex-env-extract vars b)))
         :hints(("Goal" :in-theory (enable svex-env-extract
                                           intersectp-equal
                                           svex-env-boundp-iff-member-alist-keys)
                 :induct (len vars)))))

(local (defthm svex-alist-eval-of-append-not-intersect-first
         (implies (not (intersectp-equal (svex-alist-vars x)
                                         (alist-keys (svex-env-fix a))))
                  (equal (svex-alist-eval x (append a b))
                         (svex-alist-eval x b)))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))

(local (defthm svexlist-eval-of-append-not-intersect-first
         (implies (not (intersectp-equal (svexlist-vars x)
                                         (alist-keys (svex-env-fix a))))
                  (equal (svexlist-eval x (append a b))
                         (svexlist-eval x b)))
         :hints(("Goal" :in-theory (enable svexlist-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))

(local (defthm svex-eval-of-append-not-intersect-first
         (implies (not (intersectp-equal (svex-vars x)
                                         (alist-keys (svex-env-fix a))))
                  (equal (svex-eval x (append a b))
                         (svex-eval x b)))
         :hints(("Goal" :in-theory (enable svex-eval-equal-when-extract-vars-similar
                                           svex-envs-similar)))))

(local (defthm member-svar-change-override-svarlist-change-override-diff
         (implies (not (svar-overridetype-equiv type1 type2))
                  (not (member-equal (svar-change-override x type1)
                                     (svarlist-change-override y type2))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           equal-of-svar-change-override)))))

(local (defthm member-svar-change-override-svarlist-change-override-same
         (implies (syntaxp (not (equal type ''nil)))
                  (iff (member-equal (svar-change-override x type)
                                     (svarlist-change-override y type))
                       (member-equal (svar-change-override x nil)
                                     (svarlist-change-override y nil))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           equal-of-svar-change-override)))))

(local (defthm not-member-overridekeys->override-vars-when-not-member
         (implies (not (member-equal (svar-change-override x nil)
                                     (svarlist-change-override keys nil)))
                  (not (member-equal (svar-change-override x type)
                                     (overridekeys->override-vars keys))))
         :hints(("Goal" :in-theory (e/d (overridekeys->override-vars-under-set-equiv)
                                        (svar-overridetype-equiv))
                 :cases ((svar-overridetype-equiv type :test)
                         (svar-overridetype-equiv type :val))))))

(local (defthm svar-change-override-of-svar-prime
         (equal (svar-change-override (svar-prime x) type)
                (svar-change-override x type))
         :hints(("Goal" :in-theory (enable svar-change-override svar-prime)))))


(define svarlist-overridekeys-semantic-check-subst-env ((x svarlist-p)
                                                        (override-env svex-env-p))
  :returns (env svex-env-p)
  ;; makes an env under which if you evaluate the semantic-check-subst above,
  ;; its values match those of override-env provided the conditions relating
  ;; override-env and spec-env hold.

  ;; actually the env needs to include spec-env as well; this env only includes
  ;; the additional variables that weren't in x to begin with.
  (if (atom x)
      nil
    (append (svar-overridekey-semantic-check-subst-env (car x) override-env)
            (svarlist-overridekeys-semantic-check-subst-env (cdr x) override-env)))
  ///


  

  (defret alist-keys-of-<fn>
    (Equal (alist-keys env)
           (svarlist-prime (overridekeys->override-vars x)))
    :hints(("Goal" :in-theory (enable svarlist-prime
                                      overridekeys->override-vars))))

  (local (in-theory (disable acl2::intersectp-equal-commute)))

  (local (defthm subst-vars-not-intersect-svarlist-prime
           (implies (and (not (member-equal (svar-change-override x :test) (svarlist-fix vars)))
                         (not (member-equal (svar-change-override x :val) (svarlist-fix vars)))
                         (svarlist-override-okp vars)
                         (svarlist-override-okp (svex-alist-vars values)))
                    (not (intersectp-equal
                          (svex-alist-vars (svar-overridekey-semantic-check-subst x values))
                          (svarlist-prime vars))))
           :hints (("goal" :induct (svarlist-prime vars)
                    :in-theory (enable svarlist-prime
                                       svarlist-fix
                                       svarlist-override-okp
                                       svar->svex-override-triple)))))
  
  
  (defthm svarlist-overridekeys-semantic-check-subst-env-correct
    (b* ((new-env (svarlist-overridekeys-semantic-check-subst-env x override-env))
         (subst (svarlist-overridekeys-semantic-check-subst x values))
         (subst-eval (svex-alist-eval subst (append new-env spec-env)))
         (spec-values (svex-alist-eval values spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys override-env spec-env spec-values)
                    (subsetp-equal (svarlist-change-override x nil)
                                   (svarlist-change-override overridekeys nil))
                    (svarlist-override-okp (svex-alist-vars values))
                    (no-duplicatesp-equal (svarlist-change-override x nil)))
               (equal subst-eval
                      (svex-env-extract (overridekeys->override-vars x)
                                        override-env))))
    :hints(("Goal" :in-theory (e/d (svarlist-overridekeys-semantic-check-subst
                                    ;; svex-alist-eval
                                    overridekeys->override-vars
                                    svarlist-change-override
                                      svex-env-extract
                                      svex-env-lookup-of-cons
                                      4vec-override-mux-agrees
                                      4vec-bit?!))
            :induct (len x)
            :expand ((svex-alist-eval nil spec-env))
            :do-not-induct t)))

  (defretd svex-env-boundp-of-<fn>-under-iff
    (iff (svex-env-boundp v env)
         (member-equal (svar-fix v) (svarlist-prime (overridekeys->override-vars x))))
    :hints(("Goal" :in-theory (enable overridekeys->override-vars
                                      svarlist-prime
                                      svex-env-boundp-of-svar-overridekey-semantic-check-subst-env-under-iff))))

  (local (defthmd equal-svar-prime-of-override-ok-lemma
           (implies (and (equal v (svar-prime y))
                         (svar-override-okp y)
                         (svar-p v) (svar-p y))
                    (equal (svar-unprime v) y))
           :hints (("goal" :do-not-induct t))
           :otf-flg t))
  
  (local (defthm equal-svar-prime-of-override-ok
           (implies (and (equal (svar-fix v) (svar-prime y))
                         (svar-override-okp y))
                    (equal (svar-unprime v) (svar-fix y)))
           :hints (("goal" :use ((:instance equal-svar-prime-of-override-ok-lemma
                                  (v (svar-fix v)) (y (svar-fix y))))))
           :otf-flg t))

  (local (defthmd change-override-when-equal-svar-prime-of-override-ok-lemma
           (implies (and (equal v (svar-prime y))
                         (svar-p v))
                    (equal (svar-change-override v type)
                           (svar-change-override y type)))
           :otf-flg t))
  
  (local (defthm change-override-when-equal-svar-prime-of-override-ok
           (implies (equal (svar-fix v) (svar-prime y))
                    (equal (svar-change-override v type)
                           (svar-change-override y type)))
           :hints (("goal" :use ((:instance change-override-when-equal-svar-prime-of-override-ok-lemma
                                  (v (svar-fix v))))))
           :otf-flg t))
  
  (defretd svex-env-lookup-of-<fn>
    (equal (svex-env-lookup v env)
           (if (member-equal (svar-fix v) (svarlist-prime (overridekeys->override-vars x)))
               (if (svar-override-p (svar-unprime v) :test)
                   (svex-env-lookup (svar-change-override v :test) override-env)
                 (svex-env-lookup (svar-change-override v :val) override-env))
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons
                                      overridekeys->override-vars
                                      svarlist-prime
                                      svex-env-boundp-of-svar-overridekey-semantic-check-subst-env-under-iff
                                      svex-env-lookup-of-svar-overridekey-semantic-check-subst-env))))

  (defcong set-equiv svex-envs-equivalent (svarlist-overridekeys-semantic-check-subst-env x override-env) 1
    :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                      svex-env-lookup-of-svarlist-overridekeys-semantic-check-subst-env
                                      svex-env-boundp-of-svarlist-overridekeys-semantic-check-subst-env-under-iff)
            :do-not-induct t)))
  

  (defret <fn>-of-change-override
    (equal (let ((x (svarlist-change-override x type))) <call>)
           env)
    :hints(("Goal" :in-theory (enable svarlist-change-override)))))


(defsection overridekeys-envs-agree-implies-append-extract-override-vars-similar
  (local
   (defret all-nonoverride-vars-agree-when-<fn>
     (implies (and agree
                   (case-split (or (not (svarlist-member-nonoverride v overridekeys))
                                   (and (not (svar-override-p v :test))
                                        (not (svar-override-p v :val))))))
              (equal (svex-env-lookup v impl-env)
                     (svex-env-lookup v spec-env)))
     :hints (("goal" :use <fn>-implies
              :in-theory (e/d (svar-overridekeys-envs-agree)
                              (<fn>-implies))))
     :fn overridekeys-envs-agree))

  (local (defthm svarlist-member-nonoverride-and-svar-override-p-implies-member-svarlist-change-override
           (implies (and (svarlist-member-nonoverride x y)
                         (svar-override-p x type)
                         (svar-p x))
                    (member-equal x (svarlist-change-override y type)))
           :hints(("Goal" :in-theory (enable svarlist-member-nonoverride
                                             svarlist-change-override
                                             equal-of-svar-change-override)))))
  
  (defthm overridekeys-envs-agree-implies-append-extract-override-vars-similar
    (implies (overridekeys-envs-agree overridekeys override-env spec-env values)
             (svex-envs-similar (append (svex-env-extract (overridekeys->override-vars overridekeys) override-env)
                                        spec-env)
                                override-env))
    :hints(("Goal" :in-theory (enable svex-envs-similar
                                      overridekeys->override-vars-under-set-equiv)))))
  
(defthm svex-override-eval-differs-implies-substitution-differs
  (b* ((new-env (svarlist-overridekeys-semantic-check-subst-env x override-env))
       (subst (svarlist-overridekeys-semantic-check-subst x values))
       (spec-values (svex-alist-eval values spec-env)))
    (implies (and (overridekeys-envs-agree x override-env spec-env spec-values)
                  (svarlist-override-okp (svex-alist-vars values))
                  (no-duplicatesp-equal (svarlist-change-override x nil))
                  (svarlist-override-okp (svex-vars y))
                  (not (equal (svex-eval y spec-env)
                              (svex-eval y override-env))))
             (not (equal (svex-eval y (append new-env spec-env))
                         (svex-eval (svex-compose y subst)
                                    (append new-env spec-env)))))))

(defthm svexlist-override-eval-differs-implies-substitution-differs
  (b* ((new-env (svarlist-overridekeys-semantic-check-subst-env x override-env))
       (subst (svarlist-overridekeys-semantic-check-subst x values))
       (spec-values (svex-alist-eval values spec-env)))
    (implies (and (overridekeys-envs-agree x override-env spec-env spec-values)
                  (svarlist-override-okp (svex-alist-vars values))
                  (no-duplicatesp-equal (svarlist-change-override x nil))
                  (svarlist-override-okp (svexlist-vars y))
                  (not (equal (svexlist-eval y spec-env)
                              (svexlist-eval y override-env))))
             (not (equal (svexlist-eval y (append new-env spec-env))
                         (svexlist-eval (svexlist-compose y subst)
                                        (append new-env spec-env)))))))

(defthm svex-alist-override-eval-differs-implies-substitution-differs
  (b* ((new-env (svarlist-overridekeys-semantic-check-subst-env x override-env))
       (subst (svarlist-overridekeys-semantic-check-subst x values))
       (spec-values (svex-alist-eval values spec-env)))
    (implies (and (overridekeys-envs-agree x override-env spec-env spec-values)
                  (svarlist-override-okp (svex-alist-vars values))
                  (no-duplicatesp-equal (svarlist-change-override x nil))
                  (svarlist-override-okp (svex-alist-vars y))
                  (not (equal (svex-alist-eval y spec-env)
                              (svex-alist-eval y override-env))))
             (not (equal (svex-alist-eval y (append new-env spec-env))
                         (svex-alist-eval (svex-alist-compose y subst)
                                          (append new-env spec-env)))))))


(defthm svarlist-change-override-of-svarlist-change-override
  (equal (svarlist-change-override (svarlist-change-override x type1) type2)
         (svarlist-change-override x type2))
  :hints(("Goal" :in-theory (enable svarlist-change-override))))

(defthm overridekeys-envs-agree-of-change-override
  (iff (overridekeys-envs-agree (svarlist-change-override x type) override-env spec-env spec-values)
       (overridekeys-envs-agree x override-env spec-env spec-values))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               (b* ((lit (assoc 'overridekeys-envs-agree clause))
                    (witness `(overridekeys-envs-agree-badguy . ,(cdr lit)))
                    (keys (second lit))
                    (other (if (eq keys 'x) '(svarlist-change-override x type) 'x)))
                 `(:use ((:instance badguy-not-agree-when-not-overridekeys-envs-agree
                          (overridekeys ,keys) (impl-env override-env) (spec-outs spec-values))
                         (:instance overridekeys-envs-agree-implies
                          (overridekeys ,other) (impl-env override-env) (spec-outs spec-values)
                          (v ,witness)))
                   :in-theory (enable svar-overridekeys-envs-agree))))))
                          

(defthm svarlist-override-p-of-remove-duplicates
  (implies (Svarlist-override-p x type)
           (svarlist-override-p (remove-duplicates-equal x) type))
  :hints(("Goal" :in-theory (enable remove-duplicates-equal svarlist-override-p))))

(defthm svarlist-p-of-remove-duplicates
  (implies (Svarlist-p x)
           (svarlist-p (remove-duplicates-equal x)))
  :hints(("Goal" :in-theory (enable remove-duplicates-equal svarlist-p))))

(local (defthm svarlist-change-override-when-svarlist-override-p
         (implies (svarlist-override-p x type)
                  (equal (svarlist-change-override x type) (svarlist-fix x)))
         :hints(("Goal" :in-theory (enable svarlist-override-p
                                           svarlist-change-override
                                           svarlist-fix)))))

(local (defthm no-dups-of-rem-dups
         (no-duplicatesp-equal (remove-duplicates-equal x))
         :hints(("Goal" :in-theory (enable no-duplicatesp-equal
                                           remove-duplicates-equal)))))

(defthm svex-overridekey-transparent-p-by-substitution-equiv
  (b* ((subst (svarlist-overridekeys-semantic-check-subst x values)))
    (implies (and (svex-eval-equiv y (svex-compose y subst))
                  (svarlist-override-okp (svex-alist-vars values))
                  (svarlist-override-okp (svex-vars y)))
             (svex-overridekey-transparent-p y x values)))
  :hints (("goal"
           :expand ((svex-overridekey-transparent-p y x values))
           :use ((:instance svex-override-eval-differs-implies-substitution-differs
                  (x (remove-duplicates-equal (svarlist-change-override x nil)))
                  (override-env (mv-nth 0 (svex-overridekey-transparent-p-witness y x values)))
                  (spec-env (mv-nth 1 (svex-overridekey-transparent-p-witness y x values)))))
           :in-theory (disable svex-override-eval-differs-implies-substitution-differs
                               svex-eval-of-svex-compose))))

(local
 (defsection svex-alist-compose-cong
   (defthm svex-alist-vals-of-svex-alist-compose
     (equal (svex-alist-vals (svex-alist-compose x y))
            (svexlist-compose (svex-alist-vals x) y))
     :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-compose
                                       svexlist-compose))))
   (defcong svex-alist-eval-equiv svex-alist-eval-equiv!! (svex-alist-compose x y) 2
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv!!))))))


(defthm svex-alist-overridekey-transparent-p-by-substitution-equiv
  (b* ((subst (svarlist-overridekeys-semantic-check-subst x values)))
    (implies (and (svex-alist-eval-equiv!! y (svex-alist-compose y subst))
                  (svarlist-override-okp (svex-alist-vars values))
                  (svarlist-override-okp (svex-alist-vars y)))
             (svex-alist-overridekey-transparent-p y x values)))
  :hints (("goal"
           :expand ((:with svex-alist-overridekey-transparent-p
                     (svex-alist-overridekey-transparent-p y x values)))
           :use ((:instance svex-alist-override-eval-differs-implies-substitution-differs
                  (x (remove-duplicates-equal (svarlist-change-override x nil)))
                  (override-env (mv-nth 0 (svex-alist-overridekey-transparent-p-witness y x values)))
                  (spec-env (mv-nth 1 (svex-alist-overridekey-transparent-p-witness y x values)))))
           :in-theory (disable svex-alist-override-eval-differs-implies-substitution-differs
                               svex-alist-eval-of-svex-compose))))

(defthm svexlist-overridekey-transparent-p-by-substitution-equiv
  (b* ((subst (svarlist-overridekeys-semantic-check-subst x values)))
    (implies (and (svexlist-eval-equiv y (svexlist-compose y subst))
                  (svarlist-override-okp (svex-alist-vars values))
                  (svarlist-override-okp (svexlist-vars y)))
             (svexlist-overridekey-transparent-p y x values)))
  :hints (("goal"
           :expand ((:with svexlist-overridekey-transparent-p
                     (svexlist-overridekey-transparent-p y x values)))
           :use ((:instance svexlist-override-eval-differs-implies-substitution-differs
                  (x (remove-duplicates-equal (svarlist-change-override x nil)))
                  (override-env (mv-nth 0 (svexlist-overridekey-transparent-p-witness y x values)))
                  (spec-env (mv-nth 1 (svexlist-overridekey-transparent-p-witness y x values)))))
           :in-theory (disable svexlist-override-eval-differs-implies-substitution-differs
                               svexlist-eval-of-svexlist-compose))))
           
