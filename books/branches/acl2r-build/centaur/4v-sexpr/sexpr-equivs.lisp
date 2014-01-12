; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
;
; Original author: Sol Swords <sswords@centtech.com>

; sexpr-equivs.lisp
;   - equivalence relations for 4-valued constants and environments
;   - extension of <= to sexprs and sexpr alists
;   - equivalence relations for sexprs and sexpr alists

(in-package "ACL2")
(include-book "sexpr-eval")
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "centaur/misc/fast-alists" :dir :system)
(set-inhibit-warnings "theory" "disable")

(defsection sexpr-equivs
  :parents (4v-sexprs)
  :short "Useful equivalence relations for reasoning about @(see 4v-sexprs).")

(local (xdoc::set-default-parents sexpr-equivs))


(def-universal-equiv 4v-equiv
  :equiv-terms ((equal (4v-fix x)))
  :short "Equivalence of four-valued constants, i.e., @(see 4vp)s."
  :long "<p>@('X') === @('Y') in the sense of four-valued objects if they fix
to the same @(see 4vp).  That is, except for @('(4vf)'), @('(4vz)'), and
@('(4vt)'), all objects are equivalent to @('(4vx)') under this
relationship.</p>")

(defun prove-4v-equiv-congs (n f ins)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons `(defcong 4v-equiv equal (,f . ,ins) ,n)
          (prove-4v-equiv-congs (1- n) f ins))))

(defmacro prove-4v-equiv-cong (f ins)
  `(progn
     . ,(prove-4v-equiv-congs (len ins) f ins)))


(defsection 4v-equiv-thms
  :extension 4v-equiv

  (in-theory (enable 4v-equiv))

  (defthm 4v-equiv-4v-fix
    (4v-equiv (4v-fix x) x))

  (defcong 4v-equiv equal (4v-<= a b) 1)
  (defcong 4v-equiv equal (4v-<= a b) 2)

  (prove-4v-equiv-cong 4v-fix (a))
  (prove-4v-equiv-cong 4v-unfloat (a))
  (prove-4v-equiv-cong 4v-not (a))
  (prove-4v-equiv-cong 4v-and (a b))
  (prove-4v-equiv-cong 4v-or (a b))
  (prove-4v-equiv-cong 4v-xor (a b))
  (prove-4v-equiv-cong 4v-iff (a b))
  (prove-4v-equiv-cong 4v-res (a b))
  (prove-4v-equiv-cong 4v-ite (c a b))
  (prove-4v-equiv-cong 4v-ite* (c a b))
  (prove-4v-equiv-cong 4v-zif (c a b))
  (prove-4v-equiv-cong 4v-tristate (c a))
  (prove-4v-equiv-cong 4v-pullup (a)))


(def-universal-equiv 4v-cdr-equiv
  :equiv-terms ((4v-equiv (cdr x)))
  :short "Weaker version of element equivalence for four-valued alists.")

(defsection 4v-cdr-equiv-thms
  :extension 4v-cdr-equiv

  (in-theory (enable 4v-cdr-equiv))
  (defcong 4v-cdr-equiv 4v-equiv (cdr x) 1))


(def-universal-equiv 4v-cdr-consp-equiv
  :equiv-terms ((iff (consp x))
                (equal (car x))
                (4v-equiv (cdr x)))
  :short "Stronger version of element equivalence for four-valued alists.")

(defsection 4v-cdr-consp-equiv-thms
  :extension 4v-cdr-consp-equiv

  (in-theory (enable 4v-cdr-consp-equiv))
  (defcong 4v-equiv 4v-cdr-consp-equiv (cons a b) 2
    :hints (("Goal" :in-theory (disable 4v-fix)))))


(def-universal-equiv 4v-env-equiv
  :qvars key
  :equiv-terms ((equal (4v-lookup key x)))
  :defquant t
  :short "Equivalence of four-valued environments (alists)."
  :long "<p>@('X') === @('Y') in the sense of four-valued environments if
@('X[k] === Y[k]') for all keys @('k'), in the sense of @(see 4v-equiv).</p>")

(defsection 4v-env-equiv-thms
  :extension 4v-env-equiv

  (verify-guards 4v-env-equiv)

  (defexample 4v-env-equiv-hons-assoc-equal-ex
    :pattern (hons-assoc-equal x env)
    :templates (x)
    :instance-rulename 4v-env-equiv-instancing)

  (defexample 4v-env-equiv-4v-lookup-ex
    :pattern (4v-lookup k al)
    :templates (k)
    :instance-rulename 4v-env-equiv-instancing)

  (defrefinement alist-equiv 4v-env-equiv
    :hints ((witness)))

  (defcong 4v-env-equiv 4v-env-equiv (cons a b) 2
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defcong 4v-env-equiv 4v-env-equiv (append a b) 2
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defcong 4v-env-equiv iff (4v-alist-<= a b) 1
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset (4v-alist-<=-witnessing))
            (witness :ruleset (4v-alist-<=-hons-assoc-equal-example
                               4v-env-equiv-hons-assoc-equal-ex))))

  (defcong 4v-env-equiv iff (4v-alist-<= a b) 2
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-alist-<=-witnessing)
            (witness :ruleset (4v-alist-<=-hons-assoc-equal-example
                               4v-env-equiv-hons-assoc-equal-ex))))

  (defcong 4v-env-equiv equal (4v-lookup k al) 2
    :hints(("Goal" :in-theory (disable 4v-lookup))
           (witness :ruleset 4v-env-equiv-4v-lookup-ex)))

  (defcong 4v-env-equiv 4v-cdr-equiv (hons-assoc-equal x y) 2
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defcong 4v-cdr-consp-equiv 4v-env-equiv (cons a b) 1
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)))

  (defthm-4v-sexpr-flag
    (defthm 4v-env-equiv-implies-equal-4v-sexpr-eval-2
      (implies (4v-env-equiv env1 env2)
               (equal (4v-sexpr-eval x env1)
                      (4v-sexpr-eval x env2)))
      :flag sexpr
      :rule-classes :congruence)
    (defthm 4v-env-equiv-implies-equal-4v-sexpr-eval-list-2
      (implies (4v-env-equiv env1 env2)
               (equal (4v-sexpr-eval-list x env1)
                      (4v-sexpr-eval-list x env2)))
      :flag sexpr-list
      :rule-classes :congruence)
    :hints (("Goal" :in-theory (disable* (:ruleset 4v-op-defs)))
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defcong 4v-env-equiv equal (4v-sexpr-eval-alist x env) 2)

  (defthm 4v-env-equiv-append
    (implies (and (set-equiv (double-rewrite (alist-keys a))
                             (double-rewrite (alist-keys b)))
                  (4v-env-equiv (double-rewrite a)
                                (double-rewrite b))
                  (4v-env-equiv (double-rewrite c)
                                (double-rewrite d)))
             (equal (4v-env-equiv (append a c) (append b d))
                    t))
    :hints (("Goal" :do-not-induct t :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                   (alist-keys-member-hons-assoc-equal 4v-fix))))
            (set-reasoning))))



(def-universal-equiv key-and-env-equiv
  :equiv-terms ((keys-equiv x)
                (4v-env-equiv x))
  :short "@(call key-and-env-equiv) is an extension of @(see 4v-env-equiv) that
additionally requires the keys match between the two alists.")

(defsection key-and-env-equiv-thms
  :extension key-and-env-equiv

  (local (in-theory (enable key-and-env-equiv)))

  (defrefinement key-and-env-equiv 4v-env-equiv)

  (defcong key-and-env-equiv key-and-env-equiv (append a b) 1
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defcong key-and-env-equiv key-and-env-equiv (append a b) 2
    :hints (("Goal" :in-theory (disable 4v-fix))
            (witness :ruleset 4v-env-equiv-witnessing)
            (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

  (defthm 4v-env-equiv-to-key-and-env-equiv
    (implies (keys-equiv a b)
             (equal (4v-env-equiv a b)
                    (key-and-env-equiv a b))))

  (in-theory (disable key-and-env-equiv)))



(defsection 4v-alist-extract
  :parents (4v-sexprs)
  :short "Gather up a sub-alist from some 4v environment."

  (defun 4v-alist-extract (keys al)
    (declare (xargs :guard t))
    (if (atom keys)
        nil
      (cons (cons (car keys) (4v-lookup (car keys) al))
            (4v-alist-extract (cdr keys) al))))

  (defthm alist-keys-4v-alist-extract
    (equal (alist-keys (4v-alist-extract keys alist))
           (append keys nil)))

  (defthm hons-assoc-equal-4v-alist-extract
    (equal (hons-assoc-equal key (4v-alist-extract keys al))
           (and (member-equal key keys)
                (cons key (4v-fix (cdr (hons-assoc-equal key al)))))))

  (defcong set-equiv key-and-env-equiv (4v-alist-extract keys al) 1
    :hints(("Goal" :in-theory (e/d (key-and-env-equiv)
                                   (4v-env-equiv-to-key-and-env-equiv 4v-fix)))
           (witness :ruleset 4v-env-equiv-witnessing))))



(defsection 4v-alists-agree
  :short "See whether two four-valued alists agree on particular keys."

  (defun 4v-alists-agree (keys al1 al2)
    (declare (xargs :guard t))
    (or (atom keys)
        (and (equal (4v-lookup (car keys) al1)
                    (4v-lookup (car keys) al2))
             (4v-alists-agree (cdr keys) al1 al2))))

  (defthmd 4v-alists-agree-equiv
    ;; BOZO maybe add a loop-stopper?
    (implies (and (4v-alists-agree keys al1 al2)
                  (member-equal key keys))
             (equal (equal (4v-lookup key al1)
                           (4v-lookup key al2))
                    t)))

  (defthm 4v-alists-agree-self
    (4v-alists-agree k x x))

  (defthmd 4v-alists-agree-commutes
    (implies (4v-alists-agree vars al2 al1)
             (4v-alists-agree vars al1 al2)))

  (defthmd 4v-alists-agree-transitive1
    (implies (and (4v-alists-agree vars al1 al2)
                  (4v-alists-agree vars al2 al3))
             (4v-alists-agree vars al1 al3)))

  (defthmd 4v-alists-agree-transitive2
    (implies (and (4v-alists-agree vars al1 al2)
                  (4v-alists-agree vars al2 al3))
             (4v-alists-agree vars al1 al3)))

  (defthm 4v-alists-agree-append
    (equal (4v-alists-agree (append k1 k2) a b)
           (and (4v-alists-agree k1 a b)
                (4v-alists-agree k2 a b)))
    :hints(("Goal" :in-theory (disable 4v-lookup)))))


(defsection 4v-alists-disagree-witness
  :parents (4v-alists-agree)
  :short "Try to find a key for which two four-valued alists don't agree."

  (defun 4v-alists-disagree-witness (keys al1 al2)
    (declare (xargs :guard t))
    (if (atom keys)
        nil
      (if (equal (4v-lookup (car keys) al1)
                 (4v-lookup (car keys) al2))
          (4v-alists-disagree-witness (cdr keys) al1 al2)
        (car keys))))

  (defthmd 4v-alists-witness-correct
    (iff (4v-alists-agree keys al1 al2)
         (let ((witness (4v-alists-disagree-witness keys al1 al2)))
           (or (not (member-equal witness keys))
               (equal (4v-lookup witness al1)
                      (4v-lookup witness al2)))))
    :hints(("Goal" :in-theory (disable 4v-lookup)))))

(defsection 4v-alists-agree-thms
  :extension 4v-alists-agree

  (defwitness 4v-alists-agree-witnessing
    :predicate (not (4v-alists-agree keys al1 al2))
    :expr (not (let ((witness (4v-alists-disagree-witness keys al1 al2)))
                 (or (not (member-equal witness keys))
                     (equal (4v-lookup witness al1)
                            (4v-lookup witness al2)))))
    :generalize (((4v-alists-disagree-witness keys al1 al2) . key))
    :hints ('(:in-theory '(4v-alists-witness-correct))))

  (definstantiate 4v-alists-agree-instancing
    :predicate (4v-alists-agree keys al1 al2)
    :expr (or (not (member-equal key keys))
              (equal (4v-lookup key al1)
                     (4v-lookup key al2)))
    :vars (key)
    :hints ('(:in-theory '(4v-alists-agree-equiv))))

  (defexample 4v-alists-agree-4v-lookup-ex
    :pattern (4v-lookup key al)
    :templates (key)
    :instance-rulename 4v-alists-agree-instancing)

  (defthmd 4v-alists-agree-to-4v-env-equiv
    (iff (4v-alists-agree keys al1 al2)
         (4v-env-equiv (4v-alist-extract keys al1)
                       (4v-alist-extract keys al2)))
    :hints(("Goal" :in-theory (disable 4v-fix
                                       4v-env-equiv-to-key-and-env-equiv
                                       4v-alists-agree))
           (witness :ruleset (4v-alists-agree-witnessing
                              4v-alists-agree-4v-lookup-ex
                              4v-env-equiv-witnessing
                              4v-env-equiv-4v-lookup-ex))))

  (defcong set-equiv equal (4v-alists-agree keys a b) 1
    :hints(("Goal" :in-theory (e/d (4v-alists-agree-to-4v-env-equiv)
                                   (4v-fix)))))

  (defcong 4v-env-equiv equal (4v-alists-agree keys al al2) 2
    :hints(("Goal" :in-theory (disable 4v-fix)
            :induct (len keys)))))


(defsection 4v-sexpr-<=
  :parents (4v-sexprs 4v-monotonicity)
  :short "Extension of the four-valued lattice ordering to sexprs."
  :long "<p>We say @('X <= Y') for sexprs if X always evaluates to a smaller
value than Y evaluates to in every environment, in the sense of @(see
4v-<=).</p>

<p>When @('X <= Y'), we sometimes call @('X') a <b>conservative
approximation</b> of @('Y').</p>"

  (defquant 4v-sexpr-<= (x y)
    (forall env (4v-<= (4v-sexpr-eval x env)
                       (4v-sexpr-eval y env))))

  (verify-guards 4v-sexpr-<=)

  (defexample 4v-sexpr-<=-example
    :pattern (4v-sexpr-eval x env)
    :templates (env)
    :instance-rulename 4v-sexpr-<=-instancing)

  (defthm 4v-sexpr-<=-nil
    (4v-sexpr-<= nil x)
    :hints ((witness)))

  (defthm 4v-sexpr-<=-refl
    (4v-sexpr-<= x x)
    :hints ((witness :ruleset 4v-sexpr-<=-witnessing)))

  (defthmd 4v-sexpr-<=-trans1
    (implies (and (4v-sexpr-<= a b)
                  (4v-sexpr-<= b c))
             (4v-sexpr-<= a c))
    :hints (("goal" :in-theory (e/d () (4v-sexpr-eval)))
            (witness :ruleset (4v-sexpr-<=-witnessing
                               4v-sexpr-<=-example))))

  (defthmd 4v-sexpr-<=-trans2
    (implies (and (4v-sexpr-<= b c)
                  (4v-sexpr-<= a b))
             (4v-sexpr-<= a c))
    :hints (("goal" :in-theory (e/d () (4v-sexpr-eval)))
            (witness :ruleset (4v-sexpr-<=-witnessing
                               4v-sexpr-<=-example)))))


(defsection 4v-sexpr-alist-<=
  :parents (4v-sexpr-<=)
  :short "Extension of @(see 4v-sexpr-<=) to alists."
  :long "<p>We say @('X <= Y') for sexpr alists when @('X[k] <= Y[k]') for all
  keys @('k').</p>"

  (defquant 4v-sexpr-alist-<= (a b)
    (forall k (4v-sexpr-<= (cdr (hons-assoc-equal k a))
                           (cdr (hons-assoc-equal k b)))))

  (verify-guards 4v-sexpr-alist-<=)

  (defexample 4v-sexpr-alist-<=-hons-assoc-equal-example
    :pattern (hons-assoc-equal a b)
    :templates (a)
    :instance-rulename 4v-sexpr-alist-<=-instancing)

  (defthm 4v-sexpr-alist-<=-refl
    (4v-sexpr-alist-<= x x)
    :hints ((witness :ruleset 4v-sexpr-alist-<=-witnessing)))

  (defthmd 4v-sexpr-alist-<=-trans1
    (implies (and (4v-sexpr-alist-<= a b)
                  (4v-sexpr-alist-<= b c))
             (4v-sexpr-alist-<= a c))
    :hints (("goal" :in-theory (e/d (4v-sexpr-<=-trans1)
                                    (4v-sexpr-eval)))
            (witness :ruleset (4v-sexpr-alist-<=-witnessing
                               4v-sexpr-alist-<=-hons-assoc-equal-example))))

  (defthmd 4v-sexpr-alist-<=-trans2
    (implies (and (4v-sexpr-alist-<= b c)
                  (4v-sexpr-alist-<= a b))
             (4v-sexpr-alist-<= a c))
    :hints (("goal" :in-theory (e/d (4v-sexpr-<=-trans2)
                                    (4v-sexpr-eval)))
            (witness :ruleset (4v-sexpr-alist-<=-witnessing
                               4v-sexpr-alist-<=-hons-assoc-equal-example))))

  (defthm hons-assoc-equal-sexpr-monotonic
    (implies (4v-sexpr-alist-<= a b)
             (4v-sexpr-<= (cdr (hons-assoc-equal k a))
                          (cdr (hons-assoc-equal k b))))
    :hints((witness :ruleset 4v-sexpr-alist-<=-hons-assoc-equal-example))))


(defsection 4v-sexpr-alist-<=-alt
  :parents (4v-sexpr-alist-<=)
  :short "Just a different way to define @('<=') for sexpr alists."

  :long "<p>The definition of @('4v-sexpr-alist-<=') compares the actual sexprs
bound in the alists.  Here, instead, we first evaluate all the sexprs in the
alist, then compare their results using our simple @(see 4v-alist-<=)
comparison for four-valued alists.</p>

<p>Either definition is equivalent, as established by this theorem, which is
ordinarily disabled.</p>

@(def 4v-sexpr-alist-<=-is-alt)"

  (defquant 4v-sexpr-alist-<=-alt (a b)
    (forall env
            (4v-alist-<= (4v-sexpr-eval-alist a env)
                         (4v-sexpr-eval-alist b env))))

  (defexample 4v-sexpr-alist-<=-alt-eval-ex
    :pattern (4v-sexpr-eval a env)
    :templates (env)
    :instance-rulename 4v-sexpr-alist-<=-alt-instancing)

  (defexample 4v-sexpr-alist-<=-alt-eval-alist-ex
    :pattern (4v-sexpr-eval-alist a env)
    :templates (env)
    :instance-rulename 4v-sexpr-alist-<=-alt-instancing)

  (defthm 4v-alist-<=-4v-sexpr-eval-alist
    (implies (4v-sexpr-alist-<= a b)
             (4v-alist-<= (4v-sexpr-eval-alist a env)
                          (4v-sexpr-eval-alist b env)))
    :hints (("Goal" :in-theory (disable 4v-alist-<= 4v-sexpr-eval))
            (witness) (witness) (witness)))

  (defthmd 4v-sexpr-alist-<=-is-alt
    (iff (4v-sexpr-alist-<= a b)
         (4v-sexpr-alist-<=-alt a b))
    :hints (("Goal" :in-theory (disable 4v-sexpr-eval))
            (witness :ruleset (4v-sexpr-alist-<=-witnessing
                               4v-sexpr-alist-<=-alt-witnessing))
            (witness :ruleset (4v-sexpr-<=-witnessing
                               4v-sexpr-alist-<=-alt-eval-ex))
            (witness :ruleset 4v-sexpr-alist-<=-ex)
            (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))))



(def-universal-equiv 4v-sexpr-equiv
  :qvars env
  :equiv-terms ((equal (4v-sexpr-eval x env)))
  :defquant t
  :short "@('X') === @('Y') in the sense of sexprs if they always evaluate to
  the same thing under any possible environment.")

(defsection 4v-sexpr-equiv-thms
  :extension 4v-sexpr-equiv

  (verify-guards 4v-sexpr-equiv)

  (defcong 4v-sexpr-equiv equal (4v-sexpr-eval x env) 1
    :hints (("Goal" :use ((:instance 4v-sexpr-equiv-necc (y x-equiv))))))

  (defcong 4v-sexpr-equiv iff (4v-sexpr-<= a b) 2
    :hints (("Goal" :in-theory (disable 4v-sexpr-eval))
            (witness)))

  (defcong 4v-sexpr-equiv iff (4v-sexpr-<= a b) 1
    :hints (("Goal" :in-theory (disable 4v-sexpr-eval))
            (witness)))

  (defcong 4v-sexpr-equiv 4v-sexpr-equiv (4v-sexpr-restrict x al) 1
    :hints ((witness :ruleset 4v-sexpr-equiv-witnessing)))

  (defcong 4v-sexpr-equiv 4v-sexpr-equiv (4v-sexpr-compose x al) 1
    :hints ((witness :ruleset 4v-sexpr-equiv-witnessing))))




(def-universal-equiv 4v-sexpr-list-equiv
  :qvars env
  :equiv-terms ((equal (4v-sexpr-eval-list x env)))
  :defquant t
  :short "@('X') === @('Y') in the sense of sexpr lists if they are equal
  lengths and @('Xi') evaluates to the same thing as @('Yi') for all @('i') and
  for all environments.")

(defsection 4v-sexpr-list-equiv-thms
  :extension 4v-sexpr-list-equiv

  (defexample 4v-sexpr-list-equiv-eval-list-ex
    :pattern (4v-sexpr-eval-list x env)
    :templates (env)
    :instance-rulename 4v-sexpr-list-equiv-instancing)

  (defexample 4v-sexpr-list-equiv-eval-car-ex
    :pattern (4v-sexpr-eval (car x) env)
    :templates (env)
    :instance-rulename 4v-sexpr-list-equiv-instancing)

  (encapsulate nil
    (local (defthm equal-of-booleans
             (implies (and (booleanp a) (booleanp b))
                      (equal (equal a b)
                             (iff a b)))))

    (local (in-theory (disable 4v-sexpr-eval)))
    (defthmd 4v-sexpr-list-equiv-alt-def
      (equal (4v-sexpr-list-equiv x y)
             (if (atom x)
                 (atom y)
               (and (consp y)
                    (4v-sexpr-equiv (car x) (car y))
                    (4v-sexpr-list-equiv (cdr x) (cdr y)))))
      :hints (("Goal" :do-not-induct t)
              (witness :ruleset (4v-sexpr-list-equiv-witnessing
                                 4v-sexpr-list-equiv-eval-list-ex
                                 4v-sexpr-list-equiv-eval-car-ex
                                 4v-sexpr-equiv-witnessing))
              (and stable-under-simplificationp
                   '(:in-theory (enable 4v-sexpr-list-equiv)
                                :expand ((:free (env) (4v-sexpr-eval-list x env))
                                         (:free (env) (4v-sexpr-eval-list y env))))))
      :rule-classes :definition))

  (defcong 4v-sexpr-list-equiv equal (4v-sexpr-eval-list x env) 1
    :hints (("Goal" :use ((:instance 4v-sexpr-list-equiv-necc (y x-equiv))))))

  (defcong 4v-sexpr-list-equiv 4v-sexpr-equiv (cons x a) 2
    :hints (("Goal" :in-theory (disable* (:ruleset 4v-op-defs))
             :expand ((4v-sexpr-eval (cons x a) env0)
                      (4v-sexpr-eval (cons x b) env0)))
            (witness :ruleset 4v-sexpr-equiv-witnessing)))

  (defcong 4v-sexpr-equiv 4v-sexpr-list-equiv (cons a b) 1
    :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing)))

  (defcong 4v-sexpr-list-equiv 4v-sexpr-list-equiv (cons a b) 2
    :hints ((witness :ruleset 4v-sexpr-list-equiv-witnessing))))



(def-universal-equiv 4v-sexpr-alist-pair-equiv
  :equiv-terms ((iff (consp x))
                (equal (car x))
                (4v-sexpr-equiv (cdr x)))
  :short "Element equivalence for sexpr alists.")

(defsection 4v-sexpr-alist-pair-equiv-thms
  :extension 4v-sexpr-alist-pair-equiv

  (defcong 4v-sexpr-equiv 4v-sexpr-alist-pair-equiv (cons a b) 2
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-pair-equiv))))

  (defcong 4v-sexpr-alist-pair-equiv 4v-sexpr-equiv (cdr x) 1
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-pair-equiv)))))



(def-universal-equiv 4v-sexpr-alist-equiv
  :qvars k
  :equiv-terms ((iff (hons-assoc-equal k x))
                (4v-sexpr-equiv (cdr (hons-assoc-equal k x))))
  :defquant t
  :short "@('X') === @('Y') in the sense of sexpr alists if @('X[k]') ===
  @('Y[k]') in the sense of sexprs for all keys @('k').")

(defsection 4v-sexpr-alist-equiv-thms
  :extension 4v-sexpr-alist-equiv

  (verify-guards 4v-sexpr-alist-equiv)

  (defexample 4v-sexpr-alist-equiv-example
    :pattern (hons-assoc-equal x a)
    :templates (x)
    :instance-rulename 4v-sexpr-alist-equiv-instancing)

  (defrefinement alist-equiv 4v-sexpr-alist-equiv
    :hints ((witness)))

  (defrefinement 4v-sexpr-alist-equiv keys-equiv
    :hints ((witness)))

  (defcong 4v-sexpr-alist-pair-equiv 4v-sexpr-alist-equiv (cons a b) 1
    :hints (("Goal" :in-theory (enable 4v-sexpr-alist-equiv
                                       4v-sexpr-alist-pair-equiv))))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-pair-equiv
    (hons-assoc-equal x al) 2
    :hints (("Goal" :in-theory (enable 4v-sexpr-alist-pair-equiv))
            (witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defthmd 4v-sexpr-equiv-cdr-hons-assoc-equal-when-4v-sexpr-alist-equiv
    (implies (and (4v-sexpr-alist-equiv a b)
                  (syntaxp (and (term-order a b) (not (equal a b)))))
             (4v-sexpr-equiv (cdr (hons-assoc-equal k a))
                             (cdr (hons-assoc-equal k b))))
    :hints (("Goal" :use ((:instance 4v-sexpr-alist-equiv-necc (x a) (y b))))))

  (defcong 4v-sexpr-alist-equiv iff (4v-sexpr-alist-<= a b) 1
    :hints(("Goal" :in-theory
            (enable
             4v-sexpr-equiv-cdr-hons-assoc-equal-when-4v-sexpr-alist-equiv))
           (witness)))

  (defcong 4v-sexpr-alist-equiv iff (4v-sexpr-alist-<= a b) 2
    :hints(("Goal" :in-theory
            (enable
             4v-sexpr-equiv-cdr-hons-assoc-equal-when-4v-sexpr-alist-equiv))
           (witness)))

  (defcong 4v-sexpr-equiv 4v-sexpr-alist-equiv (acons a b c) 2
    :hints(("Goal" :in-theory (enable 4v-sexpr-alist-equiv))))

  ;; unnecessary due to KEYS-EQUIV-IMPLIES-IFF-HONS-ASSOC-EQUAL-2
  ;; (defcong 4v-sexpr-alist-equiv iff (hons-assoc-equal x a) 2
  ;;  :hints ((Witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv (cons a b) 2
    :hints (("Goal" :expand ((4v-sexpr-alist-equiv (cons a b)
                                                   (cons a b-equiv))))
            (witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv (append a b) 1
    :hints (("goal" :do-not-induct t)
            (witness :ruleset 4v-sexpr-alist-equiv-witnessing)
            (witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv (append a b) 2
    :hints (("goal" :do-not-induct t)
            (witness :ruleset 4v-sexpr-alist-equiv-witnessing)
            (witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-alist-equiv-implies-4v-sexpr-equiv-4v-sexpr-restrict-2
      (implies (4v-sexpr-alist-equiv al1 al2)
               (4v-sexpr-equiv (4v-sexpr-restrict x al1)
                               (4v-sexpr-restrict x al2)))
      :flag sexpr
      :rule-classes :congruence)
    (defthm 4v-sexpr-alist-equiv-implies-4v-sexpr-list-equiv-4v-sexpr-restrict-list-2
      (implies (4v-sexpr-alist-equiv al1 al2)
               (4v-sexpr-list-equiv (4v-sexpr-restrict-list x al1)
                                    (4v-sexpr-restrict-list x al2)))
      :flag sexpr-list
      :rule-classes :congruence)
    :hints (("Goal" :induct (4v-sexpr-flag flag x))))

  (defcong 4v-sexpr-alist-equiv 4v-env-equiv
    (4v-sexpr-eval-alist al env) 1
    :hints (("Goal" :in-theory (disable alist-keys-4v-sexpr-eval-alist))
            (witness :ruleset 4v-env-equiv-witnessing)))

  (defcong 4v-sexpr-alist-equiv alist-equiv
    (4v-sexpr-eval-alist al env) 1
    :hints ((witness :ruleset (alist-equiv-witnessing))))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv
    (4v-sexpr-compose-alist a b) 1
    :hints ((witness :ruleset (4v-sexpr-alist-equiv-witnessing
                               4v-sexpr-alist-equiv-example))))




  (def-universal-equiv 4v-sexpr-alist-equiv-alt
    :qvars env
    :equiv-terms ((keys-equiv x)
                  (4v-env-equiv (4v-sexpr-eval-alist x env)))
    :defquant t)

  (defexample 4v-sexpr-alist-equiv-alt-eval-ex
    :pattern (4v-sexpr-eval a env)
    :templates (env)
    :instance-rulename 4v-sexpr-alist-equiv-alt-instancing)

  (defexample 4v-sexpr-alist-equiv-alt-eval-alist-ex
    :pattern (4v-sexpr-eval-alist a env)
    :templates (env)
    :instance-rulename 4v-sexpr-alist-equiv-alt-instancing)

  (encapsulate nil
    (local
     (defthm eval-to-x-when-unbound
       (implies (and (not (hons-assoc-equal k0 a))
                     (keys-equiv a b))
                (equal (equal 'x (4v-sexpr-eval (cdr (hons-assoc-equal k0 b))
                                                env))
                       t))))

    (defthmd 4v-sexpr-alist-equiv-is-alt
      (iff (4v-sexpr-alist-equiv a b)
           (4v-sexpr-alist-equiv-alt a b))
      :hints (("Goal" :do-not-induct t
               :in-theory (e/d (key-and-env-equiv)
                               (4v-sexpr-eval
                                4v-env-equiv-to-key-and-env-equiv)))
              (witness :ruleset (4v-sexpr-alist-equiv-witnessing
                                 4v-sexpr-alist-equiv-alt-witnessing))
              (witness :ruleset 4v-sexpr-equiv-witnessing)
              (witness :ruleset (4v-env-equiv-witnessing
                                 4v-sexpr-alist-equiv-alt-eval-ex))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (4v-sexpr-alist-equiv-alt
                                      key-and-env-equiv)
                                     (4v-sexpr-eval
                                      4v-env-equiv-to-key-and-env-equiv))))
              (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)
              )
      :otf-flg t))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv
    (4v-sexpr-restrict-alist a b) 1
    :hints (("Goal" :do-not-induct t)
            (witness :ruleset 4v-sexpr-alist-equiv-witnessing)
            (witness :ruleset 4v-sexpr-alist-equiv-example)))

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv
    (4v-sexpr-restrict-alist a b) 2)

  (defcong 4v-sexpr-alist-equiv 4v-sexpr-alist-equiv
    (4v-sexpr-alist-extract keys al) 2))