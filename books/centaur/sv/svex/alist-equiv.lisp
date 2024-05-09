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
(include-book "svex-equivs")
(include-book "env-ops")
(local (include-book "std/lists/sets" :dir :system))

(defsection svex-alist-eval-equiv
  (def-universal-equiv svex-alist-eval-equiv
    :qvars (var)
    :equiv-terms ((svex-eval-equiv (svex-lookup var x))
                  (iff (svex-lookup var x)))
    :defquant t)

  (in-theory (disable svex-alist-eval-equiv svex-alist-eval-equiv-necc))

  (defexample svex-alist-eval-equiv-svex-example
    :pattern (svex-lookup var alist)
    :templates (var)
    :instance-rulename svex-alist-eval-equiv-instancing)

  (defcong svex-alist-eval-equiv svex-eval-equiv (svex-lookup var alist) 2
    :hints ((witness :ruleset (svex-alist-eval-equiv-svex-example))))

  (defcong svex-alist-eval-equiv iff (svex-lookup var alist) 2
    :hints ((witness :ruleset (svex-alist-eval-equiv-svex-example))))

  (defcong svex-alist-eval-equiv svex-envs-equivalent (svex-alist-eval alist env) 1
    :hints ((witness) (witness)))

  (defthm svex-alist-fix-under-svex-alist-eval-equiv
    (svex-alist-eval-equiv (svex-alist-fix x) x)
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

  (defcong svex-alist-eval-equiv set-equiv (svex-alist-keys x) 1
    :hints (("goal" :in-theory (enable acl2::set-unequal-witness-correct))
            (witness)))


  (defund svex-alist-eval-equiv-envs-equivalent-witness (x y)
     (b* ((key (svex-alist-eval-equiv-witness x y)))
       (svex-eval-equiv-witness (svex-lookup key x) (svex-lookup key y))))

   (defthmd svex-envs-equivalent-implies-alist-eval-equiv
     (implies (let ((env (svex-alist-eval-equiv-envs-equivalent-witness x y)))
                (svex-envs-equivalent (svex-alist-eval x env) (svex-alist-eval y env)))
              (svex-alist-eval-equiv x y))
     :hints (("goal" :in-theory (e/d (svex-alist-eval-equiv
                                      svex-eval-equiv
                                      svex-alist-eval-equiv-envs-equivalent-witness)
                                     (svex-envs-equivalent-necc))
              :use ((:instance svex-envs-equivalent-necc
                     (k (svex-alist-eval-equiv-witness x y))
                     (x (svex-alist-eval x (svex-alist-eval-equiv-envs-equivalent-witness x y)))
                     (y (svex-alist-eval y (svex-alist-eval-equiv-envs-equivalent-witness x y))))))))

   (defcong svex-alist-equiv equal (svex-alist-eval-equiv x y) 1
     :hints (("goal" :cases ((svex-alist-eval-equiv x y)))
             (witness)))

   (defcong svex-alist-equiv equal (svex-alist-eval-equiv x y) 2
     :hints (("goal" :cases ((svex-alist-eval-equiv x y)))
             (witness)))

   (defthmd svex-alist-eval-equiv-in-terms-of-envs-equivalent
     (equal (svex-alist-eval-equiv x y)
            (let ((env (svex-alist-eval-equiv-envs-equivalent-witness x y)))
             (svex-envs-equivalent (svex-alist-eval x env)
                                   (svex-alist-eval y env))))
     :hints (("goal" :cases ((svex-alist-eval-equiv x y))
              :in-theory (enable SVEX-ENVS-EQUIVALENT-IMPLIES-ALIST-EVAL-EQUIV)))
     :rule-classes ((:definition :install-body nil))))


(defsection svex-alist-eval-equiv!
  ;; Svex-alist-eval-equiv, plus keys are equal, not just set-equiv.
  (def-universal-equiv svex-alist-eval-equiv!
    :qvars (var)
    :equiv-terms ((svex-eval-equiv (svex-lookup var x))
                  (equal (svex-alist-keys x)))
    :defquant t)

  (in-theory (disable svex-alist-eval-equiv! svex-alist-eval-equiv!-necc))

  (defexample svex-alist-eval-equiv!-svex-example
    :pattern (svex-lookup var alist)
    :templates (var)
    :instance-rulename svex-alist-eval-equiv!-instancing)

  (local (defthm svex-lookup-under-iff
           (iff (svex-lookup k x)
                (member-equal (svar-fix k) (svex-alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys)))))

  (local (in-theory (disable member-svex-alist-keys)))

  (defrefinement svex-alist-eval-equiv! svex-alist-eval-equiv
    :hints((witness)))

  

  (defrefinement svex-alist-equiv svex-alist-eval-equiv!
    :hints((witness)))

  (defcong svex-alist-eval-equiv! equal (svex-alist-keys x) 1
    :hints (("goal" :in-theory (enable svex-alist-eval-equiv!))))

  (defthmd svex-alist-eval-equiv!-when-svex-alist-eval-equiv
     (implies (and (svex-alist-eval-equiv x y)
                   (equal (svex-alist-keys x) (svex-alist-keys y)))
              (equal (svex-alist-eval-equiv! x y) t))
     :hints ((witness))))

(define svex-alist-eval-equiv!! ((x svex-alist-p) (y svex-alist-p))
  ;; Svex-alist-eval-equiv, plus keys are equal and the whole list of values
  ;; are eval-equiv including shadowed ones.
  (and (ec-call (svexlist-eval-equiv (svex-alist-vals x) (svex-alist-vals y)))
       (equal (svex-alist-keys x) (svex-alist-keys y)))
  ///
  (defequiv svex-alist-eval-equiv!!)

  (local (defun ind (x x-equiv)
           (declare (xargs :measure (+ (len x) (len x-equiv))))
           (if (and (atom x) (atom x-equiv))
               (list x x-equiv)
             (if (or (atom x)
                     (and (consp (car x))
                          (svar-p (caar x))))
                 (if (or (atom x-equiv)
                         (and (consp (car x-equiv))
                              (svar-p (caar x-equiv))))
                     (ind (cdr x) (cdr x-equiv))
                   (ind x (cdr x-equiv)))
               (ind (cdr x) x-equiv)))))
  (local (defcong svex-alist-eval-equiv!! svex-eval-equiv (svex-lookup k x) 2
           :hints(("Goal" :in-theory (enable svex-lookup
                                             svex-alist-keys
                                             svex-alist-vals
                                             svexlist-eval-equiv-redef)
                   :induct (ind x x-equiv)))))

  (local (defcong svex-alist-eval-equiv!! equal (svex-alist-keys x) 1))

  (defcong svex-alist-eval-equiv!! svexlist-eval-equiv (svex-alist-vals x) 1)

  (local (defthmd svex-alist-eval-is-pairlis$
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals
                                             svex-alist-keys
                                             svexlist-eval
                                             svex-alist-eval)))))
  
  (defcong svex-alist-eval-equiv!! equal (svex-alist-eval x env) 1
    :hints(("Goal" :in-theory (enable svex-alist-eval-is-pairlis$))))
  
  (defrefinement svex-alist-eval-equiv!! svex-alist-eval-equiv!
    :hints (("goal" :expand ((svex-alist-eval-equiv! x y))
             :in-theory (disable svex-alist-eval-equiv!!)))))


(defsection svex-envlists-similar
  (def-universal-equiv svex-envlists-similar
    :qvars (n)
    :equiv-terms ((svex-envs-similar (nth n x))
                  (equal (len x)))
    :defquant t)

  (defexample svex-envlists-similar-nth-ex
    :pattern (nth n x)
    :templates (n)
    :instance-rulename svex-envlists-similar-instancing)

  (defcong svex-envlists-similar svex-envs-similar (car x) 1
    :hints (("goal" :use ((:instance svex-envlists-similar-necc (n 0) (y x-equiv))))))

  (defcong svex-envlists-similar svex-envlists-similar (cdr x) 1
    :hints (("goal" :use ((:instance svex-envlists-similar-necc
                           (n (+ (nfix (svex-envlists-similar-witness (cdr x) (cdr x-equiv))) 1))
                           (y x-equiv)))
             :expand ((:free (x y) (svex-envlists-similar (cdr x) y))
                      (:free (x y) (svex-envlists-similar y (cdr x)))))))

  (defcong svex-envlists-similar equal (len x) 1
    :hints (("goal" :in-theory (enable svex-envlists-similar))))

  (defcong svex-envlists-similar equal (consp x) 1
    :hints (("goal" :in-theory (enable svex-envlists-similar))))

  (defcong svex-envlists-similar svex-envs-similar (nth n x) 2 :hints ((witness)))

  (defcong svex-envs-similar svex-envlists-similar (cons a b) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defcong svex-envlists-similar svex-envlists-similar (cons a b) 2
    :hints ((witness :ruleset (svex-envlists-similar-witnessing))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b)))))))))


(defsection svex-envlists-equivalent
  (def-universal-equiv svex-envlists-equivalent
    :qvars (n)
    :equiv-terms ((svex-envs-equivalent (nth n x))
                  (equal (len x)))
    :defquant t)

  (defexample svex-envlists-equivalent-nth-ex
    :pattern (nth n x)
    :templates (n)
    :instance-rulename svex-envlists-equivalent-instancing)

  (defrefinement svex-envlists-equivalent svex-envlists-similar
    :hints ((witness)))


  (defcong svex-envlists-equivalent svex-envs-equivalent (car x) 1
    :hints (("goal" :use ((:instance svex-envlists-equivalent-necc (n 0) (y x-equiv))))))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cdr x) 1
    :hints (("goal" :use ((:instance svex-envlists-equivalent-necc
                           (n (+ (nfix (svex-envlists-equivalent-witness (cdr x) (cdr x-equiv))) 1))
                           (y x-equiv)))
             :expand ((:free (x y) (svex-envlists-equivalent (cdr x) y))
                      (:free (x y) (svex-envlists-equivalent y (cdr x)))))))

  (defcong svex-envlists-equivalent svex-envs-equivalent (nth n x) 2
    :hints ((witness)))

  (defthmd svex-envlists-equivalent-redef
    (equal (svex-envlists-equivalent x y)
           (if (atom x)
               (atom y)
             (and (consp y)
                  (svex-envs-equivalent (car x) (car y))
                  (svex-envlists-equivalent (cdr x) (cdr y)))))
    :hints (("goal" :cases ((svex-envlists-equivalent x y)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc-equal 'svex-envlists-equivalent clause)))
                   `(:expand (,lit
                              (:free (n) (nth n x))
                              (:free (n) (nth n y)))))))
    :rule-classes ((:definition :install-body nil))))



(define svex-identity-subst ((x svarlist-p))
  :returns (subst svex-alist-p)
  (pairlis$ (svarlist-fix x) (svarlist->svexes x))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst) (svarlist-fix x)))

  (local (defthm nth-of-svarlist->svexes
           (equal (nth n (svarlist->svexes x))
                  (and (< (nfix n) (len x))
                       (svex-var (nth n x))))
           :hints(("Goal" :in-theory (enable svarlist->svexes nth)))))


  (local (defthm hons-assoc-equal-of-pairlis
           (equal (hons-assoc-equal var (pairlis$ (svarlist-fix x)
                                                  (svarlist->svexes x)))
                  (and (member-equal var (svarlist-fix x))
                       (cons var (svex-var var))))
           :hints(("Goal" :in-theory (enable pairlis$ svarlist-fix svarlist->svexes)))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup var subst)
           (and (member-equal (svar-fix var) (svarlist-fix x))
                (svex-var var)))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (len) ;; svarlist-fix svarlist->svexes
                                   ))))

  (local (include-book "std/lists/sets" :dir :system))

  (local
   (deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil))

  (defcong set-equiv svex-alist-eval-equiv (svex-identity-subst x) 1
    :hints (("goal" :in-theory (disable set-equiv svex-identity-subst))
            (witness)))

  (defthm svex-alist-eval-of-svex-identity-subst
    (equal (svex-alist-eval (svex-identity-subst vars) env)
           (svex-env-extract vars env))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-extract pairlis$ svarlist-fix svarlist->svexes svex-eval)))))


(define svex-compose-lookup ((var svar-p)
                             (x svex-alist-p))
  :returns (look svex-p)
  :hooks (:fix)
  ;; Looks up var in x
  (or (svex-lookup var x)
      (svex-var var)))

(defsection svex-alist-compose-equiv
  (def-universal-equiv svex-alist-compose-equiv
    :qvars (var)
    :equiv-terms ((svex-eval-equiv (svex-compose-lookup var x)))
    :defquant t)

  (in-theory (disable svex-alist-compose-equiv svex-alist-compose-equiv-necc))

  (defexample svex-alist-compose-equiv-svex-compose-lookup-example
    :pattern (svex-compose-lookup var alist)
    :templates (var)
    :instance-rulename svex-alist-compose-equiv-instancing)

  (defrefinement svex-alist-eval-equiv svex-alist-compose-equiv
    :hints(("Goal" :in-theory (enable svex-alist-compose-equiv svex-compose-lookup))))

  (defthm svex-envs-similar-append-when-svex-alist-compose-equiv
    (implies (svex-alist-compose-equiv x y)
             (svex-envs-similar (append (svex-alist-eval x env) env)
                                (append (svex-alist-eval y env) env)))
    :hints(("Goal" :in-theory (enable svex-envs-similar svex-compose-lookup)
            :use ((:instance svex-alist-compose-equiv-necc
                   (var (svex-envs-similar-witness
                         (append (svex-alist-eval x env) env)
                                (append (svex-alist-eval y env) env)))))
            :expand ((:free (x) (svex-eval (svex-var x) env)))))
    :rule-classes nil)

  (defthm svex-alist-compose-equiv-of-svex-identity-subst
    (svex-alist-compose-equiv (svex-identity-subst vars) nil)
    :hints(("Goal" :in-theory (enable svex-alist-compose-equiv
                                      svex-compose-lookup))))

  (defcong svex-alist-compose-equiv svex-eval-equiv (svex-compose-lookup var x) 2
    :hints((witness))))




(local (defthmd hons-assoc-equal-iff-member-alist-keys
         (iff (hons-assoc-equal k a)
              (member-equal k (alist-keys a)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(defsection svex-alist-keys-equiv
  (def-universal-equiv svex-alist-keys-equiv
    :qvars ()
    :equiv-terms ((set-equiv (svex-alist-keys x))))

  (local (defthmd svex-lookup-under-iff
           (iff (svex-lookup k a)
                (hons-assoc-equal (svar-fix k) (svex-alist-fix a)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (local (defthmd svex-alist-keys-is-alist-keys-of-svex-alist-fix
           (equal (svex-alist-keys x)
                  (alist-keys (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-fix alist-keys)))))



  (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-1
           (implies (and (svex-lookup var a)
                         (not (svex-lookup var b)))
                    (not (set-equiv (svex-alist-keys a)
                                    (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-alist-fix))))))

  (local (defthm svex-alist-keys-not-set-equiv-by-svex-lookup-2
           (implies (and (svex-lookup var b)
                         (not (svex-lookup var a)))
                    (not (set-equiv (svex-alist-keys a)
                                    (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-lookup-under-iff
                                           svex-alist-keys-is-alist-keys-of-svex-alist-fix
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-alist-fix))))))

  

  (defthmd svex-lookup-iff-member-svex-alist-keys
    (iff (svex-lookup k x)
         (member-equal (svar-fix k) (svex-alist-keys x))))

  
  (defcong svex-alist-keys-equiv iff (svex-lookup var x) 2
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv))))

  (defthm set-equiv-forward-to-svex-alist-keys-equiv
    (implies (set-equiv (svex-alist-keys x) (svex-alist-keys y))
             (svex-alist-keys-equiv x y))
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv)))
    :rule-classes :forward-chaining)

  

  (defthm equal-svex-alist-keys-forward-to-svex-alist-keys-equiv
    (implies (equal (svex-alist-keys x) (svex-alist-keys y))
             (svex-alist-keys-equiv x y))
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv)))
    :rule-classes :forward-chaining)

  (defrefinement svex-alist-eval-equiv svex-alist-keys-equiv
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                      svex-alist-keys-equiv))))

  (encapsulate
    (((svex-alist-keys-equiv-lookup-witness * *) => *))
    (local (defun svex-alist-keys-equiv-lookup-witness (x y)
             (svar-fix (acl2::set-unequal-witness (svex-alist-keys x)
                                                  (svex-alist-keys y)))))
    (defthm svar-p-of-svex-alist-keys-equiv-lookup-witness
      (svar-p (svex-alist-keys-equiv-lookup-witness x y)))
           
    (defthmd svex-alist-keys-equiv-in-terms-of-lookup
      (equal (svex-alist-keys-equiv x y)
             (let ((var (svex-alist-keys-equiv-lookup-witness x y)))
               (iff (svex-lookup var x) (svex-lookup var y))))
      :hints(("Goal" :in-theory (e/d (svex-alist-keys-equiv)))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (acl2::set-unequal-witness-correct
                                     svex-alist-keys-equiv-lookup-witness
                                     svex-lookup-iff-member-svex-alist-keys)
                                    (member-svex-alist-keys)))))
      :rule-classes ((:definition :install-body nil))))

  (defcong svex-alist-keys-equiv set-equiv (svex-alist-keys x) 1
    :hints(("Goal" :in-theory (enable svex-alist-keys-equiv))))
  )


(defsection svex-env-keys-equiv
  (def-universal-equiv svex-env-keys-equiv
    :qvars ()
    :equiv-terms ((set-equiv (alist-keys (svex-env-fix x)))))

  (local (defthmd svex-env-boundp-under-iff
           (iff (svex-env-boundp k a)
                (hons-assoc-equal (svar-fix k) (svex-env-fix a)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))


  (local (defthm svex-env-keys-not-set-equiv-by-svex-env-boundp-1
           (implies (and (svex-env-boundp var a)
                         (not (svex-env-boundp var b)))
                    (not (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b)))))
           :hints(("Goal" :in-theory (e/d (svex-env-boundp-under-iff
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-env-fix))))))

  (local (defthm svex-env-keys-not-set-equiv-by-svex-env-boundp-2
           (implies (and (svex-env-boundp var b)
                         (not (svex-env-boundp var a)))
                    (not (set-equiv (alist-keys (svex-env-fix a))
                                    (alist-keys (svex-env-fix b)))))
           :hints(("Goal" :in-theory (e/d (svex-env-boundp-under-iff
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (hons-assoc-equal-of-svex-env-fix))))))

  (defcong svex-env-keys-equiv iff (svex-env-boundp var x) 2
    :hints(("Goal" :in-theory (enable svex-env-keys-equiv))))

  (defthm equal-svex-env-keys-forward-to-svex-env-keys-equiv
    (implies (equal (alist-keys (svex-env-fix x))
                    (alist-keys (svex-env-fix y)))
             (svex-env-keys-equiv x y))
    :hints(("Goal" :in-theory (enable svex-env-keys-equiv)))
    :rule-classes :forward-chaining)

  ;; (defthmd svex-alist-keys-equiv-iff-svex-alist-keys-set-equiv
  ;;   (iff (svex-alist-keys-equiv x y)
  ;;        (set-equiv (svex-alist-keys x) (svex-alist-keys y))))
  )
