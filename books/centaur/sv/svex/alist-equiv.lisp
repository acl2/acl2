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


(defthm svex-env-boundp-of-svex-alist-eval
  (iff (svex-env-boundp k (svex-alist-eval al env))
       (svex-lookup k al))
  :hints(("Goal" :in-theory (enable svex-env-boundp svex-lookup svex-alist-eval))))

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
             (witness))))


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
