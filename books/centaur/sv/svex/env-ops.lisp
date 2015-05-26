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
(include-book "vars")
(local (include-book "centaur/misc/equal-sets" :dir :system))

(define svex-env-extract-aux ((keys svarlist-p) (env svex-env-p))
  :parents (svex-env-extract)
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (env1 svex-env-p)
  (if (atom keys)
      nil
    (cons (cons (svar-fix (car keys))
                (svex-env-fastlookup (car keys) env))
          (svex-env-extract-aux (cdr keys) env))))

(define svex-env-extract
  :parents (svex-env)
  :short "Restrict an @(see svex-env) to only particular variables."
  ((keys svarlist-p "Variables to keep.")
   (env  svex-env-p "Original environment to filter.  Need not be fast."))
  :returns
  (sub-env svex-env-p "Restriction of @('env') to @('keys').  Slow alist.")
  :prepwork ((local (in-theory (enable svex-env-extract-aux svarlist-fix))))
  :verify-guards nil
  (mbe :logic (if (atom keys)
                  nil
                (cons (cons (svar-fix (car keys))
                            (svex-env-fastlookup (car keys) env))
                      (svex-env-extract (cdr keys) env)))
       :exec (with-fast-alist env (svex-env-extract-aux keys env)))
  ///
  (local (defthm svex-env-extract-aux-elim
           (equal (svex-env-extract-aux keys env)
                  (svex-env-extract keys env))))

  (verify-guards svex-env-extract)

  (defthm svex-env-lookup-of-svex-env-extract
    (equal (svex-env-lookup v (svex-env-extract vars env))
           (if (member (svar-fix v) (svarlist-fix vars))
               (svex-env-lookup v env)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svarlist-fix svex-env-lookup))))

  (local (in-theory (disable svex-env-extract)))

  (defthm-svex-eval-flag
    (defthm svex-eval-extract-var-superset
      (implies (subsetp (svex-vars x) (svarlist-fix vars))
               (equal (svex-eval x (svex-env-extract vars env))
                      (svex-eval x env)))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svexlist-eval-extract-var-superset
      (implies (subsetp (svexlist-vars x) (svarlist-fix vars))
               (equal (svexlist-eval x (svex-env-extract vars env))
                      (svexlist-eval x env)))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-eval x env)))))
      :flag list))

  (defthm svex-alist-eval-of-extract-var-supserset
    (implies (subsetp (svexlist-vars (svex-alist-vals x)) (svarlist-fix vars))
             (equal (svex-alist-eval x (svex-env-extract vars env))
                    (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vals svexlist-vars))))

  (defthm alist-keys-of-svex-env-extract
    (equal (alist-keys (svex-env-extract vars env))
           (svarlist-fix vars))
    :hints(("Goal" :in-theory (enable svarlist-fix alist-keys
                                      svex-env-extract))))

  ;; for :fix hook
  (local (in-theory (enable svex-env-extract))))


(defsection svex-envs-similar
  :parents (svex-env)
  :short "@('(svex-envs-similar x y)') is like alist equivalence for @(see
svex-env)s: environments are <b>similar</b> if they bind all variables to the
same values, in the sense of @(see svex-env-lookup)."

  :long "<p>Recall that @(see svex-env-lookup) treats any unbound variables as
being bound to an infinite X vector.  Accordingly, two environments need not
have the same bound variables to be regarded as equal.</p>

<p>This is an important equivalence relation that is satisfied by, e.g., @(see
svex-eval).  It is used more than is apparent because of the congruences it
provides.</p>"

  (def-universal-equiv svex-envs-similar
    :qvars (k)
    :equiv-terms ((equal (svex-env-lookup k x)))
    :defquant t)

  (defexample svex-envs-similar-lookup-ex
    :pattern (svex-env-lookup k x)
    :templates (k)
    :instance-rulename svex-envs-similar-instancing)

  (defcong svex-envs-similar equal (svex-env-lookup k x) 2
    :hints ((witness)))

  (defthm-svex-eval-flag
    (defthm svex-eval-env-congruence
      (implies (svex-envs-similar env env2)
               (equal (svex-eval x env) (svex-eval x env2)))
      :hints ('(:expand ((:free (env) (svex-eval x env)))))
      :rule-classes :congruence
      :flag expr)
    (defthm svexlist-eval-env-congruence
      (implies (svex-envs-similar env env2)
               (equal (svexlist-eval x env) (svexlist-eval x env2)))
      :hints ('(:expand ((:free (env) (svexlist-eval x env)))))
      :rule-classes :congruence
      :flag list))

  (defcong svex-envs-similar equal (svex-alist-eval x env) 2
    :hints(("Goal" :in-theory (enable svex-alist-eval))))

  (defcong set-equiv svex-envs-similar (svex-env-extract keys env) 1
    :hints ((witness :ruleset svex-envs-similar-witnessing)))

  (defcong svex-envs-similar svex-envs-similar (svex-env-extract keys env) 2
    :hints ((witness :ruleset svex-envs-similar-witnessing)))

  (deffixcong svex-env-equiv svex-env-equiv (append a b) a)
  (deffixcong svex-env-equiv svex-env-equiv (append a b) b)

  (defrefinement svex-env-equiv svex-envs-similar
    :hints ((witness))))
