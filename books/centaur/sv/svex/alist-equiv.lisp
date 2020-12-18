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
            (witness))))
