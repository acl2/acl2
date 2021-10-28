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

(defsection svex-eval-equiv
  (def-universal-equiv svex-eval-equiv
    :qvars (env)
    :equiv-terms ((equal (svex-eval x env)))
    :defquant t)

  (in-theory (disable svex-eval-equiv svex-eval-equiv-necc))

  (defexample svex-eval-equiv-svex-example
    :pattern (svex-eval x env)
    :templates (env)
    :instance-rulename svex-eval-equiv-instancing)

  (defexample svex-eval-equiv-list-example
    :pattern (svexlist-eval x env)
    :templates (env)
    :instance-rulename svex-eval-equiv-instancing)

  (defcong svex-eval-equiv equal (svex-eval x env) 1
    :hints ((witness :ruleset (svex-eval-equiv-instancing
                                     svex-eval-equiv-svex-example))))

  (defrefinement svex-equiv svex-eval-equiv
    :hints ((witness :ruleset (svex-eval-equiv-witnessing)))))

(defsection svexlist-eval-equiv
  (def-universal-equiv svexlist-eval-equiv
    :qvars (env)
    :equiv-terms ((equal (svexlist-eval x env)))
    :defquant t)

  (in-theory (disable svexlist-eval-equiv svexlist-eval-equiv-necc))

  (defexample svexlist-eval-equiv-svex-example
    :pattern (svex-eval x env)
    :templates (env)
    :instance-rulename svexlist-eval-equiv-instancing)

  (defexample svexlist-eval-equiv-list-example
    :pattern (svexlist-eval x env)
    :templates (env)
    :instance-rulename svexlist-eval-equiv-instancing)

  (defcong svexlist-eval-equiv equal (svexlist-eval x env) 1
    :hints ((witness :ruleset (svexlist-eval-equiv-instancing
                                     svexlist-eval-equiv-list-example))))

  (defrefinement svexlist-equiv svexlist-eval-equiv
    :hints ((witness :ruleset (svexlist-eval-equiv-witnessing))))

  (defcong svexlist-eval-equiv svex-eval-equiv (car x) 1
    :hints (("goal" :expand ((:free (env) (svexlist-eval x env))
                             (:free (env) (svexlist-eval x-equiv env))))
            (witness :ruleset (svex-eval-equiv-witnessing
                                     svexlist-eval-equiv-instancing
                                     svexlist-eval-equiv-svex-example))))

  (defcong svexlist-eval-equiv svexlist-eval-equiv (cdr x) 1
    :hints (("goal" :expand ((:free (env) (svexlist-eval x env))
                             (:free (env) (svexlist-eval x-equiv env))))
            (witness :ruleset (svexlist-eval-equiv-witnessing
                                     svexlist-eval-equiv-instancing
                                     svexlist-eval-equiv-list-example))))

  (defcong svexlist-eval-equiv svexlist-eval-equiv (cons x y) 2
    :hints (("goal" :in-theory (enable svexlist-eval))
            (witness :ruleset (svexlist-eval-equiv-witnessing
                                     svexlist-eval-equiv-instancing
                                     svexlist-eval-equiv-list-example))))

  (defcong svex-eval-equiv svexlist-eval-equiv (cons x y) 1
    :hints (("goal" :in-theory (enable svexlist-eval))
            (witness :ruleset (svexlist-eval-equiv-witnessing
                                     svex-eval-equiv-instancing
                                     svex-eval-equiv-list-example))))

  (defcong svexlist-eval-equiv svex-eval-equiv (svex-call fn args) 2
    :hints (("goal" :expand ((:free (fn args env)
                              (svex-eval (svex-call fn args) env))))
            (witness))))
