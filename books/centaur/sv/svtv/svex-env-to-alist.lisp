; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "../svex/eval")
(include-book "../svex/vars")

(defsection svex-env-to-alist
  (define svex-env-to-alist ((x svex-env-p))
    :inline t
    :returns (new-x svex-alist-p)
    :verify-guards nil
    (mbe :logic (if (atom x)
                    nil
                  (if (and (consp (car x)) (svar-p (caar x)))
                      (cons (cons (caar x) (svex-quote (cdar x)))
                            (svex-env-to-alist (cdr x)))
                    (svex-env-to-alist (cdr x))))
         :exec x)
    ///
    (local (defret <fn>-is-really-svex-env-fix
             (equal new-x (svex-env-fix x))
             :hints(("Goal" :in-theory (enable svex-env-fix svex-quote)))))

    (verify-guards svex-env-to-alist$inline
      :hints(("Goal" :in-theory (enable svex-quote))))

    (defret eval-of-<fn>
      (equal (svex-alist-eval new-x env) (svex-env-fix x))
      :hints(("Goal" :in-theory (e/d (svex-alist-eval svex-env-fix)
                                     (<fn>-is-really-svex-env-fix)))))

    (defret vars-of-<fn>
      (equal (svex-alist-vars new-x) nil)
      :hints(("Goal" :in-theory (e/d (svex-alist-vars)
                                     (<fn>-is-really-svex-env-fix))))))

  (define svex-alist-all-quotes-p ((x svex-alist-p))
    (if (atom x)
        t
      (and (or (not (mbt (and (consp (car x)) (svar-p (caar x)))))
               (svex-case (cdar x) :quote))
           (svex-alist-all-quotes-p (cdr x))))
    ///
    (local (in-theory (enable svex-alist-fix))))

  (local (defthm svex-alist-all-quotes-p-means-eval-is-identity
           (implies (svex-alist-all-quotes-p x)
                    (equal (svex-alist-eval x env)
                           (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-all-quotes-p
                                             svex-alist-eval
                                             svex-alist-fix
                                             svex-fix
                                             svex-quote->val)))))

  (define svex-alist-eval-likely-all-quotes ((x svex-alist-p) (env svex-env-p))
    :enabled t
    (mbe :logic (svex-alist-eval x env)
         :exec (if (svex-alist-all-quotes-p x)
                   x
                 (svex-alist-eval x env)))))
