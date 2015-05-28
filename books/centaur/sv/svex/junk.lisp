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


;; junk.lisp -- bozo are we using any of this?


(defalist svex-memotable :key-type svex :val-type 4vec)

(defthm 4vec-p-lookup-in-svex-memotable
  (implies (and (svex-memotable-p x)
                (hons-assoc-equal k x))
           (4vec-p (cdr (hons-assoc-equal k x)))))

(defines svex-eval-memo
  ;; Self-memoized version of svex-eval, for GL
  :verify-guards nil
  (define svex-eval-memo ((x svex-p)
                          (env svex-env-p)
                          (memo svex-memotable-p))
    :returns (mv (res 4vec-p)
                 (memo1 svex-memotable-p))
    :measure (svex-count x)
    (b* ((memo (svex-memotable-fix memo)))
      (svex-case x
        :quote (mv x.val memo)
        :var (mv (svex-env-fastlookup x.name env) memo)
        :call (b* ((x (svex-fix x))
                   (look (hons-get x memo))
                   ((when look) (mv (cdr look) memo))
                   ((mv args memo) (svexlist-eval-memo x.args env memo))
                   (res (svex-apply x.fn args))
                   (memo (hons-acons x res memo)))
                (mv res memo)))))
  (define svexlist-eval-memo ((x svexlist-p)
                              (env svex-env-p)
                              (memo svex-memotable-p))
    :returns (mv (res 4veclist-p)
                 (memo1 svex-memotable-p))
    :measure (svexlist-count x)
    (b* ((memo (svex-memotable-fix memo))
         ((when (atom x)) (mv nil memo))
         ((mv first memo) (svex-eval-memo (car x) env memo))
         ((mv rest memo) (svexlist-eval-memo (cdr x) env memo)))
      (mv (cons first rest) memo)))
  ///
  (deffixequiv-mutual svex-eval-memo)
  (verify-guards svex-eval-memo)

  (defun-sk svex-eval-memotable-ok (memo env)
    (forall x
            (implies (hons-assoc-equal x (svex-memotable-fix memo))
                     (equal (cdr (hons-assoc-equal x (svex-memotable-fix memo)))
                            (svex-eval x env))))
    :rewrite :direct)

  (in-theory (disable svex-eval-memotable-ok
                      svex-eval-memotable-ok-necc))
  (local (in-theory (enable svex-eval-memotable-ok-necc)))

  (defthm svex-eval-memotable-ok-empty
    (svex-eval-memotable-ok nil env)
    :hints(("Goal" :in-theory (enable svex-eval-memotable-ok))))

  (defthm svex-eval-memotable-ok-fix
    (implies (svex-eval-memotable-ok memo env)
             (svex-eval-memotable-ok (svex-memotable-fix memo) env))
    :hints(("Goal" :expand ((svex-eval-memotable-ok (svex-memotable-fix memo) env)))))

  (defthm svex-eval-memotable-ok-extend
    (implies (and (svex-eval-memotable-ok memo env)
                  (equal val (svex-eval x env)))
             (svex-eval-memotable-ok
              (cons (cons x val) memo) env))
    :hints (("goal" :expand ((svex-eval-memotable-ok
                              (cons (cons x (svex-eval x env)) memo) env)))))

  (local (in-theory (disable svex-eval-memo svexlist-eval-memo)))

  (defthm-svex-eval-memo-flag
    (defthm svex-eval-memo-correct
      (b* (((mv res memo1) (svex-eval-memo x env memo)))
        (implies (svex-eval-memotable-ok memo env)
                 (and (svex-eval-memotable-ok memo1 env)
                      (equal res (svex-eval x env)))))
      :hints ('(:expand ((svex-eval-memo x env memo)
                         (svex-eval x env))))
      :flag svex-eval-memo)
    (defthm svexlist-eval-memo-correct
      (b* (((mv res memo1) (svexlist-eval-memo x env memo)))
        (implies (svex-eval-memotable-ok memo env)
                 (and (svex-eval-memotable-ok memo1 env)
                      (equal res (svexlist-eval x env)))))
      :hints ('(:expand ((svexlist-eval-memo x env memo)
                         (svexlist-eval x env))))
      :flag svexlist-eval-memo)))

