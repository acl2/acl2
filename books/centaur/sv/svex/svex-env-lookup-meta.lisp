; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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

(include-book "eval")
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(local (include-book "std/lists/sets" :dir :system))

(defevaluator svex-env-lookup-eval svex-env-lookup-eval-lst
  ((svex-env-lookup x y)
   (cons x y)
   (4vec-fix$inline x))
  :namedp t)

(local (acl2::def-ev-pseudo-term-fty-support svex-env-lookup-eval svex-env-lookup-eval-lst))

(local (in-theory (e/d (acl2::member-of-cons)
                       (symbol-listp
                        svar-p-when-member-equal-of-svarlist-p
                        svex-env-lookup-eval-of-variable))))

(local (defthm my-svex-env-lookup-of-cons
         (equal (svex-env-lookup k (cons pair rest))
                (if (and (consp pair)
                         (equal (svar-fix k) (car pair)))
                    (4vec-fix (cdr pair))
                  (svex-env-lookup k rest)))
         :hints(("Goal" :in-theory (enable svex-env-lookup)))))

(define const-svex-env-quote-vals (x)
  :returns (new-x)
  (b* (((when (atom x)) nil)
       ((unless (and (Consp (car x))
                     (svar-p (caar x))))
        (const-svex-env-quote-vals (cdr x))))
    (cons (cons (caar x) (acl2::pseudo-term-quote (cdar x)))
          (const-svex-env-quote-vals (cdr x))))
  ///
  (defthm svex-env-lookup-eval-lookup-of-const-svex-env-quote-vals
    (implies (svar-p key)
             (equal (4vec-fix
                     (svex-env-lookup-eval
                      (cdr (hons-assoc-equal key (const-svex-env-quote-vals x)))
                      a))
                    (svex-env-lookup key x)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-lookup)))))

  (defthm pseudo-termp-lookup-of-const-svex-env-quote-vals
    (pseudo-termp (cdr (hons-assoc-equal key (const-svex-env-quote-vals x))))
    :hints (("goal" :induct t))))

(define const-key-svex-env-term-parse-aux ((x pseudo-termp))
  :returns (mv ok alist)
  :measure (acl2::pseudo-term-count x)
  (acl2::pseudo-term-case x
    :const (mv t (const-svex-env-quote-vals x.val))
    :var (mv nil nil)
    :fncall (b* (((unless (eq x.fn 'cons))
                  (mv nil nil))
                 ((list car cdr) x.args)
                 ((mv first-ok first-null first-key first-val)
                  (acl2::pseudo-term-case car
                    :const (if (and (consp car.val)
                                    (svar-p (car car.val)))
                               (mv t nil (car car.val) (acl2::pseudo-term-quote (cdr car.val)))
                             (mv t t nil nil))
                    :var (mv nil nil nil nil)
                    :fncall (b* (((unless (eq car.fn 'cons))
                                  (mv nil nil nil nil))
                                 ((list caar cdar) car.args))
                              (acl2::pseudo-term-case caar
                                :const (if (svar-p caar.val)
                                           (mv t nil caar.val cdar)
                                         (mv t t nil nil))
                                :otherwise (mv nil nil nil nil)))
                    :otherwise (mv nil nil nil nil)))
                 ((unless first-ok) (mv nil nil))
                 ((when first-null)
                  (const-key-svex-env-term-parse-aux cdr))
                 ((mv cdr-ok rest) (const-key-svex-env-term-parse-aux cdr))
                 ((unless cdr-ok) (mv nil nil)))
              (mv t (cons (cons first-key first-val) rest)))
    :otherwise (mv nil nil)))

(local (defthm eval-when-const-key-svex-env-term-parse-aux
         (b* (((mv ok alist) (const-key-svex-env-term-parse-aux x)))
           (implies ok
                    (equal (svex-env-lookup key (svex-env-lookup-eval x a))
                           (4vec-fix
                            (svex-env-lookup-eval
                             (cdr (hons-get (svar-fix key) alist))
                             a)))))
         :hints(("Goal" :in-theory (e/d ((:i const-key-svex-env-term-parse-aux)))
                 :expand (const-key-svex-env-term-parse-aux x)
                 :induct t :do-not-induct t))))

(local (defthm pseudo-termp-lookup-of-const-key-svex-env-term-parse-aux
         (b* (((mv ?ok alist) (const-key-svex-env-term-parse-aux x)))
           (pseudo-termp (cdr (hons-assoc-equal (svar-fix key) alist))))
         :hints(("Goal" :in-theory (e/d ((:i const-key-svex-env-term-parse-aux)))
                 :expand (const-key-svex-env-term-parse-aux x)
                 :induct t :do-not-induct t))))

(define const-key-svex-env-term-parse ((x pseudo-termp))
  :enabled t
  (b* (((mv ok alist) (const-key-svex-env-term-parse-aux x)))
    (mv ok (make-fast-alist alist)))
  ///
  (memoize 'const-key-svex-env-term-parse))

(define svex-env-lookup-metafn ((x pseudo-termp))
  :returns (res pseudo-termp)
  (acl2::pseudo-term-case x
    :fncall (b* (((unless (eq x.fn 'svex-env-lookup))
                  (acl2::pseudo-term-fix x))
                 ((list key env) x.args)
                 ((unless (acl2::pseudo-term-case key :const))
                  (acl2::pseudo-term-fix x))
                 (key (acl2::pseudo-term-const->val key))
                 ((mv ok alist) (const-key-svex-env-term-parse env))
                 ((unless ok) (acl2::pseudo-term-fix x))
                 (look (cdr (hons-get (ec-call (svar-fix key)) alist))))
              (if look
                  (acl2::pseudo-term-fncall '4vec-fix$inline (list look))
                (acl2::pseudo-term-quote (4vec-x))))
    :otherwise (acl2::pseudo-term-fix x))
  ///
  (defthmd svex-env-lookup-meta
    (equal (svex-env-lookup-eval x a)
           (svex-env-lookup-eval (svex-env-lookup-metafn x) a))
    :rule-classes ((:meta :trigger-fns (svex-env-lookup)))))
