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

(include-book "../svex/env-ops")
(include-book "centaur/meta/variable-free" :dir :system)
(include-book "../svex/lattice")
(include-book "../svex/override")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))


(defthmd alist-keys-of-svex-env-fix-when-known-keys
  (implies (and (equal keys (alist-keys x))
                (syntaxp (quotep keys)))
           (equal (alist-keys (svex-env-fix x))
                  (svarlist-filter keys)))
  :hints(("Goal" :in-theory (enable svex-env-fix alist-keys svarlist-filter))))


(defthmd alist-keys-of-cons
  (equal (alist-keys (cons a b))
         (if (consp a)
             (cons (car a) (alist-keys b))
           (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys))))

(defthmd alist-keys-of-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys))))


(defthmd svex-env-reduce-of-known-keys
  (implies (and (syntaxp (and (not (quotep keys))
                              (cmr::term-variable-free-p keys)))
                (equal env-keys (alist-keys env))
                (syntaxp (quotep env-keys))
                (equal new-keys (acl2::hons-intersection env-keys (svarlist-fix keys)))
                (syntaxp (quotep new-keys)))
           (svex-envs-similar (svex-env-reduce keys env)
                              (svex-env-extract new-keys env)))
  :hints (("goal" :in-theory (enable svex-envs-similar))
          (and stable-under-simplificationp
               '(:in-theory (enable svex-env-lookup
                                    acl2::alist-keys-member-hons-assoc-equal)))))

;; the following are all duplicated in svtv-fsm-override
(defthmd svex-env-extract-of-cons
  (equal (svex-env-extract (cons key keys) env)
         (cons (cons (svar-fix key) (svex-env-lookup key env))
               (svex-env-extract keys env)))
  :hints(("Goal" :in-theory (enable svex-env-extract))))

(defthm svex-env-extract-of-nil
    (equal (svex-env-extract nil env) nil)
    :hints(("Goal" :in-theory (enable svex-env-extract))))


(cmr::def-force-execute hons-intersection-force-execute
  acl2::hons-intersection)


(define svex-env-<<=-each ((x svex-env-p)
                           (y svex-env-p))
  ;; Like svex-env-<<=, but iterates over the pairs in x rather than
  ;; quantifying over the keys.  So it's the same as svex-env-<<= as long as x
  ;; has no duplicate keys (or at least no duplicated keys bound to different
  ;; values).
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (svar-p (caar x)))))
             (4vec-<<= (cdar x) (svex-env-lookup (caar x) y)))
         (svex-env-<<=-each (cdr x) y)))
  ///
  (local (defthm svex-env-<<=-each-implies-4vec-<<=
           (implies (svex-env-<<=-each x y)
                    (4vec-<<= (svex-env-lookup k x)
                              (svex-env-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (defthm svex-env-<<=-each-implies-svex-env-<<=
           (implies (svex-env-<<=-each x y)
                    (svex-env-<<= x y))
           :hints(("Goal" :expand ((svex-env-<<= x y))))))

  (local (defthm svex-env-<<=-cdr-when-first-key-not-repeated
           (implies (and (or (not (consp (car x)))
                             (not (svar-p (caar x)))
                             (not (svex-env-boundp (caar x) (cdr x))))
                         (svex-env-<<= x y))
                    (svex-env-<<= (cdr x) y))
           :hints (("Goal" :expand ((svex-env-<<= (cdr x) y))
                    :use ((:instance svex-env-<<=-necc
                           (var (svex-env-<<=-witness (cdr x) y))))
                    :in-theory (e/d (svex-env-lookup
                                     svex-env-boundp)
                                    (svex-env-<<=-necc))))))

  (local (defthm svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each
           (implies (and (svex-env-<<= x y)
                         (no-duplicatesp-equal (alist-keys (svex-env-fix x))))
                    (svex-env-<<=-each x y))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup
                                           svex-env-boundp
                                           acl2::alist-keys-member-hons-assoc-equal
                                           svex-env-fix)
                                          (svex-env-<<=-necc))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance svex-env-<<=-necc
                                (var (caar x)))))))))

  (defthm svex-env-<<=-each-of-cons
    (equal (svex-env-<<=-each (cons pair x) y)
           (and (or (not (consp pair))
                    (not (svar-p (car pair)))
                    (4vec-<<= (cdr pair) (svex-env-lookup (car pair) y)))
                (svex-env-<<=-each x y))))

  (defthm svex-env-<<=-each-of-nil
    (equal (svex-env-<<=-each nil y) t))

  (local (defthm svarlist-filter-of-alist-keys
           (equal (svarlist-filter (alist-keys x))
                  (alist-keys (svex-env-fix x)))
           :hints(("Goal" :in-theory (enable svarlist-filter alist-keys svex-env-fix)))))

  (defthmd svex-env-<<=-is-svex-env-<<=-each-when-no-duplicate-keys
    (implies (and (equal keys (alist-keys x))
                  (syntaxp (quotep keys))
                  (not (acl2::hons-dups-p (svarlist-filter keys))))
             (equal (svex-env-<<= x y)
                    (svex-env-<<=-each x y)))
    :hints(("Goal" :in-theory (disable acl2::hons-dups-p
                                       svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :use (svex-env-<<=-and-no-duplicate-keys-implies-svex-env-<<=-each)
            :do-not-induct t)))

  (local (in-theory (enable svex-env-fix))))


(defthmd 4vec-<<=-when-integerp
  (implies (integerp x)
           (equal (4vec-<<= x y)
                  (equal (4vec-fix y) x)))
  :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix)))))

(defthmd svex-env-lookup-when-integerp-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (integerp (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints (("goal" :use ((:instance svex-env-<<=-necc
                         (x env1) (y env2) (var k)))
           :in-theory (e/d (4vec-<<=-when-integerp)
                           (svex-env-<<=-necc)))))



(defprod svtv-override-triple
  ((test svex-p)
   (val svex-p)
   (refvar svar-p))
  :layout :list)

(fty::defmap svtv-override-triplemap :key-type svar :val-type svtv-override-triple :true-listp t)

(fty::deflist svtv-override-triplemaplist :elt-type svtv-override-triplemap :true-listp t)

(fty::deflist svtv-override-triplelist :elt-type svtv-override-triple :true-listp t)

(define svtv-override-triplemap-to-triplelist ((x svtv-override-triplemap-p))
  :returns (triples svtv-override-triplelist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-override-triplemap-to-triplelist (cdr x))))
    (cons (svtv-override-triple-fix (cdar x))
          (svtv-override-triplemap-to-triplelist (cdr x)))))


(define svtv-override-triplemaplist-to-triplelist ((x svtv-override-triplemaplist-p))
  :returns (triples svtv-override-triplelist-p)
  (b* (((when (atom x)) nil))
    (append (svtv-override-triplemap-to-triplelist (car x))
            (svtv-override-triplemaplist-to-triplelist (cdr x)))))

(define svar-override-triple-to-svtv-override-triple ((x svar-override-triple-p))
  :returns (trip svtv-override-triple-p)
  (b* (((svar-override-triple x)))
    (make-svtv-override-triple :test (svex-var x.testvar)
                               :val (svex-var x.valvar)
                               :refvar x.refvar)))

(define svar-override-triplelist-to-svtv-override-triplelist ((x svar-override-triplelist-p))
  :returns (trips svtv-override-triplelist-p)
  (if (atom x)
      nil
    (cons (svar-override-triple-to-svtv-override-triple (car x))
          (svar-override-triplelist-to-svtv-override-triplelist (cdr x)))))


(define svtv-override-triplelist-val-alist ((x svtv-override-triplelist-p))
  (b* (((when (atom x)) nil)
       ((svtv-override-triple x1) (car x))
       ((unless (svex-case x1.val :var))
        (svtv-override-triplelist-val-alist (cdr x))))
    (cons (cons (svex-var->name x1.val) (svtv-override-triple-fix x1))
          (svtv-override-triplelist-val-alist (cdr x)))))


