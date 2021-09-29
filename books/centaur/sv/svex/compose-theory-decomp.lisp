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
(include-book "compose-theory-base")
(include-book "rewrite-base")
;; (local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (std::add-default-post-define-hook :fix))


(deftagsum svar-decomp
  (:segment ((width posp :rule-classes :type-prescription)
             (var svar-p)
             (rest svar-decomp-p)))
  (:remainder ((var svar-p))))



(fty::defmap svar-decomptable :key-type svar :val-type svar-decomp :true-listp t)



(define svar-decomp-vars ((x svar-decomp-p))
  :measure (svar-decomp-count x)
  :returns (vars svarlist-p)
  (svar-decomp-case x
    :segment (cons x.var (svar-decomp-vars x.rest))
    :remainder (list x.var)))

(define svar-decomptable-vars ((x svar-decomptable-p))
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-vars (cdr x))))
    (append (svar-decomp-vars (cdar x))
            (svar-decomptable-vars (cdr x))))
  ///
  (local (in-theory (enable svar-decomptable-fix))))

(define svar-decomp-eval ((x svar-decomp-p)
                          (env svex-env-p))
  :returns (val 4vec-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (4vec-concat
              (2vec x.width)
              (svex-env-lookup x.var env)
              (svar-decomp-eval x.rest env))
    :remainder (svex-env-lookup x.var env))
  ///
  (defthm svar-decomp-eval-of-acons-non-member
    (implies (not (member-equal (svar-fix var) (svar-decomp-vars x)))
             (equal (svar-decomp-eval x (svex-env-acons var val rest))
                    (svar-decomp-eval x rest)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomp-eval-of-append-superset
    (implies (subsetp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env1)))
             (equal (svar-decomp-eval x (append env1 env2))
                    (svar-decomp-eval x env1)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-boundp))))

  (defthm svar-decomp-eval-of-append-non-intersecting
    (implies (not (intersectp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env1))))
             (equal (svar-decomp-eval x (append env1 env2))
                    (svar-decomp-eval x env2)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-boundp))))

  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env)))
             (equal (svar-decomp-eval x (append env env2))
                    val))
    :hints(("Goal" :in-theory (enable svar-decomp-vars)))))

(define svar-decomptable-eval ((x svar-decomptable-p)
                               (env svex-env-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-eval (cdr x) env)))
    (svex-env-acons (caar x) (svar-decomp-eval (cdar x) env)
                    (svar-decomptable-eval (cdr x) env)))
  ///
  (defthm svar-decomptable-eval-of-acons-non-member
    (implies (not (member-equal (svar-fix var) (svar-decomptable-vars x)))
             (equal (svar-decomptable-eval x (svex-env-acons var val rest))
                    (svar-decomptable-eval x rest)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-eval-of-append-superset
    (implies (subsetp-equal (svar-decomptable-vars x) (alist-keys (svex-env-fix env1)))
             (equal (svar-decomptable-eval x (append env1 env2))
                    (svar-decomptable-eval x env1)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars svex-env-boundp))))

  (defthm svar-decomptable-eval-of-append-non-intersecting
    (implies (not (intersectp-equal (svar-decomptable-vars x) (alist-keys (svex-env-fix env1))))
             (equal (svar-decomptable-eval x (append env1 env2))
                    (svar-decomptable-eval x env2)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars svex-env-boundp))))

  (local (in-theory (enable svar-decomptable-fix))))


(define svar-decomp-shift ((offset natp) (x svar-decomp-p))
  ;; NOTE: returns NIL if the offset does not corrspond with a particular slice of x.
  :returns (new-x (iff (svar-decomp-p new-x) new-x))
  :measure (svar-decomp-count x)
  (if (zp offset)
      (svar-decomp-fix x)
    (svar-decomp-case x
      :segment (if (< (lnfix offset) x.width)
                   nil
                 (svar-decomp-shift (- (lnfix offset) x.width) x.rest))
      :remainder nil))
  ///
  (defret eval-of-<fn>
    (implies new-x
             (equal (svar-decomp-eval new-x env)
                    (4vec-rsh (2vec (nfix offset)) (svar-decomp-eval x env))))
    :hints(("Goal" :induct <call>
            :expand ((svar-decomp-eval x env)))))

  (defret rest-of-<fn>
    (implies (and new-x
                  (svar-decomp-case new-x :segment))
             (and (equal (svar-decomp-segment->rest new-x)
                         (svar-decomp-shift (+ (nfix offset)
                                               (svar-decomp-segment->width new-x))
                                            x))
                  (svar-decomp-shift (+ (nfix offset)
                                        (svar-decomp-segment->width new-x))
                                     x))))

  (defret <fn>-var-member-vars-segment
    (implies (and new-x
                  (svar-decomp-case new-x :segment))
             (member-equal (svar-decomp-segment->var new-x) (svar-decomp-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars))))

  (defret <fn>-var-member-vars-remainder
    (implies (and new-x
                  (svar-decomp-case new-x :remainder))
             (member-equal (svar-decomp-remainder->var new-x) (svar-decomp-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars)))))

(define svar-decomp-var-offset ((var svar-p) (x svar-decomp-p))
  :returns (offset natp :rule-classes :type-prescription)
  :measure (svar-decomp-count x)
  (svar-decomp-case x
    :segment (if (equal (svar-fix var) x.var)
                 0
               (+ x.width (svar-decomp-var-offset var x.rest)))
    :remainder 0)
  ///
  (defthm svar-decomp-var-offset-of-svar-decomp-shift-segment
    (let ((shift (svar-decomp-shift offset x)))
      (implies (and shift
                    (svar-decomp-case shift :segment)
                    (no-duplicatesp-equal (svar-decomp-vars x)))
               (equal (svar-decomp-var-offset (svar-decomp-segment->var shift) x)
                      (nfix offset))))
    :hints(("Goal" :in-theory (enable svar-decomp-shift svar-decomp-vars)
            :induct (svar-decomp-shift offset x))
           (and stable-under-simplificationp
                '(:use ((:instance svar-decomp-shift-var-member-vars-segment
                         (offset (+ offset (- (svar-decomp-segment->width x))))
                         (x (svar-decomp-segment->rest x))))
                  :in-theory (disable svar-decomp-shift-var-member-vars-segment)))))

  (defthm svar-decomp-var-offset-of-svar-decomp-shift-remainder
    (let ((shift (svar-decomp-shift offset x)))
      (implies (and shift
                    (svar-decomp-case shift :remainder)
                    (no-duplicatesp-equal (svar-decomp-vars x)))
               (equal (svar-decomp-var-offset (svar-decomp-remainder->var shift) x)
                      (nfix offset))))
    :hints(("Goal" :in-theory (enable svar-decomp-shift svar-decomp-vars)
            :induct (svar-decomp-shift offset x))
           (and stable-under-simplificationp
                '(:use ((:instance svar-decomp-shift-var-member-vars-remainder
                         (offset (+ offset (- (svar-decomp-segment->width x))))
                         (x (svar-decomp-segment->rest x))))
                  :in-theory (disable svar-decomp-shift-var-member-vars-remainder)))))

  (defthm svar-decomp-shift-of-var-offset-under-iff
    (svar-decomp-shift (svar-decomp-var-offset var x) x)
    :hints(("Goal" :in-theory (enable svar-decomp-shift))))

  (defthm var-of-svar-decomp-shift-of-offset-when-segment
    (let ((shift (svar-decomp-shift (svar-decomp-var-offset var x) x)))
      (implies (svar-decomp-case shift :segment)
               (equal (svar-decomp-segment->var shift) (svar-fix var))))
    :hints(("Goal" :in-theory (enable svar-decomp-shift))))

  (defthm var-of-svar-decomp-shift-of-offset-when-remainder
    (let ((shift (svar-decomp-shift (svar-decomp-var-offset var x) x)))
      (implies (and (svar-decomp-case shift :remainder)
                    (member-equal (svar-fix var) (svar-decomp-vars x)))
               (equal (svar-decomp-remainder->var shift) (svar-fix var))))
    :hints(("Goal" :in-theory (enable svar-decomp-shift svar-decomp-vars)))))

(define svar-decomp->svex ((x svar-decomp-p))
  :returns (svex svex-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (svcall concat
                     (svex-quote (2vec x.width))
                     (svex-var x.var)
                     (svar-decomp->svex x.rest))
    :remainder (svex-var x.var))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval svex env)
           (svar-decomp-eval x env))
    :hints(("Goal" :in-theory (enable svar-decomp-eval svex-apply)
            :expand ((:free (x) (svex-eval (svex-var x) env))))))

  (defret svex-vars-of-<fn>
    (set-equiv (svex-vars svex)
               (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svex-vars svar-decomp-vars)))))


(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(define svar-decomptable->subst ((x svar-decomptable-p))
  :returns (subst svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable->subst (cdr x))))
    (cons (cons (caar x) (svar-decomp->svex (cdar x)))
          (svar-decomptable->subst (cdr x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svar-decomptable-eval x env))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval
                                      svex-env-acons
                                      svex-alist-eval)
            :induct t)))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst)
           (alist-keys (svar-decomptable-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys svar-decomptable-fix alist-keys))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup v subst)
           (b* ((look (hons-assoc-equal (svar-fix v) x)))
             (and look
                  (svar-decomp->svex (cdr look))))))

  (local (in-theory (enable svar-decomptable-fix)))

  (defret svex-alist-vars-of-<fn>
    (set-equiv (svex-alist-vars subst)
               (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svex-alist-vars svar-decomptable-vars)))))


(define svar-decomptable-find-domainvar ((key svar-p)
                                         (x svar-decomptable-p))
  :returns (domainvar (iff (svar-p domainvar) domainvar))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-find-domainvar key (cdr x))))
    (if (member-equal (svar-fix key) (svar-decomp-vars (cdar x)))
        (caar x)
      (svar-decomptable-find-domainvar key (cdr x))))
  ///
  (local (in-theory (enable svar-decomptable-vars)))
  (defret <fn>-under-iff
    (iff domainvar
         (member-equal (svar-fix key) (svar-decomptable-vars x))))

  (defret lookup-exists-of-<fn>
    (implies domainvar
             (hons-assoc-equal domainvar x)))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret member-svar-decomp-vars-of-<fn>
    (implies (and (equal key1 (svar-fix key))
                  domainvar
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (member-equal key1 (svar-decomp-vars
                                 (cdr (hons-assoc-equal domainvar x)))))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys))))

  (local (defthm intersectp-when-member-both
           (implies (and (member-equal k y)
                         (member-equal k x))
                    (intersectp-equal x y))))

  (local (defthm member-svar-decomptable-vars-when-member-svar-decomp-vars-of-lookup
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         (member-equal key
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp)))))
                    (member-equal key (svar-decomptable-vars decomp)))
           :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

  (defret member-svar-decomp-vars-of-<fn>-when-no-duplicate-vars
    (implies (and (svar-p key)
                  (hons-assoc-equal var (svar-decomptable-fix x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x)))
                  (no-duplicatesp-equal (svar-decomptable-vars x)))
             (iff (member-equal key (svar-decomp-vars
                                      (cdr (hons-assoc-equal var x))))
                  (and domainvar
                       (equal var domainvar))))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys)
            :induct <call>
            :expand ((svar-decomptable-vars x)))))


  (local (in-theory (enable svar-decomptable-fix))))

(define svar-decomp-extract ((x svar-decomp-p)
                             (env svex-env-p))
  :returns (new-env svex-env-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (svex-env-acons x.var (4vec-zero-ext
                                    (2vec x.width)
                                    (svex-env-lookup x.var env))
                             (svar-decomp-extract x.rest env))
    :remainder (svex-env-acons x.var (svex-env-lookup x.var env) nil))
  ///
  (local (defthm 4vec-concat-of-4vec-zero-ext
           (equal (4vec-concat w (4vec-zero-ext w x) y)
                  (4vec-concat w x y))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext)))))

  (defret svar-decomp-eval-of-<fn>
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal (svar-decomp-eval x new-env)
                    (svar-decomp-eval x env)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval svar-decomp-vars))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys (svar-decomp-extract x env))
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-acons alist-keys)))))

(define svar-decomp-lookup ((key svar-p)
                            (x svar-decomp-p)
                            (position natp)
                            (val 4vec-p))
  :measure (svar-decomp-count x)
  :returns (new-val (iff (4vec-p new-val) new-val))
  (svar-decomp-case x
    :segment (if (equal (svar-fix key) x.var)
                 (4vec-part-select (2vec (lnfix position))
                                   (2vec x.width)
                                   val)
               (svar-decomp-lookup key x.rest (+ x.width (lnfix position)) val))
    :remainder (and (equal (svar-fix key) x.var)
                    (4vec-rsh (2vec (lnfix position)) val)))
  ///
  (defret <fn>-under-iff
    (iff new-val (member-equal (svar-fix key) (svar-decomp-vars x)))
    :hints(("Goal" 
            :induct <call>
            :expand ((svar-decomp-vars x)))))

  (defret <fn>-in-terms-of-var-offset
    (implies (member-equal (Svar-fix key) (svar-decomp-vars x))
             
             (equal new-val
                    (let* ((offset (svar-decomp-var-offset key x))
                           (shift (svar-decomp-shift offset x)))
                      (svar-decomp-case shift
                        :segment
                        (4vec-part-select (2vec (+ (nfix position) offset))
                                          (2vec shift.width)
                                          val)
                        :remainder (4vec-rsh (2vec (+ (nfix position) offset)) val)))))
    :hints(("Goal" :in-theory (enable svar-decomp-var-offset
                                      svar-decomp-shift
                                      svar-decomp-vars)))))

(define svar-decomp-inverse-env ((x svar-decomp-p)
                                 (position natp)
                                 (val 4vec-p))
  :measure (svar-decomp-count x)
  :returns (env svex-env-p)
  :verify-guards :after-returns
  :prepwork ()
  (svar-decomp-case x
    :segment (svex-env-acons x.var (4vec-part-select
                                    (2vec (lnfix position))
                                    (2vec x.width)
                                    val)
                             (svar-decomp-inverse-env x.rest
                                                      (+ x.width (lnfix position))
                                                      val))
    :remainder (svex-env-acons x.var (4vec-rsh (2vec (lnfix position)) val) nil))
  ///
  (local (defthm concat-part-select-rsh
           (implies (and (natp pos)
                         (natp w))
                    (equal (4vec-concat (2vec w) (4vec-part-select (2vec pos) (2vec w) val) (4vec-rsh (2vec (+ pos w)) val))
                           (4vec-rsh (2vec pos) val)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-part-select 4vec-rsh 4vec-zero-ext 4vec-shift-core))
                  (bitops::logbitp-reasoning))))

  (defret svar-decomp-eval-with-<fn>
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal (svar-decomp-eval x env)
                    (4vec-rsh (2vec (lnfix position)) val)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval no-duplicatesp-equal svar-decomp-vars))))

  (local (defthm concat-of-part-select
           (implies (and (natp width)
                         (integerp position)
                         (<= width position))
                    (equal (4vec-part-select (2vec position) (2vec width1) (4vec-concat (2vec width) val1 val2))
                           (4vec-part-select (2vec (- position width)) (2vec width1) val2)))
           :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-concat 4vec-zero-ext 4vec-shift-core 4vec-rsh)))))
                           
           

  (defthm svar-decomp-inverse-env-of-concat
    (implies (and (natp width)
                  (integerp position)
                  (<= width position))
             (equal (svar-decomp-inverse-env x position (4vec-concat (2vec width) val1 val2))
                    (svar-decomp-inverse-env x (- position width) val2))))
           
  (local (defthm equal-of-4vec-concat-strong
           (implies (natp w)
                    (equal (equal val (4vec-concat (2vec w) val1 val2))
                           (and (4vec-p val)
                                (equal (4vec-zero-ext (2vec w) val)
                                       (4vec-zero-ext (2vec w) val1))
                                (equal (4vec-rsh (2vec w) val)
                                       (4vec-fix val2)))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext 4vec-shift-core 4vec-rsh))
                  (bitops::logbitp-reasoning))))
                                        

  (defret <fn>-of-svar-decomp-eval
    ;; :pre-bind ((val (svar-decomp-eval x env1)))
    (implies (and (no-duplicatesp-equal (svar-decomp-vars x))
                  (equal (4vec-rsh (2vec (nfix position)) val)
                         (svar-decomp-eval x env1)))
             (equal env (svar-decomp-extract x env1)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval no-duplicatesp-equal svar-decomp-vars
                                      svar-decomp-extract)
            :induct <call>
            :expand ((:free (val) <call>)))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-acons 4vec-part-select)))))

  (defret <fn>-of-svar-decomp-eval-0
    :pre-bind ((val (svar-decomp-eval x env1))
               (position 0))
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal env (svar-decomp-extract x env1)))
    :hints (("goal" :use ((:instance <fn>-of-svar-decomp-eval
                           (position 0)
                           (val (svar-decomp-eval x env1)))))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys env)
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars alist-keys svex-env-acons))))

  (defret lookup-in-<fn>
    (equal (svex-env-lookup key env)
           (if (member-equal (svar-fix key) (svar-decomp-vars x))
               (svar-decomp-lookup key x position val)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svar-decomp-lookup
                                      svar-decomp-vars
                                      svar-decomp-var-offset
                                      svar-decomp-shift)))))


(define svar-decomp->inverse ((x svar-decomp-p)
                              (position natp)
                              (val svex-p))
  :returns (alist svex-alist-p)
  :measure (svar-decomp-count x)
  (svar-decomp-case x
    :segment (cons (cons x.var (svcall partsel
                                       (svex-quote (2vec (lnfix position)))
                                       (svex-quote (2vec x.width))
                                       val))
                   (svar-decomp->inverse x.rest
                                         (+ x.width (lnfix position))
                                         val))
    :remainder (list (cons x.var (svcall rsh (svex-quote (2vec (lnfix position))) val))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svar-decomp-inverse-env x position (svex-eval val env)))
    :hints(("Goal" :in-theory (enable svar-decomp-inverse-env svex-apply svex-alist-eval
                                      svex-env-acons))))

  (defthm svar-decomp-svex-of-inverse
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (svex-eval-equiv (svex-compose (svar-decomp->svex x) (svar-decomp->inverse x position val))
                              (svcall rsh (svex-quote (2vec (nfix position))) val)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply))))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup key alist)
         (member-equal (svar-fix key) (svar-decomp-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars))))
  
  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key alist) env)
           (if (member-equal (svar-fix key) (svar-decomp-vars x))
               (svar-decomp-lookup key x position (svex-eval val env))
             (4vec-x)))
    :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                           (k key)
                           (x alist)))
             :in-theory (disable svex-env-lookup-of-svex-alist-eval)
             :do-not-induct t))
    :hints-sub-returnnames t)

  (local (Defthm cdr-hons-assoc-equal-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (local (defthm svar-p-when-lookup-in-svex-alist
           (implies (and (hons-assoc-equal k x)
                         (svex-alist-p x))
                    (svar-p k))))

  (defret hons-assoc-equal-of-<fn>
    (iff (hons-assoc-equal key alist)
         (and (svar-p key)
              (member-equal key (svar-decomp-vars x))))
    :hints (("goal" :use svex-lookup-under-iff-of-<fn>
             :in-theory (e/d (svex-lookup)
                             (svex-lookup-under-iff-of-<fn>))
             :do-not-induct t)))

  (local (defthm not-hons-assoc-equal-when-not-svar-p
           (implies (and (svex-alist-p x)
                         (not (svar-p k)))
                    (not (hons-assoc-equal k x)))))
  

  (defret svex-eval-cdr-hons-assoc-equal-of-<fn>
    (equal (svex-eval (cdr (hons-assoc-equal key alist)) env)
           (if (and (svar-p key)
                    (member-equal key (svar-decomp-vars x)))
               (svar-decomp-lookup key x position (svex-eval val env))
             (4vec-x)))
    :hints (("goal" :use eval-lookup-of-<fn>
             :in-theory (e/d (svex-lookup)
                             (eval-lookup-of-<fn>))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((svar-p key))))))

  (local (defthm 4vec-part-select-in-terms-of-concat
           (implies (and (natp lsb) (natp width))
                    (Equal (4vec-part-select (2vec lsb) (2vec width) in)
                           (4vec-concat (2vec width) (4vec-rsh (2vec lsb) in) 0)))
           :hints(("Goal" :in-theory (enable 4vec-part-select
                                             4vec-concat
                                             4vec-rsh
                                             4vec-shift-core
                                             4vec-zero-ext)))))

  (defretd svex-lookup-of-<fn>-under-svex-eval-equiv
    (implies (member-equal (svar-fix key) (svar-decomp-vars x))
             (svex-eval-equiv (svex-lookup key alist)
                              (b* ((offset (svar-decomp-var-offset key x))
                                   (shift (svar-decomp-shift offset x)))
                                (svar-decomp-case shift
                                  :segment (svex-concat
                                            shift.width
                                            (svex-rsh (+ (nfix position) offset) val)
                                            0)
                                  :remainder (svex-rsh (+ (nfix position) offset) val)))))
    :hints(("Goal" :in-theory (e/d (svex-eval-equiv svex-apply 4vec-part-select 4vec-zero-ext)
                                   (<fn>)))))
                              

  (defret svex-alist-keys-of-<fn>
    (equal (Svex-alist-keys alist)
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-alist-keys)))))

(define svar-decomptable-lookup ((key svar-p)
                                 (x svar-decomptable-p)
                                 (env svex-env-p))
  :returns (new-val (iff (4vec-p new-val) new-val))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-lookup key (cdr x) env)))
    (or (svar-decomp-lookup key (cdar x) 0 (svex-env-lookup (caar x) env))
        (svar-decomptable-lookup key (cdr x) env)))
  ///
  (defret <fn>-under-iff
    (iff new-val (member-equal (svar-fix key) (svar-decomptable-vars x)))
    :hints(("Goal" 
            :induct <call>
            :expand ((svar-decomptable-vars x)))))

  (defthm svar-decomptable-lookup-of-acons-non-key
    (implies (not (hons-assoc-equal (svar-fix v) (svar-decomptable-fix decomp)))
             (equal (svar-decomptable-lookup key decomp (cons (cons v val) env))
                    (svar-decomptable-lookup key decomp env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-lookup-of-acons-when-key-not-in-new-var-decomp
    (implies (or (not (svar-p v))
                 (and (not (member-equal (svar-fix key)
                                         (svar-decomp-vars (cdr (hons-assoc-equal v decomp)))))
                      (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))))
             (equal (svar-decomptable-lookup key decomp (cons (cons v val) env))
                    (svar-decomptable-lookup key decomp env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup alist-keys svar-decomptable-fix))))

  ;; (defthm svar-decomptable-lookup-empty-env
  ;;   (Equal (svar-decomptable-lookup key decomp nil)
  ;;          (and (member-equal (svar-fix key) (svar-decomptable-vars decomp))
  ;;               (4vec-x)))
  ;;   :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix)))


  (local (defthm svex-env-boundp-by-member-alist-keys
           (implies (member (svar-fix key) (alist-keys (svex-env-fix env)))
                    (svex-env-boundp key env))
           :hints(("Goal" :in-theory (enable svex-env-boundp alist-keys)))))

  (defthm svar-decomptable-lookup-of-append-env-when-alist-keys-subsetp
    (implies (subsetp-equal (alist-keys (svar-decomptable-fix x)) (alist-keys (svex-env-fix env)))
             (equal (svar-decomptable-lookup key x (append env rest))
                    (svar-decomptable-lookup key x env)))
    :hints(("Goal" :in-theory (e/d (alist-keys) (member-alist-keys)))))


  (defthmd svar-decomptable-lookup-in-terms-of-svar-decomptable-find-domainvar
    (implies (and (member-equal (svar-fix key) (svar-decomptable-vars x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (equal (svar-decomptable-lookup key x env)
                    (let* ((dom (svar-decomptable-find-domainvar key x))
                           (decomp (cdr (hons-assoc-equal dom (svar-decomptable-fix x)))))
                      (svar-decomp-lookup key decomp 0 (svex-env-lookup dom env)))))
    :hints(("Goal" :in-theory (enable svar-decomptable-find-domainvar
                                      svar-decomptable-vars
                                      alist-keys)))))



(local (defthm alist-keys-of-append
         (equal (alist-keys (append x y))
                (append (alist-keys x) (alist-keys y)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(define svar-decomptable-extract ((x svar-decomptable-p)
                                  (env svex-env-p))
  :returns (new-env svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-extract (cdr x) env)))
    (append (svar-decomp-extract (cdar x) env)
            (svar-decomptable-extract (cdr x) env)))
  ///

  (defret svar-decomptable-eval-of-<fn>
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (equal (svar-decomptable-eval x new-env)
                    (svar-decomptable-eval x env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval svar-decomptable-vars))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys (svar-decomptable-extract x env))
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))


(define svar-decomptable-inverse-env ((x svar-decomptable-p)
                                      (env svex-env-p))
  :returns (new-env svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-inverse-env (cdr x) env)))
    (append (svar-decomp-inverse-env (cdar x) 0 (svex-env-lookup (caar x) env))
            (svar-decomptable-inverse-env (cdr x) env)))
  ///

  (defret svar-decomptable-eval-with-<fn>
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (equal (svar-decomptable-eval x new-env)
                    (svex-env-extract (alist-keys (svar-decomptable-fix x)) env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval svar-decomptable-vars alist-keys
                                      svex-env-extract svex-env-acons)
            :induct <call>
            :expand ((svar-decomptable-fix x)))))
                           
  (defthm svar-decomptable-inverse-env-of-svex-env-acons-non-member
    (implies (not (member (svar-fix v) (alist-keys (svar-decomptable-fix x))))
             (equal (svar-decomptable-inverse-env x (svex-env-acons v val env))
                    (svar-decomptable-inverse-env x env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys))))

  (defret <fn>-of-svar-decomptable-eval
    :pre-bind ((env (svar-decomptable-eval x env1)))
    (implies (and (no-duplicatesp-equal (svar-decomptable-vars x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (equal new-env (svar-decomptable-extract x env1)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval
                                      svar-decomptable-vars
                                      svar-decomptable-extract
                                      svar-decomptable-fix
                                      alist-keys))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys new-env)
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-boundp-is-member-alist-keys
           (iff (svex-env-boundp key x)
                (member-equal (svar-fix key) (alist-keys (svex-env-fix x))))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (defret lookup-in-<fn>
    (equal (svex-env-lookup key new-env)
           (if (member-equal (svar-fix key) (svar-decomptable-vars x))
               (svar-decomptable-lookup key x env)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svar-decomptable-lookup
                                      svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))

(local
 (defthm svex-alist-keys-of-append
   (equal (svex-alist-keys (append x y))
          (append (svex-alist-keys x)
                  (svex-alist-keys y)))
   :hints(("Goal" :in-theory (enable svex-alist-keys)))))

(define svar-decomptable->inverse ((x svar-decomptable-p))
  :returns (alist svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable->inverse (cdr x))))
    (append (svar-decomp->inverse (cdar x) 0 (svex-var (caar x)))
            (svar-decomptable->inverse (cdr x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svar-decomptable-inverse-env x env))
    :hints(("Goal" :in-theory (enable svar-decomptable-inverse-env svex-alist-eval)
            :induct <call>
            :expand ((:free (v) (svex-eval (svex-var v) env))))))

  (local (defthm svex-alist-eval-of-pairlis$-vars
           (implies (svarlist-p vars)
                    (equal (svex-alist-eval (pairlis$ vars (svarlist->svexes vars)) env)
                           (svex-env-extract vars env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-extract svarlist->svexes svex-eval)))))

  (local (defthm svarlist-p-keys-of-svar-decomptable
           (implies (svar-decomptable-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-svex-of-inverse
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (svex-alist-eval-equiv (svex-alist-compose (svar-decomptable->subst x) (svar-decomptable->inverse x))
                                    (svex-identity-subst (alist-keys (svar-decomptable-fix x)))))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)
            :do-not-induct t)))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup key alist)
         (member-equal (svar-fix key) (svar-decomptable-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key alist) env)
           (if (member-equal (svar-fix key) (svar-decomptable-vars x))
               (svar-decomptable-lookup key x env)
             (4vec-x)))
    :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                           (k key)
                           (x alist)))
             :in-theory (disable svex-env-lookup-of-svex-alist-eval)
             :do-not-induct t))
    :hints-sub-returnnames t)

  

  (local (defthm 4vec-part-select-in-terms-of-concat
           (implies (and (natp lsb) (natp width))
                    (Equal (4vec-part-select (2vec lsb) (2vec width) in)
                           (4vec-concat (2vec width) (4vec-rsh (2vec lsb) in) 0)))
           :hints(("Goal" :in-theory (enable 4vec-part-select
                                             4vec-concat
                                             4vec-rsh
                                             4vec-shift-core
                                             4vec-zero-ext)))))

  (defretd lookup-of-<fn>-under-svex-eval-equiv
    (implies (and (member-equal (Svar-fix key) (svar-decomptable-vars x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (svex-eval-equiv (svex-lookup key alist)
                              (b* ((dom (svar-decomptable-find-domainvar key x))
                                   (decomp (cdr (hons-assoc-equal dom (svar-decomptable-fix x))))
                                   (offset (svar-decomp-var-offset key decomp))
                                   (shift (svar-decomp-shift offset decomp)))
                                (svar-decomp-case shift
                                  :segment
                                  (svex-concat shift.width
                                               (svex-rsh Offset (svex-var dom))
                                               0)
                                  :remainder (svex-rsh Offset (svex-var dom))))))
    :hints(("Goal" :in-theory (e/d (svex-eval-equiv
                                    svex-apply
                                    svar-decomptable-lookup-in-terms-of-svar-decomptable-find-domainvar)
                                   (<fn>))
            :expand ((:free (x env) (svex-eval (svex-var x) env))))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys alist)
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))






(local (defthm member-alist-keys
         (iff (member k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (Defthm svex-lookup-when-subsetp-alist-keys
         (implies (and (subsetp set (svex-alist-keys x))
                       (member-equal (svar-fix key) set))
                  (svex-lookup key x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup)))))

(define svex-alist-decomptable-decompose ((x svex-alist-p)
                                          (decomp svar-decomptable-p))
  ;; Just affects the keys, not the values
  :returns (new-x svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-alist-decomptable-decompose (cdr x) decomp))
       ((cons var val) (car x))
       (look (hons-assoc-equal var (svar-decomptable-fix decomp)))
       ((unless look)
        (cons (cons var (svex-fix val))
              (svex-alist-decomptable-decompose (cdr x) decomp))))
    (append (svar-decomp->inverse (cdr look) 0 val)
            (svex-alist-decomptable-decompose (cdr x) decomp)))
  ///
  (local (defthm svex-p-lookup-in-svex-alist
           (implies (and (svex-alist-p x)
                         (hons-assoc-equal k x))
                    (svex-p (cdr (hons-assoc-equal k x))))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append x y))
                  (or (hons-assoc-equal k x)
                      (hons-assoc-equal k y)))))

  (local (defthm intersectp-when-member-both
           (implies (and (member-equal k y)
                         (member-equal k x))
                    (intersectp-equal x y))))

  (local (defthm member-svar-decomptable-vars-when-member-svar-decomp-vars-of-lookup
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         (member-equal key
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp)))))
                    (member-equal key (svar-decomptable-vars decomp)))
           :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

  (local (defthm svar-decomptable-lookup-when-var-in-look
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         ;; (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                         (member-equal (svar-fix key)
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp))))
                         (no-duplicatesp-equal (svar-decomptable-vars decomp)))
                    (equal (svar-decomptable-lookup key decomp env)
                           (svar-decomp-lookup key (cdr (hons-assoc-equal k decomp))
                                               0 (svex-env-lookup k env))))
           :hints(("Goal" :in-theory (enable svar-decomptable-lookup svar-decomptable-vars
                                             svar-decomptable-fix alist-keys)))))

  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup k (cons (cons key val) env))
                  (if (and (svar-p key) (equal (svar-fix k) key))
                      (4vec-fix val)
                    (svex-env-lookup k env)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
                        

  (defret eval-svex-lookup-of-<fn>
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp))))
             (equal (svex-eval (svex-lookup key new-x) env)
                    (cond ((member-equal (svar-fix key) (svar-decomptable-vars decomp))
                           (if (svex-lookup (svar-decomptable-find-domainvar key decomp)
                                            x)
                               (svar-decomptable-lookup key decomp (svex-alist-eval x env))
                             (4vec-x)))
                          ((member-equal (svar-fix key) (alist-keys (svar-decomptable-fix decomp)))
                           (4vec-x))
                          (t (svex-eval (svex-lookup key x) env)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys svex-alist-eval))))

  (local (defthm cdr-hons-assoc-equal-under-iff-in-svex-alist
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))))

  (defret svex-lookup-under-iff-of-<fn>
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp))))
             (iff (svex-lookup key new-x)
                  (cond ((member-equal (svar-fix key) (svar-decomptable-vars decomp))
                         (svex-lookup (svar-decomptable-find-domainvar key decomp)
                                      x))
                        ((member-equal (svar-fix key) (alist-keys (svar-decomptable-fix decomp)))
                         nil)
                        (t (svex-lookup key x)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys svex-alist-eval))))




  (defthm alist-keys-of-svex-alist-eval
    (equal (alist-keys (svex-alist-eval x env))
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval alist-keys))))

  (defret <fn>-in-terms-of-svar-decomptable->inverse
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                  (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                                 (svex-alist-keys x)))
             (svex-alist-eval-equiv new-x
                                    (append (svex-alist-compose (svar-decomptable->inverse decomp) x)
                                            (svex-alist-removekeys (alist-keys (svar-decomptable-fix decomp)) x))))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                      svex-eval-equiv)
            :do-not-induct t)))

  (local (in-theory (enable svex-alist-fix))))




(define svex-alist-to-decomp ((x svex-alist-p)
                              (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-decompose (svex-alist-compose x (svar-decomptable->subst decomp)) decomp))


(local
 (progn
   (defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 1
     :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

   (defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 2
     :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

   (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-removekeys keys x) 2
     :hints((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

   (defthm svex-compose-nil
     (svex-eval-equiv (svex-compose x nil) x)
     :hints(("Goal" :in-theory (enable svex-eval-equiv svex-alist-eval))))

   (defthm svex-alist-eval-equiv-of-compose-nil
     (svex-alist-eval-equiv (svex-alist-compose x nil) x)
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                       svex-alist-eval))))

   (defthm svex-alist-removekeys-of-nil
     (equal (svex-alist-removekeys keys nil) nil)
     :hints(("Goal" :in-theory (enable svex-alist-removekeys))))))


(define svex-alist-decomptable-recompose ((x svex-alist-p)
                                          (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (append (svex-alist-compose (svar-decomptable->subst decomp) x)
          (svex-alist-removekeys (svar-decomptable-vars decomp) x))
  ///
  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-decomptable-recompose x decomp) 1)
  (defthm svex-alist-decomptable-recompose-of-nil
    (svex-alist-eval-equiv (svex-alist-decomptable-recompose nil decomp)
                           (svar-decomptable->subst decomp))))


(define svex-alist-from-decomp ((x svex-alist-p)
                                (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-recompose (append (svex-alist-compose x (svar-decomptable->inverse decomp))
                                            (svar-decomptable->inverse decomp))
                                    decomp)
  ///
  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-from-decomp x decomp) 1))


(local
 (progn


   (defthm svex-alist-keys-of-svex-alist-compose
     (Equal (svex-alist-keys (svex-alist-compose x a))
            (svex-alist-keys x))
     :hints(("Goal" :in-theory (enable svex-alist-compose
                                       svex-alist-keys))))

   (defthm svex-alist-compose-of-append
     (equal (svex-alist-compose (append x y) a)
            (append (svex-alist-compose x a)
                    (svex-alist-compose y a)))
     :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons))))

   ;; (local
   ;;  (defthm svex-alist-removekeys-of-cons-member
   ;;    (implies (or (member-equal (car pair) (svarlist-fix vars))
   ;;                 (not (consp pair))
   ;;                 (not (svar-p (car pair))))
   ;;             (equal (svex-alist-removekeys vars (cons pair y))
   ;;                    (svex-alist-removekeys vars y)))
   ;;    :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))

   (defthm svex-alist-removekeys-of-append-subset
     (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix vars))
              (equal (svex-alist-removekeys vars (append x y))
                     (svex-alist-removekeys vars y)))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys))))

   (defthm svex-alist-removekeys-of-non-intersect
     (implies (not (intersectp-equal (svex-alist-keys x) (svarlist-fix vars)))
              (equal (svex-alist-removekeys vars x)
                     (svex-alist-fix x)))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys
                                       svex-alist-fix))))



   (defthm neteval-ordering-compile-of-nil
     (equal (neteval-ordering-compile nil network) nil)
     :hints(("Goal" :in-theory (enable neteval-ordering-compile))))





   (defthm svex-alist-keys-of-svex-alist-compose
     (Equal (svex-alist-keys (svex-alist-compose x a))
            (svex-alist-keys x))
     :hints(("Goal" :in-theory (enable svex-alist-compose
                                       svex-alist-keys))))

   (defthm svex-alist-compose-of-append
     (equal (svex-alist-compose (append x y) a)
            (append (svex-alist-compose x a)
                    (svex-alist-compose y a)))
     :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons))))

   ;; (local
   ;;  (defthm svex-alist-removekeys-of-cons-member
   ;;    (implies (or (member-equal (car pair) (svarlist-fix vars))
   ;;                 (not (consp pair))
   ;;                 (not (svar-p (car pair))))
   ;;             (equal (svex-alist-removekeys vars (cons pair y))
   ;;                    (svex-alist-removekeys vars y)))
   ;;    :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))

   (defthm svex-alist-removekeys-of-append-subset
     (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix vars))
              (equal (svex-alist-removekeys vars (append x y))
                     (svex-alist-removekeys vars y)))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys))))

   (defthm svex-alist-removekeys-of-non-intersect
     (implies (not (intersectp-equal (svex-alist-keys x) (svarlist-fix vars)))
              (equal (svex-alist-removekeys vars x)
                     (svex-alist-fix x)))
     :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys
                                       svex-alist-fix))))

   ;; (local (defthm consp-hons-assoc-equal
   ;;          (iff (consp (hons-assoc-equal k a))
   ;;               (hons-assoc-equal k a))))



   (std::defret-mutual svex-eval-of-append-when-subsetp-first
     (defret <fn>-of-append-when-subsetp-first
       (implies (subsetp-equal (svex-vars x) (alist-keys (svex-env-fix env)))
                (equal (svex-eval x (append env env2))
                       val))
       :hints ('(:expand ((:free (env) <call>)
                          (svex-vars x)))
               (and stable-under-simplificationp
                    '(:in-theory (enable svex-env-boundp))))
       :fn svex-eval)
     (defret <fn>-of-append-when-subsetp-first
       (implies (subsetp-equal (svexlist-vars x) (alist-keys (svex-env-fix env)))
                (equal (svexlist-eval x (append env env2))
                       vals))
       :hints ('(:expand ((:free (env) <call>)
                          (svexlist-vars x))))
       :fn svexlist-eval)
     :mutual-recursion svex-eval)

   (local
    (std::defret-mutual svex-eval-of-special-append
      (defret <fn>-of-special-append
        (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svex-vars x)))
                 (equal (svex-eval x (append (svex-env-extract keys env) env2 env))
                        val))
        :hints ('(:expand ((:free (env) <call>)
                           (svex-vars x)))
                (and stable-under-simplificationp
                     '(:in-theory (enable svex-env-boundp))))
        :fn svex-eval)
      (defret <fn>-of-special-append
        (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svexlist-vars x)))
                 (equal (svexlist-eval x (append (svex-env-extract keys env) env2 env))
                        vals))
        :hints ('(:expand ((:free (env) <call>)
                           (svexlist-vars x))))
        :fn svexlist-eval)
      :mutual-recursion svex-eval))


   (defret <fn>-of-special-append
     (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svex-alist-vars x)))
              (equal (svex-alist-eval x (append (svex-env-extract keys env) env2 env))
                     result))
     :hints (("goal" :in-theory (enable svex-alist-eval svex-alist-vars)))
     :fn svex-alist-eval)

   (defthm svex-alist-eval-of-append-when-subsetp-first
     (implies (subsetp (svex-alist-vars x) (alist-keys (svex-env-fix a)))
              (equal (svex-alist-eval x (append a b))
                     (svex-alist-eval x a)))
     :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))
   

   (defthm svex-alist-compose-of-append-when-subsetp-first
     (implies (subsetp (svex-alist-vars x) (svex-alist-keys a))
              (svex-alist-eval-equiv (svex-alist-compose x (append a b))
                                     (svex-alist-compose x a)))
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))

   (defthm svex-alist-eval-of-svex-alist-removekeys
     (equal (svex-alist-eval (svex-alist-removekeys vars x) a)
            (svex-env-removekeys vars (svex-alist-eval x a)))
     :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-removekeys svex-env-removekeys))))))



#||
;; Composition steps.
;; 1: compose original network (orig) via dfs, resulting in comp1.  We have (netcomp-p comp1 orig).
;; 2: apply svex-alist-to-decomp to comp1, resulting in compdec1.
;; 3: compose compdec1 via dfs, resulting in compdec2.  We have (netcomp-p compdec2 compdec1).
;; 4. apply svex-alist-from-decomp to compdec2, resulting in comp2.
;;     --- Can we conclude (netcomp-p comp2 comp1)?
;;
(defthm from-decomp-of-to-decomp-preserves-netcomp-p
  (implies (and (not (intersectp-equal (svex-alist-keys comp1)
                                       (svar-decomptable-vars decomp)))
                (not (intersectp-equal (svex-alist-vars comp1)
                                       (svar-decomptable-vars decomp)))
                (no-duplicatesp-equal (svar-decomptable-vars decomp))
                (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                               (svex-alist-keys comp1))
                (netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp)))
           (netcomp-p (svex-alist-from-decomp compdec2 decomp) comp1))
  :hints ('(:computed-hint-replacement
            ((and stable-under-simplificationp
                  (let ((ordering (acl2::find-call-lst 'netcomp-p-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,ordering . ordering)))))))
            :expand ((netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp))))))

;; this reduces to:
(IMPLIES
 (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-KEYS COMP1)))
      (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-VARS COMP1)))
      (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
      (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
      (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                     (SVEX-ALIST-KEYS COMP1)))
 (NETCOMP-P
  (SVEX-ALIST-FROM-DECOMP
   (NETEVAL-ORDERING-COMPILE ORDERING
                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
   DECOMP)
  COMP1))
;; so we have to construct (from-to-decomp-ordering ordering decomp)
;; for which:

(IMPLIES
 (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-KEYS COMP1)))
      (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-VARS COMP1)))
      (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
      (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
      (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                     (SVEX-ALIST-KEYS COMP1)))
 (svex-alist-eval-equiv
  (SVEX-ALIST-FROM-DECOMP
   (NETEVAL-ORDERING-COMPILE ORDERING
                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
   DECOMP)
  (neteval-ordering-compile (from-decomp-ordering ordering decomp) COMP1)))

||#

(local
 (progn
   (defthm neteval-ordering-compile-of-nil
     (equal (neteval-ordering-compile nil network) nil)
     :hints(("Goal" :in-theory (enable neteval-ordering-compile))))

   (local
    (defthm svex-alist-removekeys-when-superset
      (implies (subsetp (svex-alist-keys a) (svarlist-fix keys))
               (equal (svex-alist-removekeys keys a) nil))
      :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys svex-alist-fix)))))

   (local
    (defthm svex-alist-keys-of-svex-alist-removekeys
      (equal (svex-alist-keys (svex-alist-removekeys vars alist))
             (set-difference-equal (svex-alist-keys alist) (svarlist-fix vars)))
      :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys set-difference-equal)))))

   (local (defthm subsetp-set-difference
            (subsetp-equal (set-difference-equal a b) a)
            :hints(("goal" :in-theory (enable acl2::subsetp-witness-rw)))))

   (local (defthm subsetp-keys-of-svex-alist-reduce
            (implies (svarlist-p vars)
                     (subsetp-equal (svex-alist-keys (svex-alist-reduce vars alist)) vars))
            :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-reduce)))))




   (local
    (define svex-pair-eval-equiv (x y)
      :verify-guards nil
      (and (iff (consp x) (consp y))
           (implies (consp x)
                    (and (equal (car x) (car y))
                         (svex-eval-equiv (cdr x) (cdr y)))))
      ///
      (defequiv svex-pair-eval-equiv)
      (defcong svex-pair-eval-equiv svex-alist-eval-equiv (cons pair rest) 1
        :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                          svex-lookup))))

      (defcong svex-eval-equiv svex-pair-eval-equiv (cons key val) 2)))


   (local
    (defthm svex-compose-of-rsh-under-eval-equiv
      (svex-eval-equiv (svex-compose (svex-rsh offset x) a)
                       (svex-rsh offset (svex-compose x a)))
      :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

   (local
    (defthm svex-compose-of-concat-under-eval-equiv
      (svex-eval-equiv (svex-compose (svex-concat offset x y) a)
                       (svex-concat offset (svex-compose x a) (svex-compose y a)))
      :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

   (local (defthm svex-compose-of-compose
            (svex-eval-equiv (svex-compose (svex-compose x a) b)
                             (svex-compose x (append (svex-alist-compose a b) b)))
            :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

   (local (defthm svex-alist-compose-of-svex-alist-compose
            (svex-alist-eval-equiv (svex-alist-compose (svex-alist-compose x a) b)
                                   (svex-alist-compose x (append (svex-alist-compose a b) b)))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))



   (local (defthm svex-alist-removekeys-of-append-removekeys
            (equal (svex-alist-removekeys vars (append (svex-alist-removekeys vars x) y))
                   (svex-alist-removekeys vars (append x y)))
            :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))


   (local (defthm svex-alist-removekeys-of-append
            (Equal (svex-alist-removekeys vars (append a b))
                   (append (svex-alist-removekeys vars a)
                           (svex-alist-removekeys vars b)))
            :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))


   (local
    (std::defret-mutual svex-eval-of-append-reduce-superset
      (defret <fn>-of-append-reduce-superset
        :pre-bind ((env (append a b c)))
        (implies (subsetp-equal (svex-vars x) (svarlist-fix vars))
                 (equal (svex-eval x (append a (svex-env-reduce vars b) c))
                        val))
        :hints ('(:expand ((:free (env) <call>)
                           (svex-vars x)))
                (and stable-under-simplificationp
                     '(:in-theory (enable svex-env-boundp))))
        :fn svex-eval)
      (defret <fn>-of-append-reduce-superset
        :pre-bind ((env (append a b c)))
        (implies (subsetp-equal (svexlist-vars x) (svarlist-fix vars))
                 (equal (svexlist-eval x (append a (svex-env-reduce vars b) c))
                        vals))
        :hints ('(:expand ((:free (env) <call>)
                           (svexlist-vars x))))
        :fn svexlist-eval)
      :mutual-recursion svex-eval))

   (local (defthm svex-alist-eval-append-reduce-superset
            (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                     (equal (svex-alist-eval x (append a (svex-env-reduce vars b) c))
                            (svex-alist-eval x (append a b c))))
            :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars)))))

   (local (defthm svex-alist-compose-append-reduce-superset
            (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                     (svex-alist-eval-equiv (svex-alist-compose x (append a (svex-alist-reduce vars b)))
                                            (svex-alist-compose x (append a b))))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))


   (local
    (encapsulate nil
      (local (defthmd svex-env-boundp-is-member-alist-keys
               (iff (svex-env-boundp key x)
                    (member-equal (svar-fix key) (alist-keys (svex-env-fix x))))
               :hints(("Goal" :in-theory (enable svex-env-boundp)))))
      (local (defthm svex-env-lookup-when-not-boundp
               (implies (not (svex-env-boundp key x))
                        (equal (svex-env-lookup key x) (4vec-x)))
               :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

      (defthm svex-envs-equivalent-append-removekeys-set-equiv
        (implies (acl2::set-equiv (alist-keys (svex-env-fix a)) (svarlist-fix vars))
                 (svex-envs-equivalent (append (svex-env-removekeys vars b) a)
                                       (append a b)))
        :hints(("Goal" :in-theory (enable svex-envs-equivalent))
               (and stable-under-simplificationp
                    '(:in-theory (e/d (svex-env-boundp-is-member-alist-keys)
                                      (member-alist-keys))))))

      (defthm svex-alist-eval-equiv-append-removekeys-set-equiv
        (implies (acl2::set-equiv (svex-alist-keys a) (svarlist-fix vars))
                 (svex-alist-eval-equiv (append (svex-alist-removekeys vars b) a)
                                        (append a b)))
        :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))))

   ;; (local
   ;;  (std::defret-mutual svex-eval-of-append-remove-superset-of-other
   ;;    (defret <fn>-of-append-reduce-superset
   ;;      :pre-bind ((env (append a b)))
   ;;      (implies (subsetp-equal (alist-keys (svex-env-fix a)) (svarlist-fix vars))
   ;;               (equal (svex-eval x (append (svex-env-removekeys vars b) a))
   ;;                      val))
   ;;      :hints ('(:expand ((:free (env) <call>)))
   ;;              (and stable-under-simplificationp
   ;;                   '(:in-theory (enable svex-env-boundp))))
   ;;      :fn svex-eval)
   ;;    (defret <fn>-of-append-reduce-superset
   ;;      :pre-bind ((env (append a b)))
   ;;      (implies (subsetp-equal (alist-keys (svex-env-fix a)) (svarlist-fix vars))
   ;;               (equal (svexlist-eval x (append (svex-env-removekeys vars b) a))
   ;;                      vals))
   ;;      :hints ('(:expand ((:free (env) <call>))))
   ;;      :fn svexlist-eval)
   ;;    :mutual-recursion svex-eval))

   (local (defthm svex-compose-lookup-of-append
            (equal (Svex-compose-lookup key (append x y))
                   (or (svex-lookup key x)
                       (svex-compose-lookup key y)))
            :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

   (local (defthm svex-compose-lookup-of-svex-alist-removekeys
            (equal (svex-compose-lookup v (svex-alist-removekeys keys x))
                   (if (member-equal (svar-fix v) (svarlist-fix keys))
                       (svex-var v)
                     (svex-compose-lookup v x)))
            :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

   (local (defthm svex-compose-lookup-of-svex-alist-compose
            (equal (Svex-compose-lookup v (svex-alist-compose x a))
                   (if (svex-lookup v x)
                       (svex-compose (svex-lookup v x) a)
                     (svex-var v)))
            :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

   (local (Defthm svex-compose-lookup-when-svex-lookup
            (implies (svex-lookup v x)
                     (equal (svex-compose-lookup v x)
                            (svex-lookup v x)))
            :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

   (local (Defthm svex-compose-lookup-when-not-svex-lookup
            (implies (not (svex-lookup v x))
                     (equal (svex-compose-lookup v x)
                            (svex-var v)))
            :hints(("Goal" :in-theory (enable svex-compose-lookup)))))


   (local (defthm svex-compose-of-svex-var
            (equal (svex-compose (svex-var x) a)
                   (svex-compose-lookup x a))
            :hints(("Goal" :in-theory (enable svex-compose svex-compose-lookup)))))


   (local
    (std::defret-mutual svex-eval-of-append-remove-non-intersecting
      (defret <fn>-of-append-remove-non-intersecting
        :pre-bind ((env (append a b c)))
        (implies (not (intersectp-equal (svex-vars x) (svarlist-fix vars)))
                 (equal (svex-eval x (append a (svex-env-removekeys vars b) c))
                        val))
        :hints ('(:expand ((:free (env) <call>)
                           (svex-vars x)))
                (and stable-under-simplificationp
                     '(:in-theory (enable svex-env-boundp))))
        :fn svex-eval)
      (defret <fn>-of-append-remove-non-intersecting
        :pre-bind ((env (append a b c)))
        (implies (not (intersectp-equal (svexlist-vars x) (svarlist-fix vars)))
                 (equal (svexlist-eval x (append a (svex-env-removekeys vars b) c))
                        vals))
        :hints ('(:expand ((:free (env) <call>)
                           (svexlist-vars x))))
        :fn svexlist-eval)
      :mutual-recursion svex-eval))

   (local (defthm svex-alist-eval-append-remove-non-intersecting
            (implies (not (intersectp-equal (svex-alist-vars x) (svarlist-fix vars)))
                     (equal (svex-alist-eval x (append a (svex-env-removekeys vars b) c))
                            (svex-alist-eval x (append a b c))))
            :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars)))))

   (local (defthm svex-alist-compose-append-remove-non-intersecting
            (implies (not (intersectp-equal (svex-alist-vars x) (svarlist-fix vars)))
                     (svex-alist-eval-equiv (svex-alist-compose x (append a (svex-alist-removekeys vars b)))
                                            (svex-alist-compose x (append a b))))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))

   (local (defthm svex-alist-compose-append-remove-non-intersecting-3
            (implies (not (intersectp-equal (svex-alist-vars x) (svarlist-fix vars)))
                     (svex-alist-eval-equiv (svex-alist-compose x (append a (svex-alist-removekeys vars b) c))
                                            (svex-alist-compose x (append a b c))))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))

   (local (defthm svex-compose-lookup-append-remove-non-intersecting-3
            (implies (not (intersectp-equal (svex-alist-vars x) (svarlist-fix vars)))
                     (svex-eval-equiv (svex-compose (svex-lookup var x)
                                                    (append a (svex-alist-removekeys vars b) c))
                                      (svex-compose (svex-lookup var x)
                                                    (append a b c))))
            :hints (("goal" :use ((:instance svex-lookup-of-svex-alist-compose
                                   (v var) (x x) (a (append a (svex-alist-removekeys vars b) c)))
                                  (:instance svex-lookup-of-svex-alist-compose
                                   (v var) (x x) (a (append a b c))))
                     :in-theory (disable svex-lookup-of-svex-alist-compose))
                    (and stable-under-simplificationp
                         '(:in-theory (e/d (svex-compose)
                                           (svex-lookup-of-svex-alist-compose)))))))

   (local (defthm svex-compose-lookup-append-remove-non-intersecting-2
            (implies (not (intersectp-equal (svex-alist-vars x) (svarlist-fix vars)))
                     (svex-eval-equiv (svex-compose (svex-lookup var x)
                                                    (append a (svex-alist-removekeys vars b)))
                                      (svex-compose (svex-lookup var x)
                                                    (append a b))))
            :hints (("goal" :use ((:instance svex-lookup-of-svex-alist-compose
                                   (v var) (x x) (a (append a (svex-alist-removekeys vars b))))
                                  (:instance svex-lookup-of-svex-alist-compose
                                   (v var) (x x) (a (append a b))))
                     :in-theory (disable svex-lookup-of-svex-alist-compose))
                    (and stable-under-simplificationp
                         '(:in-theory (e/d (svex-compose)
                                           (svex-lookup-of-svex-alist-compose)))))))


   (local
    (std::defret-mutual svex-eval-of-append-non-intersecting
      (defret <fn>-of-append-non-intersecting
        :pre-bind ((env (append a c)))
        (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix b))))
                 (equal (svex-eval x (append a b c))
                        val))
        :hints ('(:expand ((:free (env) <call>)
                           (svex-vars x)))
                (and stable-under-simplificationp
                     '(:in-theory (enable svex-env-boundp))))
        :fn svex-eval)
      (defret <fn>-of-append-non-intersecting
        :pre-bind ((env (append a c)))
        (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix b))))
                 (equal (svexlist-eval x (append a b c))
                        vals))
        :hints ('(:expand ((:free (env) <call>)
                           (svexlist-vars x))))
        :fn svexlist-eval)
      :mutual-recursion svex-eval))

   (defret <fn>-of-append-non-intersecting-third-of-four
     :pre-bind ((env (append a b d)))
     (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix c))))
              (equal (svex-eval x (append a b c d))
                     val))
     :hints (("goal" :use ((:instance <fn>-of-append-non-intersecting
                            (a (append a b))
                            (b c)
                            (c d)))))
     :fn svex-eval)


   (local (defthm svex-compose-append-remove-non-intersecting-third
            (implies (not (intersectp-equal (svex-vars x) (svex-alist-keys c)))
                     (svex-eval-equiv (svex-compose x
                                                    (append a b c))
                                      (svex-compose x
                                                    (append a b))))
            :hints(("Goal" :in-theory (enable svex-eval-equiv)))))



   (local
    (encapsulate nil
      (defthm svex-compose-lookup-append-remove-non-intersecting-third
        (implies (not (intersectp-equal (svex-alist-vars x) (svex-alist-keys c)))
                 (svex-eval-equiv (svex-compose (svex-lookup v x)
                                                (append a b c))
                                  (svex-compose (svex-lookup v x)
                                                (append a b))))
        :hints (("goal" :use ((:instance svex-compose-append-remove-non-intersecting-third
                               (x (svex-lookup v x)))
                              (:instance svex-vars-of-svex-alist-lookup
                               (k v)))
                 :in-theory (disable svex-compose-append-remove-non-intersecting-third
                                     svex-vars-of-svex-alist-lookup))
                (set-reasoning)))))

   (local
    (defthm svex-rsh-0-under-eval-equiv
      (svex-eval-equiv (svex-rsh 0 x) x)
      :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))

   (local (defthm svarlist-p-alist-keys-when-svar-decomptable-p
            (implies (svar-decomptable-p x)
                     (svarlist-p (alist-keys x)))
            :hints(("Goal" :in-theory (enable svar-decomptable-p alist-keys)))))

   ;; (define decomp-var-correspondence-p ((relevant-width maybe-natp)
   ;;                                      (signal svar-p)
   ;;                                      (offset natp)
   ;;                                      (decomp-signal svar-p)
   ;;                                      (decomp-offset natp)
   ;;                                      (decomp svar-decomptable-p))
   ;;   (b* ((signal-decomp (hons-assoc-equal (svar-fix signal) (svar-decomptable-fix decomp)))
   ;;        ((unless signal-decomp)
   ;;         (and (equal (svar-fix signal) (svar-fix decomp-signal))
   ;;              (eql (lnfix offset) (lnfix decomp-offset))))
   

   (progn ;; put back in defines form below?
     (local (defthm svar-decomptable-domainvar-rw
              (implies (and (bind-free
                             (let ((call (acl2::find-call 'hons-assoc-equal var)))
                               (and call `((signal . ,(cadr call)))))
                             (signal))
                            (equal look (hons-assoc-equal signal (svar-decomptable-fix x)))
                            look
                            (member-equal (svar-fix var) (svar-decomp-vars (cdr look)))
                            (no-duplicatesp-equal (svar-decomptable-vars x))
                            (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
                       (equal (svar-decomptable-find-domainvar var x)
                              signal))))

     (local (defthm no-duplicate-decomp-vars-when-no-duplicate-decomptable-vars
              (implies (and (no-duplicatesp-equal (svar-decomptable-vars x))
                            (svar-p signal))
                       (no-duplicatesp-equal (svar-decomp-vars (cdr (hons-assoc-equal signal x)))))
              :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

     (defthm neteval-sigordering-compile-concat-under-svex-eval-equiv
       (svex-eval-equiv (neteval-sigordering-compile
                         (neteval-sigordering-concat
                          width first rest)
                         var offset network)
                        (svex-concat
                         width
                         (neteval-sigordering-compile first var offset network)
                         (neteval-sigordering-compile rest var (+ (nfix offset) (nfix width)) network)))
       :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply))))

     (defthm svex-concat-under-svex-eval-equiv
       (implies (natp width)
                (svex-eval-equiv (svex-call 'concat (list (svex-quote (2vec width)) first rest))
                                 (svex-concat width first rest)))
       :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply))))

     (local (defthm svex-compose-of-svex-call
              (equal (svex-compose (svex-call fn args) a)
                     (svex-call fn (svexlist-compose args a)))
              :hints(("Goal" :Expand ((svex-compose (svex-call fn args) a))))))

     (local (defthm svexlist-compose-of-nil
              (equal (svexlist-compose nil a) nil)
              :hints(("Goal" :in-theory (enable svexlist-compose)))))

     (local (defthm svexlist-compose-of-cons
              (equal (svexlist-compose (cons x y) a)
                     (cons (svex-compose x a)
                           (svexlist-compose y a)))
              :hints(("Goal" :in-theory (enable svexlist-compose)))))

     (local (defthm svex-compose-of-svex-quote
              (equal (svex-compose (svex-quote val) a)
                     (svex-quote val))
              :hints(("Goal" :expand ((svex-compose (svex-quote val) a))))))


     (local (defthm logapp-of-logapp
              (equal (logapp width (logapp width a b) c)
                     (logapp width a c))
              :hints(("Goal" :in-theory (enable* bitops::logapp-right-assoc)))))
     

     (local (defthm 4vec-concat-of-concat
              (equal (4vec-concat width (4vec-concat width a b) c)
                     (4vec-concat width a c))
              :hints(("Goal" :in-theory (enable 4vec-concat)))))

     (local (defthm svex-concat-of-svex-concat-under-svex-eval-equiv
              (svex-eval-equiv (svex-concat width (svex-concat width a b) c)
                               (svex-concat width a c))
              :hints(("Goal" :in-theory (e/d (svex-eval-equiv svex-eval svex-apply)
                                             (svex-concat-under-svex-eval-equiv))))))

     )


   (defcong svex-alist-compose-equiv svex-eval-equiv
     (neteval-ordering-or-null-compile x signal network) 3
     :hints(("Goal" :in-theory (enable svex-eval-equiv))))

   (defcong svex-alist-compose-equiv svex-eval-equiv
     (neteval-sigordering-compile x signal offset network) 4
     :hints(("Goal" :in-theory (enable svex-eval-equiv))))


   (define neteval-ordering-or-null-compile-split ((x neteval-ordering-or-null-p)
                                                   ;; a signal from the non-decomposed space
                                                   (signal svar-p)
                                                   ;; a substitute for the lookup of signal in network
                                                   ;; in case it isn't bound
                                                   (lookup svex-p)
                                                   ;; this is the decomposed network.
                                                   (network svex-alist-p))
     :returns (compose svex-p)
     (neteval-ordering-or-null-case x
       :null (svex-var signal)
       :ordering (svex-compose
                  (or (svex-lookup signal network)
                      (svex-fix lookup))
                  (neteval-ordering-compile x.ord network)))
     ///
     (defret <fn>-when-signal-bound
       (implies (svex-lookup signal network)
                (equal compose
                       (neteval-ordering-or-null-compile x signal network)))
       :hints(("Goal" :in-theory (enable neteval-ordering-or-null-compile))))
     
     (defret <fn>-of-svex-var
       :pre-bind ((lookup (svex-var signal)))
       (equal compose
              (neteval-ordering-or-null-compile x signal network))
       :hints(("Goal" :in-theory (enable neteval-ordering-or-null-compile))))
     
     ;; Signal2 is the signal in the decomposed space, therefore not bound in decomp.
     ;; Signal is a signal from the non-decomposed space, therefore not in the vars of decomp.
     (defretd <fn>-switch-vars
       (implies (and (svex-eval-equiv lookup (svex-lookup signal2 network))
                     (svex-eval-equiv (svex-compose-lookup signal inverse) (svex-compose-lookup signal2 inverse))
                     (svex-lookup signal2 network)
                     (not (svex-lookup signal network)))
                (svex-eval-equiv (svex-compose compose inverse)
                                 (svex-compose
                                  (neteval-ordering-or-null-compile
                                   x signal2 network)
                                  inverse)))
       :hints(("Goal" :in-theory (enable neteval-ordering-or-null-compile))))

     (local
      (defthmd svex-compose-of-rsh-under-eval-equiv-rev
        (svex-eval-equiv (svex-rsh offset (svex-compose x a))
                         (svex-compose (svex-rsh offset x) a))))

     (defretd <fn>-switch-vars-shift
       (implies (and (svex-eval-equiv (svex-rsh offset lookup) (svex-rsh offset2 (svex-lookup signal2 network)))
                     (svex-eval-equiv (svex-rsh offset (svex-compose-lookup signal inverse))
                                      (svex-rsh offset2 (svex-compose-lookup signal2 inverse)))
                     (svex-lookup signal2 network)
                     (not (svex-lookup signal network)))
                (svex-eval-equiv (svex-rsh offset (svex-compose compose inverse))
                                 (svex-rsh offset2 (svex-compose
                                                    (neteval-ordering-or-null-compile
                                                     x signal2 network)
                                                    inverse))))
       :hints(("Goal" :in-theory (e/d (neteval-ordering-or-null-compile
                                       svex-compose-of-rsh-under-eval-equiv-rev)
                                      (svex-compose-of-rsh-under-eval-equiv)))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-compose-of-rsh-under-eval-equiv)))))

     (local (defthm svex-compose-of-0
              (equal (svex-compose 0 a) 0)
              :hints(("Goal" :in-theory (enable svex-compose)))))

     (local
      (defthmd svex-compose-of-concat-under-eval-equiv-rev
        (svex-eval-equiv (svex-concat offset (svex-compose x a) 0)
                         (svex-compose (svex-concat offset x 0) a))))

     (local (defretd <fn>-switch-vars-shift-concat-0
              (implies (and (svex-eval-equiv (svex-concat width (svex-rsh offset lookup) 0)
                                             (svex-concat width (svex-rsh offset2 (svex-lookup signal2 network)) 0))
                            (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose-lookup signal inverse)) 0)
                                             (svex-concat width (svex-rsh offset2 (svex-compose-lookup signal2 inverse)) 0))
                            (svex-lookup signal2 network)
                            (not (svex-lookup signal network)))
                       (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose compose inverse)) 0)
                                        (svex-concat width (svex-rsh offset2 (svex-compose
                                                                              (neteval-ordering-or-null-compile
                                                                               x signal2 network)
                                                                              inverse))
                                                     0)))
              :hints(("Goal" :in-theory (e/d (neteval-ordering-or-null-compile
                                              svex-compose-of-rsh-under-eval-equiv-rev
                                              svex-compose-of-concat-under-eval-equiv-rev)
                                             (svex-compose-of-rsh-under-eval-equiv
                                              svex-compose-of-concat-under-eval-equiv)))
                     (and stable-under-simplificationp
                          '(:in-theory (enable svex-compose-of-rsh-under-eval-equiv
                                               svex-compose-of-concat-under-eval-equiv))))))

     (local (defthmd svex-concat-equiv-when-concat-0-equiv
              (implies (svex-eval-equiv (svex-concat width x 0)
                                        (svex-concat width y 0))
                       (equal (svex-eval-equiv (svex-concat width x rest)
                                               (svex-concat width y rest))
                              t))
              :hints (("goal" :use ((:instance svex-concat-of-svex-concat-under-svex-eval-equiv
                                     (a x) (b 0) (c rest))
                                    (:instance svex-concat-of-svex-concat-under-svex-eval-equiv
                                     (a y) (b 0) (c rest)))
                       :in-theory (disable svex-concat-of-svex-concat-under-svex-eval-equiv)))))

     (defretd <fn>-switch-vars-shift-concat-any
       (implies (and (svex-eval-equiv (svex-concat width (svex-rsh offset lookup) 0)
                                      (svex-concat width (svex-rsh offset2 (svex-lookup signal2 network)) 0))
                     (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose-lookup signal inverse)) 0)
                                      (svex-concat width (svex-rsh offset2 (svex-compose-lookup signal2 inverse)) 0))
                     (svex-lookup signal2 network)
                     (not (svex-lookup signal network)))
                (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose compose inverse)) rest)
                                 (svex-concat width (svex-rsh offset2 (svex-compose
                                                                       (neteval-ordering-or-null-compile
                                                                        x signal2 network)
                                                                       inverse))
                                              rest)))
       :hints(("Goal" :in-theory (e/d (svex-concat-equiv-when-concat-0-equiv
                                       <fn>-switch-vars-shift-concat-0)
                                      (<fn>)))))


     (defcong svex-alist-eval-equiv svex-eval-equiv
       (neteval-ordering-or-null-compile-split x signal lookup network) 4))


   (define neteval-sigordering-compile-split ((x neteval-sigordering-p)
                                              (signal svar-p)
                                              (offset natp)
                                              (lookup svex-p)
                                              (network svex-alist-p))
     :measure (neteval-sigordering-count x)
     :returns (compose svex-p)
     :Verify-guards :after-returns
     ;; :guard (svex-lookup signal network)
     (neteval-sigordering-case x
       :segment (svex-concat x.width
                             (svex-rsh offset (neteval-ordering-or-null-compile-split x.ord signal lookup network))
                             (neteval-sigordering-compile-split x.rest signal (+ x.width (lnfix offset)) lookup network))
       :remainder (svex-rsh offset (neteval-ordering-or-null-compile-split x.ord signal lookup network))
       ;;(svex-compose function (neteval-ordering-compile x.ord network))
       )
     ///
     
     (defret <fn>-when-signal-bound
       (implies (svex-lookup signal network)
                (equal compose
                       (neteval-sigordering-compile x signal offset network)))
       :hints(("Goal" :in-theory (enable neteval-sigordering-compile))))

     (defret <fn>-of-svex-var
       :pre-bind ((lookup (svex-var signal)))
       (equal compose
              (neteval-sigordering-compile x signal offset network))
       :hints(("Goal" :in-theory (enable neteval-sigordering-compile))))


     (local
      (defthmd svex-compose-of-rsh-under-eval-equiv-rev
        (svex-eval-equiv (svex-rsh offset (svex-compose x a))
                         (svex-compose (svex-rsh offset x) a))))
     
     (local (defun switch-vars-ind (x offset offset2)
              (declare (xargs :measure (neteval-sigordering-count x)))
              (neteval-sigordering-case x
                :segment (switch-vars-ind x.rest (+ x.width (lnfix offset)) (+ x.width (lnfix offset2)))
                :remainder (list offset offset2))))

     (local (defthmd logtails-equal
              (implies (and (equal (logtail n x) (logtail m y))
                            (natp i))
                       (equal (equal (logtail (+ i (nfix n)) x) (logtail (+ i (nfix m)) y))
                              t))
              :hints ((acl2::logbitp-reasoning :prune-examples nil))))

     (local (defthm rsh-equiv-when-lesser-equiv
              (implies (and (svex-eval-equiv (svex-rsh offset x) (svex-rsh offset2 y))
                            (natp width))
                       (equal (svex-eval-equiv (svex-rsh (+ width (nfix offset)) x)
                                               (svex-rsh (+ width (nfix offset2)) y))
                              t))
              :hints((and stable-under-simplificationp
                          `(:computed-hint-replacement
                            ((let ((env (acl2::find-call-lst 'svex-eval-equiv-witness clause)))
                               `(:clause-processor (acl2::generalize-with-alist-cp
                                                    clause '((,env . env))))))
                            :expand (,(car (last clause)))))
                     (and stable-under-simplificationp
                          '(:use ((:instance svex-eval-equiv-necc
                                   (x (svex-rsh offset x)) (y (svex-rsh offset2 y))))
                            :in-theory (e/d (4vec-rsh 4vec-shift-core svex-apply logtails-equal)
                                            (svex-eval-equiv-necc)))))))

     (defretd <fn>-switch-vars
       (implies (and (svex-eval-equiv (svex-rsh offset lookup)
                                      (svex-rsh offset2 (svex-lookup signal2 network)))
                     (svex-eval-equiv (svex-rsh offset (svex-compose-lookup signal inverse))
                                      (svex-rsh offset2 (svex-compose-lookup signal2 inverse)))
                     (svex-lookup signal2 network)
                     (not (svex-lookup signal network)))
                (svex-eval-equiv (svex-compose compose inverse)
                                 (svex-compose
                                  (neteval-sigordering-compile
                                   x signal2 offset2 network)
                                  inverse)))
       :hints(("Goal" ;; :in-theory (enable neteval-sigordering-compile)
               :induct (switch-vars-ind x offset offset2)
               :expand ((neteval-sigordering-compile x signal2 offset2 network)
                        <call>)
               :do-not-induct t)
              '(:in-theory (enable NETEVAL-ORDERING-OR-NULL-COMPILE-SPLIT-SWITCH-VARS-SHIFT))
              ;; '(:in-theory (e/d (svex-compose-of-rsh-under-eval-equiv-rev)
              ;;                   (svex-compose-of-rsh-under-eval-equiv)))
              ))

     (local (defun switch-vars-concat-ind (x offset offset2 width)
              (declare (xargs :measure (neteval-sigordering-count x)))
              (neteval-sigordering-case x
                :segment (if (< x.width (nfix width))
                             (switch-vars-concat-ind x.rest (+ x.width (lnfix offset)) (+ x.width (lnfix offset2)) (- (nfix width) x.width))
                           (list offset offset2))
                :remainder (list offset offset2))))

     (local (in-theory (disable svex-concat-under-svex-eval-equiv)))

     (local (defthm svex-concat-of-svex-concat-less
              (implies (<= (nfix width) (nfix width2))
                       (svex-eval-equiv (svex-concat width (svex-concat width2 x y) z)
                                        (svex-concat width x z)))
              :hints(("Goal" :in-theory (e/d (svex-eval-equiv svex-apply)
                                             (svex-concat-under-svex-eval-equiv))))))

     (local (defthm svex-concat-of-svex-concat-more
              (implies (< (nfix width2) (nfix width))
                       (svex-eval-equiv (svex-concat width (svex-concat width2 x y) z)
                                        (svex-concat width2 x (svex-concat (- (nfix width) (nfix width2)) y z))))
              :hints(("Goal" :in-theory (e/d (svex-eval-equiv svex-apply)
                                             (svex-concat-under-svex-eval-equiv))))))

     (local (defthm shifted-logapps-equiv
              (implies (and (equal (logapp width (logtail offset x) rest)
                                   (logapp width (logtail offset2 y) rest))
                            (natp w) (natp width) (< w width))
                       (equal (equal (logapp (+ (- w) width)
                                             (logtail (+ w (nfix offset)) x)
                                             rest)
                                     (logapp (+ (- w) width)
                                             (logtail (+ w (nfix offset2)) y)
                                             rest))
                              t))
              :hints ((bitops::logbitp-reasoning :prune-examples nil))))
     


     (local (defthm shifted-concats-equiv
              (implies (and (svex-eval-equiv (svex-concat width (svex-rsh offset x) rest)
                                             (svex-concat width (svex-rsh offset2 y) rest))
                            (natp w)
                            (natp width)
                            (< w width))
                       (equal (svex-eval-equiv (svex-concat (+ width (- w))
                                                            (svex-rsh (+ w (nfix offset)) x)
                                                            rest)
                                               (svex-concat (+ width (- w))
                                                            (svex-rsh (+ w (nfix offset2)) y)
                                                            rest))
                              t))
              :hints((and stable-under-simplificationp
                          `(:computed-hint-replacement
                            ((let ((env (acl2::find-call-lst 'svex-eval-equiv-witness clause)))
                               `(:clause-processor (acl2::generalize-with-alist-cp
                                                    clause '((,env . env))))))
                            :expand (,(car (last clause)))))
                     (and stable-under-simplificationp
                          '(:use ((:instance svex-eval-equiv-necc
                                   (x (svex-concat width (svex-rsh offset x) rest))
                                   (y (svex-concat width (svex-rsh offset2 y) rest))))
                            :in-theory (e/d (4vec-rsh 4vec-shift-core 4vec-concat svex-apply logtails-equal)
                                            (svex-eval-equiv-necc)))))))

     (local (defthm lesser-logapps-equiv
              (implies (and (equal (logapp width x rest)
                                   (logapp width y rest))
                            (< (nfix w) (nfix width)))
                       (equal (equal (logapp w x rest)
                                     (logapp w y rest))
                              t))
              :hints ((bitops::logbitp-reasoning :prune-examples nil))))

     (local (defthm lesser-concats-equiv
              (implies (and (svex-eval-equiv (svex-concat width x rest)
                                             (svex-concat width y rest))
                            (< (nfix w) (nfix width)))
                       (equal (svex-eval-equiv (svex-concat w x rest)
                                               (svex-concat w y rest))
                              t))
              :hints((and stable-under-simplificationp
                          `(:computed-hint-replacement
                            ((let ((env (acl2::find-call-lst 'svex-eval-equiv-witness clause)))
                               `(:clause-processor (acl2::generalize-with-alist-cp
                                                    clause '((,env . env))))))
                            :expand (,(car (last clause)))))
                     (and stable-under-simplificationp
                          '(:use ((:instance svex-eval-equiv-necc
                                   (x (svex-concat width x rest))
                                   (y (svex-concat width y rest))))
                            :in-theory (e/d (4vec-rsh 4vec-shift-core 4vec-concat svex-apply logtails-equal)
                                            (svex-eval-equiv-necc)))))))

     (local
      (defretd <fn>-switch-vars-shift-concat-any-bind
        (implies (and (bind-free '((offset2 . offset2) (signal2 . signal2)) (offset2 signal2))
                      (svex-eval-equiv (svex-concat width (svex-rsh offset lookup) 0)
                                       (svex-concat width (svex-rsh offset2 (svex-lookup signal2 network)) 0))
                      (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose-lookup signal inverse)) 0)
                                       (svex-concat width (svex-rsh offset2 (svex-compose-lookup signal2 inverse)) 0))
                      (svex-lookup signal2 network)
                      (not (svex-lookup signal network)))
                 (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose compose inverse)) rest)
                                  (svex-concat width (svex-rsh offset2 (svex-compose
                                                                        (neteval-ordering-or-null-compile
                                                                         x signal2 network)
                                                                        inverse))
                                               rest)))
        :hints(("Goal" :in-theory (enable <fn>-switch-vars-shift-concat-any)))
        :fn neteval-ordering-or-null-compile-split))

     (defretd <fn>-switch-vars-concat
       (implies (and (svex-eval-equiv (svex-concat width (svex-rsh offset lookup) 0)
                                      (svex-concat width (svex-rsh offset2 (svex-lookup signal2 network)) 0))
                     (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose-lookup signal inverse)) 0)
                                      (svex-concat width (svex-rsh offset2 (svex-compose-lookup signal2 inverse)) 0))
                     (svex-lookup signal2 network)
                     (not (svex-lookup signal network)))
                (svex-eval-equiv (svex-concat width (svex-compose compose inverse) rest)
                                 (svex-concat width
                                              (svex-compose
                                               (neteval-sigordering-compile
                                                x signal2 offset2 network)
                                               inverse)
                                              rest)))
       :hints(("Goal" ;; :in-theory (enable neteval-sigordering-compile)
               :induct (switch-vars-concat-ind x offset offset2 width)
               :expand ((neteval-sigordering-compile x signal2 offset2 network)
                        <call>)
               :do-not-induct t)
              '(:in-theory (enable neteval-ordering-or-null-compile-split-switch-vars-shift-concat-any-bind))
              ;; '(:in-theory (e/d (svex-compose-of-rsh-under-eval-equiv-rev)
              ;;                   (svex-compose-of-rsh-under-eval-equiv)))
              ))
     
     (defcong svex-alist-eval-equiv svex-eval-equiv
       (neteval-sigordering-compile-split x signal offset lookup network) 5))

   (define svar-decomp-neteval-sigordering-compile ((dec svar-decomp-p)
                                                    (x neteval-ordering-p)
                                                    (signal svar-p)
                                                    (offset natp)
                                                    (comp-net svex-alist-p)
                                                    (decomp-net svex-alist-p)
                                                    (decomp svar-decomptable-p))
     :measure (svar-decomp-count dec)
     :returns (val svex-p)
     :verify-guards :after-returns
     (b* ((var (svar-decomp-case dec
                 :segment dec.var
                 :remainder dec.var))
          (sigord (cdr (hons-assoc-equal var (neteval-ordering-fix x))))
          (look ;; (svex-rsh offset 
           (svex-compose (svex-compose-lookup ;; var
                          signal comp-net)
                         (svar-decomptable->subst decomp)))
          (val1 (if sigord
                    (neteval-sigordering-compile-split sigord signal offset ;; var 0
                                                       look decomp-net)
                  ;; ????
                  (svex-rsh offset (svex-var signal))
                  ;; look
                  )))
       (svar-decomp-case dec
         :segment (svex-concat dec.width val1 (svar-decomp-neteval-sigordering-compile
                                               dec.rest x signal (+ dec.width (lnfix offset))
                                               comp-net decomp-net decomp))
         :remainder val1))
     ///

     (defcong svex-alist-eval-equiv svex-eval-equiv
       (svar-decomp-neteval-sigordering-compile dec x signal offset comp-net decomp-net decomp)
       6 ;; decomp-net
       )

     (local (defthm member-svar-decomp-remainder->var-when-subsetp
              (implies (and (subsetp-equal (svar-decomp-vars dec) super)
                            (svar-decomp-case dec :remainder))
                       (member-equal (svar-decomp-remainder->var dec) super))
              :hints(("Goal" :in-theory (enable svar-decomp-vars)))))

     (local (defthm member-svar-decomp-segment->var-when-subsetp
              (implies (and (subsetp-equal (svar-decomp-vars dec) super)
                            (svar-decomp-case dec :segment))
                       (member-equal (svar-decomp-segment->var dec) super))
              :hints(("Goal" :in-theory (enable svar-decomp-vars)))))

     (local (defthm subsetp-svar-decomp-vars-of-shift
              (implies (and (subsetp-equal (svar-decomp-vars dec) super)
                            (svar-decomp-shift offset dec))
                       (subsetp-equal (svar-decomp-vars (svar-decomp-shift offset dec)) super))
              :hints(("Goal" :in-theory (enable svar-decomp-shift svar-decomp-vars)))))

     (local (defthm svar-decomp-vars-of-lookup
              (implies (and (svar-p var)
                            (hons-assoc-equal var decomp))
                       (subsetp-equal (svar-decomp-vars (cdr (hons-assoc-equal var decomp)))
                                      (svar-decomptable-vars decomp)))
              :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

     (local (defthm neteval-sigordering-fix-under-iff
              (neteval-sigordering-fix x)))

     (local (defthm cons-under-iff
              (cons x y)))

     (local (defthm neteval-sigordering-compile-under-iff
              (neteval-sigordering-compile x var offset network)))

     (local (defthm svex-compose-under-iff
              (svex-compose x a)))



     (local (defretd <fn>-switch-vars-equiv
              (implies (and (case-split
                              (svex-eval-equiv (svex-rsh offset lookup)
                                               (svex-rsh offset2 (svex-lookup signal2 network))))
                            (case-split
                              (svex-eval-equiv (svex-rsh offset (svex-compose-lookup signal inverse))
                                               (svex-rsh offset2 (svex-compose-lookup signal2 inverse))))
                            (svex-lookup signal2 network)
                            (not (svex-lookup signal network)))
                       (equal (svex-eval-equiv (svex-compose compose inverse)
                                               (svex-compose
                                                (neteval-sigordering-compile
                                                 x signal2 offset2 network)
                                                inverse))
                              t))
              :hints (("goal" :in-theory (enable <fn>-switch-vars)))
              :fn neteval-sigordering-compile-split))

     (local
      (defretd <fn>-switch-vars-concat-equiv
        (implies (and (case-split (svex-eval-equiv (svex-concat width (svex-rsh offset lookup) 0)
                                                   (svex-concat width (svex-rsh offset2 (svex-lookup signal2 network)) 0)))
                      (case-split
                        (svex-eval-equiv (svex-concat width (svex-rsh offset (svex-compose-lookup signal inverse)) 0)
                                         (svex-concat width (svex-rsh offset2 (svex-compose-lookup signal2 inverse)) 0)))
                      (svex-lookup signal2 network)
                      (not (svex-lookup signal network)))
                 (equal (svex-eval-equiv (svex-concat width (svex-compose compose inverse) rest)
                                         (svex-concat width
                                                      (svex-compose
                                                       (neteval-sigordering-compile
                                                        x signal2 offset2 network)
                                                       inverse)
                                                      rest))
                        t))
        :hints(("Goal" :in-theory (enable <fn>-switch-vars-concat)))
        :fn neteval-sigordering-compile-split))

     (local
      (defthmd prop-for-svar-decomp-neteval-sigordering-compile-aux
        (implies (and (not (intersectp-equal (svex-alist-keys comp1)
                                             (svar-decomptable-vars decomp)))
                      (no-duplicatesp-equal (svar-decomptable-vars decomp))
                      (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                      (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                                     (svex-alist-keys comp1))
                      (hons-assoc-equal decomp-key (svar-decomptable-fix decomp))
                      ;; (subsetp-equal (svar-decomp-vars dec) (svar-decomptable-vars decomp))
                      (let ((shift (svar-decomp-shift offset
                                                      (cdr (hons-assoc-equal (svar-fix decomp-key)
                                                                             (svar-decomptable-fix decomp))))))
                        (and shift
                             (equal dec shift))))
                 (svex-eval-equiv (SVEX-COMPOSE (SVAR-DECOMP-NETEVAL-SIGORDERING-COMPILE
                                                 dec
                                                 X decomp-key
                                                 offset COMP1
                                                 (SVEX-ALIST-TO-DECOMP COMP1 DECOMP)
                                                 DECOMP)
                                                (SVAR-DECOMPTABLE->INVERSE DECOMP))
                                  (SVEX-compose
                                   (svar-decomp->svex dec)
                                   (APPEND
                                    (SVEX-ALIST-COMPOSE
                                     (NETEVAL-ORDERING-COMPILE
                                      X
                                      (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                                     (SVAR-DECOMPTABLE->INVERSE DECOMP))
                                    (SVAR-DECOMPTABLE->INVERSE DECOMP)))))
        :hints(("Goal" :induct (SVAR-DECOMP-NETEVAL-SIGORDERING-COMPILE
                                dec
                                X decomp-key
                                offset COMP1
                                decomp-net
                                DECOMP)
                :expand ((:free (look) (svar-decomp->svex (svar-decomp-shift offset look))))
                :do-not-induct t)
               (and stable-under-simplificationp
                    '(:in-theory (enable svex-alist-to-decomp
                                         svex-alist-decomptable-recompose
                                         svex-compose-lookup
                                         lookup-of-svar-decomptable->inverse-under-svex-eval-equiv
                                         NETEVAL-SIGORDERING-COMPILE-SPLIT-SWITCH-VARS-EQUIV
                                         NETEVAL-SIGORDERING-COMPILE-SPLIT-SWITCH-VARS-concat-EQUIV
                                         ))))))

     ;; (local
     ;;  (defthm prop-for-svar-decomp-neteval-sigordering-compile-aux2
     ;;    (implies (and (not (intersectp-equal (svex-alist-keys comp1)
     ;;                                         (svar-decomptable-vars decomp)))
     ;;                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
     ;;                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
     ;;                  (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
     ;;                                 (svex-alist-keys comp1))
     ;;                  (hons-assoc-equal decomp-key (svar-decomptable-fix decomp))
     ;;                  ;; (subsetp-equal (svar-decomp-vars dec) (svar-decomptable-vars decomp))
     ;;                  (let ((shift (svar-decomp-shift offset
     ;;                                                  (cdr (hons-assoc-equal (svar-fix decomp-key)
     ;;                                                                         (svar-decomptable-fix decomp))))))
     ;;                    (and shift
     ;;                         (equal (svar-decomp-fix dec) shift))))
     ;;             (svex-eval-equiv (SVEX-COMPOSE (SVAR-DECOMP-NETEVAL-SIGORDERING-COMPILE
     ;;                                             dec
     ;;                                             X decomp-key
     ;;                                             offset COMP1
     ;;                                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP)
     ;;                                             DECOMP)
     ;;                                            (SVAR-DECOMPTABLE->INVERSE DECOMP))
     ;;                              (SVEX-compose
     ;;                               (svar-decomp->svex dec)
     ;;                               (APPEND
     ;;                                (SVEX-ALIST-COMPOSE
     ;;                                 (NETEVAL-ORDERING-COMPILE
     ;;                                  X
     ;;                                  (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;                                 (SVAR-DECOMPTABLE->INVERSE DECOMP))
     ;;                                (SVAR-DECOMPTABLE->INVERSE DECOMP)))))
     ;;    :hints (("goal" :use ((:instance prop-for-svar-decomp-neteval-sigordering-compile-aux
     ;;                           (dec (svar-decomp-fix dec))))))))


     (local (defthm svar-decomp-shift-0
              (equal (svar-decomp-shift 0 x)
                     (svar-decomp-fix x))
              :hints(("Goal" :in-theory (enable svar-decomp-shift)))))

     (fty::deffixequiv svar-decomp-neteval-sigordering-compile)

     ;; (local (defcong svex-alist-compose-equiv svex-alist-compose-equiv (append x y) 2
     ;;          :hints ((and stable-under-simplificationp
     ;;                       `(:expand (,(car (last clause))))))))

     (local (defthm append-svex-alist-reduce-under-svex-alist-eval-equiv
              (svex-alist-eval-equiv (append (svex-alist-reduce keys x) x) x)
              :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))


     (defthm prop-for-svar-decomp-neteval-sigordering-compile
       (implies (and (not (intersectp-equal (svex-alist-keys comp1)
                                            (svar-decomptable-vars decomp)))
                     (no-duplicatesp-equal (svar-decomptable-vars decomp))
                     (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                     (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                                    (svex-alist-keys comp1))
                     (hons-assoc-equal (svar-fix decomp-key) decomp))
                (svex-eval-equiv (SVEX-COMPOSE (SVAR-DECOMP-NETEVAL-SIGORDERING-COMPILE
                                                (CDR (HONS-ASSOC-EQUAL (svar-fix decomp-key)
                                                                       DECOMP))
                                                X decomp-key
                                                0 COMP1
                                                (SVEX-ALIST-TO-DECOMP COMP1 DECOMP)
                                                DECOMP)
                                               (SVAR-DECOMPTABLE->INVERSE DECOMP))
                                 (SVEX-LOOKUP
                                  decomp-key
                                  (SVEX-ALIST-FROM-DECOMP
                                   (APPEND
                                    (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                                    (SVEX-IDENTITY-SUBST (SVAR-DECOMPTABLE-VARS DECOMP)))
                                   DECOMP))))
       :hints(("Goal" :use ((:instance prop-for-svar-decomp-neteval-sigordering-compile-aux
                             (dec (svar-decomp-fix (CDR (HONS-ASSOC-EQUAL (svar-fix decomp-key)
                                                                          DECOMP))))
                             (decomp-key (svar-fix decomp-key))
                             (offset 0)))
               :in-theory (e/d (svex-alist-from-decomp
                                svex-alist-decomptable-recompose)
                               (svar-decomp-neteval-sigordering-compile))
               :do-not-induct t))
       :otf-flg t))

   (defines from-decomp-ordering
     ;; The ordering is in terms of decomposed variables.  We want to create one
     ;; in terms of the non-decomposed variables.  To do this for the decomposed
     ;; variables, we go through the decomptable and for each non-decomp
     ;; variable bound, we create a neteval-sigordering based on its
     ;; decomposition.  But we also need to translate the part involving the
     ;; non-decomposed variables.
     :ruler-extenders :lambdas
     (define from-decomp-ordering ((x neteval-ordering-p)
                                   (decomp svar-decomptable-p))
       :measure (nat-list-measure (list (neteval-ordering-count x) 2 0))
       :returns (new-x neteval-ordering-p)
       :verify-guards nil
       (append (from-decomp-ordering-decomp-vars x (alist-keys (svar-decomptable-fix decomp)) decomp)
               (from-decomp-ordering-non-decomp-vars x decomp)))
     
     ;; Going through all the keys in decomp to produce a neteval-ordering that
     ;; covers all decomposed variables.
     (define from-decomp-ordering-decomp-vars ((x neteval-ordering-p)
                                               (decomp-keys svarlist-p)
                                               (decomp svar-decomptable-p))
       :measure (nat-list-measure (list (neteval-ordering-count x) 1 (len decomp-keys)))
       :returns (new-x neteval-ordering-p)
       (b* (((when (Atom decomp-keys)) nil)
            (var (svar-fix (car decomp-keys)))
            (look  (hons-assoc-equal var decomp))
            ((unless look)
             (from-decomp-ordering-decomp-vars x (cdr decomp-keys) decomp))
            (dec (cdr look)))
         (cons (cons var (from-decomp-ordering-decomp-vars-decomp-sigordering dec x ;; var 0
                                                                              decomp))
               (from-decomp-ordering-decomp-vars x (cdr decomp-keys) decomp))))


     ;; Dec is the suffix at offset of the decomp entry for signal.  We
     ;; concatenate together the transformed sigorderings for the remaining parts of dec.
     (define from-decomp-ordering-decomp-vars-decomp-sigordering ((dec svar-decomp-p)
                                                                  (x neteval-ordering-p)
                                                                  ;; (signal svar-p)
                                                                  ;; (offset natp)
                                                                  (decomp svar-decomptable-p))
       ;; (declare (ignorable offset))
       :measure (nat-list-measure (list (neteval-ordering-count x) 0 (svar-decomp-count dec)))
       :returns (new-x neteval-sigordering-p)
       (b* (((mv var ?width) (svar-decomp-case dec
                               :segment (mv dec.var dec.width)
                               :remainder (mv dec.var nil)))
            (sigord (cdr (hons-assoc-equal var (neteval-ordering-fix x))))
            (new-sigord (if sigord
                            (from-decomp-ordering-sigord sigord ;; signal
                                                         ;; signal offset
                                                         ;; var 0
                                                         ;; width
                                                         decomp)
                          (make-neteval-sigordering-remainder :ord (make-neteval-ordering-or-null-null)))))
         (svar-decomp-case dec
           :segment (neteval-sigordering-concat
                     dec.width new-sigord
                     (from-decomp-ordering-decomp-vars-decomp-sigordering
                      dec.rest x ;; signal (+ dec.width (lnfix offset))
                      decomp))
           :remainder new-sigord)))

     ;; The relevant signal for the signal ordering produced here is either
     ;;  1) a key in svar-decomptable, as when called through
     ;; from-decomp-ordering-decomp-vars-decomp-sigordering from from-decomp-ordering-decomp-vars
     ;;  2) a variable not in the decomptable vars nor keys, as when called by from-decomp-ordering-non-decomp-vars.

     ;; We transform sigordering x in the decomposed space to a sigordering in the
     ;; composed space.  Signal/offset will be the context for evaluating the
     ;; resulting sigordering, decomp-signal/decomp-offset are the context for
     ;; evaluating the input sigordering.

     (define from-decomp-ordering-sigord ((x neteval-sigordering-p)
                                          ;; (signal svar-p)
                                          ;; (offset natp)
                                          ;; (decomp-signal svar-p)
                                          ;; (decomp-offset natp)
                                          ;; (relevant-width maybe-natp)
                                          (decomp svar-decomptable-p))
       :measure (nat-list-measure (list (neteval-sigordering-count x) 0 0))
       :returns (new-x neteval-sigordering-p)
       ;; (declare (ignorable offset decomp-signal decomp-offset))
       (neteval-sigordering-case x
         :segment (b* ((ord (from-decomp-ordering-ordering-or-null x.ord
                                                                   ;; signal offset decomp-signal decomp-offset relevant-width
                                                                   decomp)))
                    ;; (if (or (not relevant-width) (< x.width (lnfix relevant-width)))
                    (make-neteval-sigordering-segment
                     :width x.width
                     :ord ord
                     :rest (from-decomp-ordering-sigord x.rest ;; signal (+ x.width (lnfix offset)) decomp-signal decomp-offset (and relevant-width (- (lnfix relevant-width) x.width))
                                                        decomp))
                    ;; (make-neteval-sigordering-remainder :ord ord)
                    )
         :remainder (make-neteval-sigordering-remainder
                     :ord (from-decomp-ordering-ordering-or-null x.ord ;; signal
                                                                 ;; decomp-signal
                                                                 decomp))))

     (define from-decomp-ordering-ordering-or-null ((x neteval-ordering-or-null-p)
                                                    ;; (signal svar-p)
                                                    ;; (offset natp)
                                                    ;; (decomp-signal svar-p)
                                                    ;; (decomp-offset natp)
                                                    ;; (relevant-width maybe-natp)
                                                    (decomp svar-decomptable-p))
       :measure (nat-list-measure (list (neteval-ordering-or-null-count x) 0 0))
       :returns (new-x neteval-ordering-or-null-p)
       ;; (declare (ignorable signal decomp-signal))
       (neteval-ordering-or-null-case x
         :null (make-neteval-ordering-or-null-null)
         :ordering ;; (if (and ;; (hons-assoc-equal (svar-fix signal) x.ord)
         ;;          (hons-assoc-equal (svar-fix signal) (svar-decomptable-fix decomp)))
         ;;     ;; if signal is a key in decomp (therefore a variable in
         ;;     ;; the non-decomposed space and not the decomposed space) 
         ;;     ;; the LHS of from-decomp-ordering-ordering-or-null-prop reduces to (svex-var signal).
         ;;     (make-neteval-ordering-or-null-null)
         (make-neteval-ordering-or-null-ordering
          :ord (from-decomp-ordering x.ord decomp))))
     
     (define from-decomp-ordering-non-decomp-vars ((x neteval-ordering-p)
                                                   (decomp svar-decomptable-p))
       :measure (nat-list-measure (list (neteval-ordering-count x) 0 0))
       :returns (new-x neteval-ordering-p)
       (b* ((x (neteval-ordering-fix x))
            ((when (atom x)) nil)
            ((cons signal sigordering) (car x))
            ((when (or (member-equal signal (svar-decomptable-vars decomp))
                       (hons-assoc-equal signal (svar-decomptable-fix decomp))))
             (from-decomp-ordering-non-decomp-vars (cdr x) decomp)))
         (cons (cons signal (from-decomp-ordering-sigord sigordering ;; signal 0 signal 0
                                                         decomp))
               (from-decomp-ordering-non-decomp-vars (cdr x) decomp))))
     ///
     (verify-guards from-decomp-ordering)


     (defun-sk from-decomp-ordering-sigord-prop (x comp1 decomp-net decomp)
       (forall (signal offset)
               (implies ;; (svex-lookup signal comp1)
                (not (member-equal (svar-fix signal) (svar-decomptable-vars decomp)))
                (svex-eval-equiv
                 (neteval-sigordering-compile (from-decomp-ordering-sigord x decomp) signal offset COMP1)
                 (svex-compose
                  (NETEVAL-sigORDERING-COMPILE-split x signal offset
                                                     (svex-compose (svex-compose-lookup signal comp1)
                                                                   (svar-decomptable->subst decomp))
                                                     decomp-net)
                  (svar-decomptable->inverse decomp)))))
       :rewrite :direct)

     (local (in-theory (disable from-decomp-ordering-sigord-prop)))

     (defun-sk from-decomp-ordering-ordering-or-null-prop (x comp1 decomp-net decomp)
       (forall (signal)
               (implies ;; (svex-lookup signal comp1)
                (not (member-equal (svar-fix signal) (svar-decomptable-vars decomp)))
                (svex-eval-equiv
                 (neteval-ordering-or-null-compile (from-decomp-ordering-ordering-or-null x decomp) signal COMP1)
                 ;; if signal is a key of decomp, then it is not bound in
                 ;; decomp-net and so the neteval-ordering-or-null-compile of it
                 ;; (below) will reduce to the identity, i.e. (svex-var signal).
                 ;; Then, since it's not in the decomptable vars, it isn't bound
                 ;; in the inverse either so all this reduces to (svex-var
                 ;; signal).  What do we want instead?
                 (svex-compose
                  ;; (if (hons-assoc-equal (svar-fix signal) (svar-decomptable-fix decomp))
                  
                  (neteval-ordering-or-null-compile-split
                   x signal
                   (svex-compose (svex-compose-lookup signal comp1)
                                 (svar-decomptable->subst decomp))
                   decomp-net)
                  (svar-decomptable->inverse decomp)))))
       :rewrite :direct)

     (local (in-theory (disable from-decomp-ordering-ordering-or-null-prop)))


     (defun-sk from-decomp-ordering-decomp-vars-decomp-sigordering-prop (dec x comp1 decomp-net decomp)
       (forall (signal offset)
               (implies (hons-assoc-equal (svar-fix signal) (svar-decomptable-fix decomp))
                        (svex-eval-equiv
                         ;; (svex-lookup signal
                         (neteval-sigordering-compile (from-decomp-ordering-decomp-vars-decomp-sigordering
                                                       dec x decomp)
                                                      signal offset COMP1)
                         (svex-compose
                          (svar-decomp-neteval-sigordering-compile
                           dec x signal offset comp1 decomp-net decomp)
                          (svar-decomptable->inverse decomp)))))
       :rewrite :direct)

     (local (in-theory (disable from-decomp-ordering-decomp-vars-decomp-sigordering-prop)))

     (local (in-theory (disable append acl2::consp-of-append)))

     (local (in-theory (disable from-decomp-ordering
                                from-decomp-ordering-decomp-vars
                                from-decomp-ordering-non-decomp-vars
                                from-decomp-ordering-sigord
                                from-decomp-ordering-ordering-or-null
                                from-decomp-ordering-decomp-vars-decomp-sigordering)))

     ;; (defret member-svar-decomp-vars-of-<fn>-when-no-duplicate-vars
     ;;     (implies (and (svar-p key)
     ;;                   (hons-assoc-equal var (svar-decomptable-fix x))
     ;;                   (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x)))
     ;;                   (no-duplicatesp-equal (svar-decomptable-vars x)))
     ;;              (iff (member-equal key (svar-decomp-vars
     ;;                                       (cdr (hons-assoc-equal var x))))
     ;;                   (and domainvar
     ;;                        (equal var domainvar))))
     ;;     :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys)
     ;;             :induct <call>
     ;;             :expand ((svar-decomptable-vars x)))))


     ;; (local (defthm svex-alist-eval-equiv-special-case
     ;;          (implies (and (svex-lookup key rest)
     ;;                        (svex-eval-equiv (svex-lookup key rest) (svex-x)))
     ;;                   (svex-alist-eval-equiv (cons (cons key (svex-x)) rest)
     ;;                                    rest))
     ;;          :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

     (local (defthm svar-decomp-vars-of-lookup
              (implies (and (svar-p var)
                            (hons-assoc-equal var decomp))
                       (subsetp-equal (svar-decomp-vars (cdr (hons-assoc-equal var decomp)))
                                      (svar-decomptable-vars decomp)))
              :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

     ;; (local (defthmd lemma
     ;;          (IMPLIES
     ;;           (AND
     ;;            (SVEX-ALIST-EVAL-EQUIV
     ;;             decomp-vars-result
     ;;             (SVEX-ALIST-REDUCE
     ;;              (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
     ;;              (APPEND
     ;;               (SVEX-ALIST-COMPOSE
     ;;                (SVAR-DECOMPTABLE->SUBST DECOMP)
     ;;                (APPEND
     ;;                 (SVEX-ALIST-COMPOSE
     ;;                  (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;                  (SVAR-DECOMPTABLE->INVERSE DECOMP))
     ;;                 (SVAR-DECOMPTABLE->INVERSE DECOMP)))
     ;;               (SVEX-ALIST-REMOVEKEYS
     ;;                (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;                (SVEX-ALIST-COMPOSE
     ;;                 (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;                 (SVAR-DECOMPTABLE->INVERSE DECOMP))))))
     ;;            (SVEX-ALIST-EVAL-EQUIV
     ;;             non-decomp-vars-result
     ;;             (SVEX-ALIST-REMOVEKEYS
     ;;              (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
     ;;              (SVEX-ALIST-REMOVEKEYS
     ;;               (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;               (SVEX-ALIST-REMOVEKEYS
     ;;                (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;                (SVEX-ALIST-COMPOSE
     ;;                 (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;                 (SVAR-DECOMPTABLE->INVERSE DECOMP))))))
     ;;            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;                                   (SVEX-ALIST-KEYS COMP1)))
     ;;            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;                                   (SVEX-ALIST-VARS COMP1)))
     ;;            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
     ;;            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
     ;;            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
     ;;                           (SVEX-ALIST-KEYS COMP1)))
     ;;           (SVEX-ALIST-COMPOSE-EQUIV
     ;;            (APPEND decomp-vars-result non-decomp-vars-result)
     ;;            (APPEND
     ;;             (SVEX-ALIST-COMPOSE
     ;;              (SVAR-DECOMPTABLE->SUBST DECOMP)
     ;;              (APPEND
     ;;               (SVEX-ALIST-COMPOSE
     ;;                (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;                (SVAR-DECOMPTABLE->INVERSE DECOMP))
     ;;               (SVAR-DECOMPTABLE->INVERSE DECOMP)))
     ;;             (SVEX-ALIST-REMOVEKEYS
     ;;              (SVAR-DECOMPTABLE-VARS DECOMP)
     ;;              (SVEX-ALIST-COMPOSE
     ;;               (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
     ;;               (SVAR-DECOMPTABLE->INVERSE DECOMP))))))
     
     (local (defthm append-svex-alist-reduce-under-svex-alist-eval-equiv
              (svex-alist-eval-equiv (append (svex-alist-reduce keys x) x) x)
              :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))
     
     (local (defthmd from-decomp-ordering-lemma
              (IMPLIES
               (AND
                (SVEX-ALIST-EVAL-EQUIV
                 decomp-vars-result
                 (SVEX-ALIST-REDUCE
                  (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                  (SVEX-ALIST-FROM-DECOMP
                   (APPEND (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                           (SVEX-IDENTITY-SUBST (SVAR-DECOMPTABLE-VARS DECOMP)))
                   DECOMP)))
                (SVEX-ALIST-EVAL-EQUIV
                 non-decomp-vars-result
                 (SVEX-ALIST-REMOVEKEYS
                  (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                  (SVEX-ALIST-REMOVEKEYS
                   (SVAR-DECOMPTABLE-VARS DECOMP)
                   (SVEX-ALIST-FROM-DECOMP
                    (APPEND
                     (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                     (SVEX-IDENTITY-SUBST (SVAR-DECOMPTABLE-VARS DECOMP)))
                    DECOMP))))
                (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                       (SVEX-ALIST-KEYS COMP1)))
                (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                       (SVEX-ALIST-VARS COMP1)))
                (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
                (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
                (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                               (SVEX-ALIST-KEYS COMP1)))
               (equal (SVEX-ALIST-COMPOSE-EQUIV
                       (APPEND decomp-vars-result non-decomp-vars-result)
                       (SVEX-ALIST-FROM-DECOMP
                        (NETEVAL-ORDERING-COMPILE X (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                        DECOMP))
                      t))
              :hints(("Goal" :in-theory (enable svex-alist-compose-equiv))
                     (and stable-under-simplificationp
                          (let ((wit (acl2::find-call-lst 'svex-alist-compose-equiv-witness clause)))
                            `(:clause-processor (acl2::generalize-with-alist-cp clause '((,wit . key))))))
                     (and stable-under-simplificationp
                          '(:in-theory (enable svex-alist-from-decomp
                                               svex-alist-decomptable-recompose
                                               svex-alist-compose-equiv))))))

     (std::defret-mutual <fn>-correct
       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1)))
          (svex-alist-compose-equiv
           (neteval-ordering-compile new-x COMP1)
           (SVEX-ALIST-FROM-DECOMP
            (NETEVAL-ORDERING-COMPILE x
                                      (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
            DECOMP)))
         :hints ('(:expand (;; (:free (net) (neteval-ordering-compile x net))
                            <call>
                            ;; (:free (net) (neteval-ordering-compile new-x net))
                            )
                   :in-theory (enable from-decomp-ordering-lemma)
                   ;; :in-theory (enable svex-alist-from-decomp
                   ;;                    svex-alist-decomptable-recompose)
                   ;; (and stable-under-simplificationp
                   ;;      '(:expand ((:free (x) <call>))))
                   )
                 
                 
                 )
         :fn from-decomp-ordering)
       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1))
               (subsetp-equal (svarlist-fix decomp-keys) (alist-keys (svar-decomptable-fix decomp))))
          (svex-alist-eval-equiv
           (neteval-ordering-compile new-x COMP1)
           (svex-alist-reduce decomp-keys
                              (SVEX-ALIST-FROM-DECOMP
                               (append (NETEVAL-ORDERING-COMPILE x
                                                                 (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                                       (svex-identity-subst (svar-decomptable-vars decomp)))
                               DECOMP))))
         :hints ('(:expand (;; (:free (net) (neteval-ordering-compile x net))
                            <call>
                            ;; (svar-decomptable-vars decomp)
                            ;; (svar-decomptable-fix decomp)
                            (:free (x) (svex-alist-reduce decomp-keys x))
                            (svarlist-fix decomp-keys)
                            ;; (:free (net) (neteval-ordering-compile new-x net))
                            )
                   :in-theory (enable svex-alist-from-decomp
                                      svex-alist-decomptable-recompose))
                 ;; :in-theory (enable alist-keys))
                 ;; (and stable-under-simplificationp
                 ;;      '(:expand ((:free (x) <call>))))
                 )
         :fn from-decomp-ordering-decomp-vars)

       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1))
               ;; (member-equal (svar-fix signal) (alist-keys (svar-decomptable-fix decomp)))
               (subsetp-equal (svar-decomp-vars dec) (svar-decomptable-vars decomp))
               ;; (let ((offs (svar-decomp-shift offset
               ;;                                (cdr (hons-assoc-equal (svar-fix signal)
               ;;                                                       (svar-decomptable-fix decomp))))))
               ;;   (and offs
               ;;        (equal dec offs)))
               )
          ;; (svex-eval-equiv
          ;;  ;; (svex-lookup signal
          ;;  (neteval-sigordering-compile new-x signal offset COMP1)
          ;;  (svex-compose
          ;;   (svex-compose (svar-decomp->svex dec)
          ;;                 (NETEVAL-ORDERING-COMPILE x
          ;;                                           (SVEX-ALIST-TO-DECOMP COMP1 DECOMP)))
          ;;   (svar-decomptable->inverse decomp)))
          (from-decomp-ordering-decomp-vars-decomp-sigordering-prop dec x comp1
                                                                    (svex-alist-to-decomp comp1 decomp)
                                                                    decomp)
          )
         :hints ((and stable-under-simplificationp
                      `(:computed-hint-replacement
                        ((let ((wit (acl2::find-call-lst 'from-decomp-ordering-decomp-vars-decomp-sigordering-prop-witness clause)))
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,wit) . signal)
                                                                                        ((mv-nth '1 ,wit) . offset))))))
                        :expand (,(car (last clause))
                                 ;; (:free (net) (neteval-ordering-compile x net))
                                 <call>
                                 (svar-decomp-vars dec)
                                 (svar-decomp->svex dec)
                                 (:free (offset) (neteval-sigordering-compile '(:remainder (:null)) signal offset comp1))
                                 (neteval-ordering-or-null-compile '(:null) signal comp1)
                                 (:free (x signal offset comp-net decomp-net decomp)
                                  (svar-decomp-neteval-sigordering-compile dec x signal offset comp-net decomp-net decomp))
                                 ;; (svar-decomptable-vars decomp)
                                 ;; (svar-decomptable-fix decomp)
                                 ;; (:free (x) (svex-alist-reduce decomp-keys x))
                                 ;; (svarlist-fix decomp-keys)
                                 ;; (:free (net) (neteval-ordering-compile new-x net))
                                 )
                        ;; :in-theory (enable lookup-of-svar-decomptable->inverse-under-svex-eval-equiv)
                        ))
                 ;; (and stable-under-simplificationp
                 ;;      '(:in-theory (enable svex-alist-from-decomp
                 ;;                      svex-alist-to-decomp
                 ;;                      svex-alist-decomptable-recompose)))
                 ;; :in-theory (enable alist-keys))
                 ;; (and stable-under-simplificationp
                 ;;      '(:expand ((:free (x) <call>))))
                 )
         :fn from-decomp-ordering-decomp-vars-decomp-sigordering)
       
       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1)))
          (svex-alist-eval-equiv
           (neteval-ordering-compile new-x COMP1)
           (svex-alist-removekeys
            (alist-keys (svar-decomptable-fix decomp))
            (svex-alist-removekeys
             (svar-decomptable-vars decomp)
             (SVEX-ALIST-FROM-DECOMP
              (append (NETEVAL-ORDERING-COMPILE x
                                                (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                      (svex-identity-subst (svar-decomptable-vars decomp)))
              DECOMP)))))
         :hints ('(:expand ((:free (net) (neteval-ordering-compile x net))
                            <call>
                            (:free (vars a b) (svex-alist-removekeys vars (cons a b)))
                            (:free (x y a) (svex-alist-compose (cons x y) a))
                            ;; (:free (net) (neteval-ordering-compile new-x net))
                            )
                   :in-theory (enable svex-alist-from-decomp
                                      svex-alist-to-decomp
                                      svex-alist-decomptable-recompose
                                      svex-acons)
                   :do-not-induct t)
                 (and stable-under-simplificationp
                      '(:in-theory (enable svex-compose-lookup)))
                 ;; (and stable-under-simplificationp
                 ;;      '(:expand ((:free (x) <call>))))
                 )
         :fn from-decomp-ordering-non-decomp-vars)
       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1)))
          ;; (implies ;; (svex-lookup signal comp1)
          ;;  (not (member-equal (svar-fix signal) (svar-decomptable-vars decomp)))
          ;;       (svex-eval-equiv
          ;;        (svex-compose
          ;;         (NETEVAL-sigORDERING-COMPILE x decomp-signal decomp-offset (svex-alist-to-decomp comp1 decomp))
          ;;         (svar-decomptable->inverse decomp))
          ;;        (neteval-sigordering-compile (from-decomp-ordering-sigord x signal offset decomp-signal decomp-offset decomp)
          ;;                                     signal offset COMP1)))
          (from-decomp-ordering-sigord-prop x comp1
                                            (svex-alist-to-decomp comp1 decomp)
                                            decomp)
          )
         :hints ((and stable-under-simplificationp
                      `(:computed-hint-replacement
                        ((let ((wit (acl2::find-call-lst 'from-decomp-ordering-sigord-prop-witness clause)))
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,wit) . signal)
                                                                                        ((mv-nth '1 ,wit) . offset))))))
                        :expand (,(car (last clause)))))
                 (and stable-under-simplificationp
                      '(:expand ((:free (net signal offset lookup) (neteval-sigordering-compile-split x signal offset lookup net))
                                 <call>
                                 (:free (ord signal offset net)
                                  (neteval-sigordering-compile
                                   (neteval-sigordering-remainder ord) signal offset net))
                                 (:free (width ord rest signal offset net)
                                  (neteval-sigordering-compile
                                   (neteval-sigordering-segment width ord rest) signal offset net))
                                 )))
                 (and stable-under-simplificationp
                      '(:expand (<call>))))
         :fn from-decomp-ordering-sigord)

       (defret <fn>-correct
         (IMPLIES
          (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-KEYS COMP1)))
               (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                      (SVEX-ALIST-VARS COMP1)))
               (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
               (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
               (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                              (SVEX-ALIST-KEYS COMP1)))
          (from-decomp-ordering-ordering-or-null-prop x comp1
                                                      (svex-alist-to-decomp comp1 decomp)
                                                      decomp)
          ;; (implies ;; (svex-lookup signal comp1)
          ;;       (not (member-equal (svar-fix signal) (svar-decomptable-vars decomp)))
          ;;       (svex-eval-equiv
          ;;        (neteval-ordering-or-null-compile (from-decomp-ordering-ordering-or-null x signal decomp-signal decomp) signal COMP1)
          ;;        (svex-compose
          ;;         (NETEVAL-ordering-or-null-COMPILE x decomp-signal (svex-alist-to-decomp comp1 decomp))
          ;;         (svar-decomptable->inverse decomp))))
          )
         :hints ((and stable-under-simplificationp
                      `(:computed-hint-replacement
                        ((let ((wit (acl2::find-call-lst 'from-decomp-ordering-ordering-or-null-prop-witness clause)))
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '((,wit . signal))))))
                        :expand (,(car (last clause))
                                 (:free (net signal) (neteval-ordering-or-null-compile x signal net))
                                 <call>
                                 (:free (net signal)
                                  (neteval-ordering-or-null-compile
                                   '(:null) signal net))
                                 (:free (ord net signal)
                                  (neteval-ordering-or-null-compile
                                   (neteval-ordering-or-null-ordering ord) signal net))
                                 (svex-compose (svex-var signal) (svar-decomptable->inverse decomp))
                                 )
                        :in-theory (enable neteval-ordering-or-null-compile-split)
                        :do-not-induct t))
                 (and stable-under-simplificationp
                      '(:in-theory (enable svex-alist-to-decomp
                                           svex-alist-decomptable-recompose
                                           svex-alist-from-decomp)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable neteval-sigordering-compile-when-signal-not-in-network)))
                 )
         :fn from-decomp-ordering-ordering-or-null)
       :skip-others t))))


(defthm from-decomp-of-to-decomp-preserves-netcomp-p
  (implies (and (not (intersectp-equal (svex-alist-keys comp1)
                                       (svar-decomptable-vars decomp)))
                (not (intersectp-equal (svex-alist-vars comp1)
                                       (svar-decomptable-vars decomp)))
                (no-duplicatesp-equal (svar-decomptable-vars decomp))
                (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                               (svex-alist-keys comp1))
                (netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp)))
           (netcomp-p (svex-alist-from-decomp compdec2 decomp) comp1))
  :hints ('(:computed-hint-replacement
            ((and stable-under-simplificationp
                  (let ((ordering (acl2::find-call-lst 'netcomp-p-eval-equiv-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,ordering . ordering)))))))
            :expand ((netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp))))
          (and stable-under-simplificationp
               '(:use ((:instance netcomp-p-suff
                        (comp (svex-alist-from-decomp
                               (neteval-ordering-compile ordering
                                                         (svex-alist-to-decomp comp1 decomp))
                               decomp))
                        (decomp comp1)
                        (ordering (from-decomp-ordering ordering decomp))))))))

(local
 (progn

   (defthm svex-compose-of-append-first-superset
     (implies (subsetp (svex-vars x) (svex-alist-keys a))
              (svex-eval-equiv (svex-compose x (append a b))
                               (svex-compose x a)))
     :hints(("Goal" :in-theory (enable svex-eval-equiv))))

   (std::defret-mutual svex-eval-of-append-when-non-intersectp-first
     (defret <fn>-of-append-when-non-intersectp-first
       (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix env2))))
                (equal (svex-eval x (append env2 env))
                       val))
       :hints ('(:expand ((:free (env) <call>)
                          (svex-vars x)))
               (and stable-under-simplificationp
                    '(:in-theory (enable svex-env-boundp))))
       :fn svex-eval)
     (defret <fn>-of-append-when-non-intersectp-first
       (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix env2))))
                (equal (svexlist-eval x (append env2 env))
                       vals))
       :hints ('(:expand ((:free (env) <call>)
                          (svexlist-vars x))))
       :fn svexlist-eval)
     :mutual-recursion svex-eval)

   (defthm svex-compose-of-append-first-non-intersect
     (implies (not (intersectp-equal (svex-vars x) (svex-alist-keys a)))
              (svex-eval-equiv (svex-compose x (append a b))
                               (svex-compose x b)))
     :hints(("Goal" :in-theory (enable svex-eval-equiv))))

   (defthm svex-compose-of-append-second-non-intersect
     (implies (not (intersectp-equal (svex-vars x) (svex-alist-keys a)))
              (svex-eval-equiv (svex-compose x (append b a))
                               (svex-compose x b)))
     :hints(("Goal" :in-theory (enable svex-eval-equiv))))

   (local (defthm svar-decomp-vars-of-lookup
            (implies (and (svar-p var)
                          (hons-assoc-equal var decomp))
                     (subsetp-equal (svar-decomp-vars (cdr (hons-assoc-equal var decomp)))
                                    (svar-decomptable-vars decomp)))
            :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

   (local (defthm not-intersectp-subset
            (implies (and (not (intersectp-equal y x))
                          (subsetp z y))
                     (not (intersectp-equal x z)))
            :hints ((acl2::set-reasoning))))

   (local (defthm svex-call-rsh-0-under-eval-equiv
            (svex-eval-equiv (svex-call 'rsh (list 0 x))
                             x)
            :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply)))))

   (defthm svar-decomp->svex-of-decomptable-inverse
     (implies (and (no-duplicatesp-equal (svar-decomptable-vars decomp))
                   (hons-assoc-equal (svar-fix key) decomp))
              (svex-eval-equiv
               (svex-compose (svar-decomp->svex (cdr (hons-assoc-equal (svar-fix key) decomp)))
                             (svar-decomptable->inverse decomp))
               (svex-var key)))
     :hints(("Goal" :in-theory (enable svar-decomptable->inverse
                                       svar-decomptable-vars))))

   (defthm svar-decomp->svex-of-decomptable-inverse-composed
     (implies (and (no-duplicatesp-equal (svar-decomptable-vars decomp))
                   (hons-assoc-equal (svar-fix key) decomp))
              (svex-eval-equiv
               (svex-compose (svar-decomp->svex (cdr (hons-assoc-equal (svar-fix key) decomp)))
                             (svex-alist-compose (svar-decomptable->inverse decomp) a))
               (svex-compose-lookup key a)))
     :hints (("goal" :use ((:instance svex-compose-of-compose
                            (x (svar-decomp->svex (cdr (hons-assoc-equal (svar-fix key) decomp))))
                            (a (svar-decomptable->inverse decomp)) (b a)))
              :in-theory (disable svex-compose-of-compose))))


   (local (defthm not-intersectp-subset2
            (implies (and (not (intersectp-equal x y))
                          (subsetp z y))
                     (not (intersectp-equal x z)))
            :hints ((acl2::set-reasoning))))))


(defthm from-decomp-of-to-decomp
  (implies (and (not (intersectp-equal (svex-alist-keys x)
                                       (svar-decomptable-vars decomp)))
                (not (intersectp-equal (svex-alist-vars x)
                                       (svar-decomptable-vars decomp)))
                (no-duplicatesp-equal (svar-decomptable-vars decomp))
                (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                               (svex-alist-keys x)))
           (svex-alist-compose-equiv (svex-alist-from-decomp (svex-alist-to-decomp x decomp) decomp)
                                  x))
  :hints(("Goal" :in-theory (enable svex-alist-from-decomp svex-alist-to-decomp
                                    svex-alist-decomptable-recompose
                                    svex-alist-compose-equiv
                                    svex-compose-lookup))
         (and stable-under-simplificationp
              (let ((key (acl2::find-call-lst 'SVEX-ALIST-compose-equiv-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,key . key))))))))

















