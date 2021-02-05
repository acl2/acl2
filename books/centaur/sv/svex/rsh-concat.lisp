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
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable ash logapp)))

(defthm 4vec-concat-associative
  (implies (and (2vec-p w1)
                (<= 0 (2vec->val w1))
                (2vec-p w2)
                (<= 0 (2vec->val w2)))
           (equal (4vec-concat w1 (4vec-concat w2 a b) c)
                  (if (<= (2vec->val w1) (2vec->val w2))
                      (4vec-concat w1 a c)
                    (4vec-concat w2 a (4vec-concat (2vec (- (2vec->val w1)
                                                            (2vec->val w2)))
                                                   b c)))))
  :hints(("Goal" :in-theory (enable 4vec-concat))
         (acl2::logbitp-reasoning)))

(defthm 4vec-concat-of-0
  (equal (4vec-concat 0 lo hi)
         (4vec-fix hi))
  :hints(("Goal" :in-theory (enable 4vec-concat))))

(defthm 4vec-rsh-0
    (equal (4vec-rsh 0 x)
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core))))

(defthm 4vec-rsh-of-rsh
  (implies (and (2vec-p sh1)
                (<= 0 (2vec->val sh1))
                (2vec-p sh2)
                (<= 0 (2vec->val sh2)))
           (equal (4vec-rsh sh1 (4vec-rsh sh2 x))
                  (4vec-rsh (2vec (+ (2vec->val sh1)
                                     (2vec->val sh2)))
                            x)))
  :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core))))


(defthmd equal-of-logapp
  (equal (equal (logapp w x1 y1) (logapp w x2 y2))
         (and (equal (ifix y1) (ifix y2))
              (equal (loghead w x1) (loghead w x2))))
  :hints ((acl2::logbitp-reasoning :prune-examples nil)))

(defthm 4vec-rsh-of-concat
  (implies (and (2vec-p sh)
                (<= 0 (2vec->val sh))
                (2vec-p w)
                (<= 0 (2vec->val w)))
           (equal (4vec-rsh sh (4vec-concat w x y))
                  (if (< (2vec->val sh) (2vec->val w))
                      (4vec-concat (2vec (- (2vec->val w)
                                            (2vec->val sh)))
                                   (4vec-rsh sh x) y)
                    (4vec-rsh (2vec (- (2vec->val sh)
                                       (2vec->val w)))
                              y))))
  :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-concat))))

(defthmd equal-of-4vec-fix
  (equal (equal (4vec-fix x) (4vec-fix y))
         (and (equal (4vec->upper x) (4vec->upper y))
              (equal (4vec->lower x) (4vec->lower y))))
  :hints(("Goal" :in-theory (enable 4vec-fix 4vec->upper 4vec->lower 4vec-p))))

(defthmd equal-of-4vec-concat
  (implies (and (syntaxp (not (and (quotep y1) (quotep y2)
                                   (equal y1 y2)
                                   (equal (acl2::unquote y1) (4vec-z)))))
                (2vec-p w)
                (<= 0 (2vec->val w)))
           (equal (equal (4vec-concat w x1 y1) (4vec-concat w x2 y2))
                  (and (equal (4vec-fix y1) (4vec-fix y2))
                       (equal (4vec-concat w x1 (4vec-z))
                              (4vec-concat w x2 (4vec-z))))))
  :hints(("Goal" :in-theory (enable 4vec-concat equal-of-4vec-fix
                                    equal-of-logapp))))




(define match-concat ((x svex-p))
  :returns (mv (matchedp)
               (width natp :rule-classes :type-prescription)
               (lsbs svex-p)
               (msbs svex-p))
  (b* ((x (svex-fix x)))
    (svex-case x
      :call (b* (((unless (and (eq x.fn 'concat)
                               (eql (len x.args) 3)))
                  (mv nil 0 (svex-x) x))
                 (width (car x.args)))
              (svex-case width
                :quote (if (and (2vec-p width.val)
                                (<= 0 (2vec->val width.val)))
                           (mv t (2vec->val width.val)
                               (second x.args) (third x.args))
                         (mv nil 0 (svex-x) x))
                :otherwise (mv nil 0 (svex-x) x)))
      :otherwise (mv nil 0 (svex-x) x)))
  ///
  (local (defthm 2vec-of-4vec->lower
           (implies (2vec-p x)
                    (equal (2vec (4vec->lower x))
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable 2vec 2vec-p)))))

  (defretd match-concat-correct
    (equal (4vec-concat (2vec width) (svex-eval lsbs env)
                        (svex-eval msbs env))
           (svex-eval x env))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4veclist-nth-safe))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-concat)))))

  (defret vars-of-match-concat
    (implies (not (member v (svex-vars x)))
             (and (not (member v (svex-vars lsbs)))
                  (not (member v (svex-vars msbs)))))
    :hints(("Goal" :in-theory (enable svexlist-vars)
            :expand ((svexlist-vars (cddr (svex-call->args x)))
                     (svexlist-vars (cdr (svex-call->args x)))
                     (svexlist-vars (svex-call->args x))))))

  ;; This is the rule to enable if you want to reason about this function's
  ;; semantics.
  (defretd match-concat-correct-rewrite-svex-eval-of-x
    (implies matchedp
             (equal (svex-eval x env)
                    (4vec-concat (2vec width) (svex-eval lsbs env)
                                 (svex-eval msbs env))))
    :hints(("Goal" :in-theory '(match-concat-correct))))

  (defret svex-count-of-match-concat-lsbs
    (implies matchedp
             (< (svex-count lsbs) (svex-count x)))
    :rule-classes :linear)

  (defret svex-count-of-match-concat-msbs
    (implies matchedp
             (< (svex-count msbs) (svex-count x)))
    :rule-classes :linear))


(define match-ext ((x svex-p))
  :returns (mv (matchedp)
               (width natp :rule-classes :type-prescription)
               (lsbs svex-p)
               (sign-extend-p))
  (b* ((x (svex-fix x)))
    (svex-case x
      :call (b* (((unless (and (or (eq x.fn 'zerox)
                                   (eq x.fn 'signx))
                               (eql (len x.args) 2)))
                  (mv nil 0 x nil))
                 (width (car x.args)))
              (svex-case width
                :quote (if (and (2vec-p width.val)
                                (<= 0 (2vec->val width.val)))
                           (mv t (2vec->val width.val)
                               (second x.args)
                               (eq x.fn 'signx))
                         (mv nil 0 x nil))
                :otherwise (mv nil 0 x nil)))
      :otherwise (mv nil 0 x nil)))
  ///
  (local (defthm 2vec-of-4vec->lower
           (implies (2vec-p x)
                    (equal (2vec (4vec->lower x))
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable 2vec 2vec-p)))))

  (defretd match-ext-correct
    (implies matchedp
             (and (implies sign-extend-p
                           (equal (4vec-sign-ext (2vec width) (svex-eval lsbs env))
                                  (svex-eval x env)))
                  (implies (not sign-extend-p)
                           (equal (4vec-zero-ext (2vec width) (svex-eval lsbs env))
                                  (svex-eval x env)))))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4veclist-nth-safe))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-zero-ext 4vec-sign-ext)))))

  (defret vars-of-match-ext
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars lsbs))))
    :hints(("Goal" :in-theory (enable svexlist-vars)
            :expand ((svexlist-vars (cdr (svex-call->args x)))
                     (svexlist-vars (svex-call->args x))))))

  ;; This is the rule to enable if you want to reason about this function's
  ;; semantics.
  (defretd match-ext-correct-rewrite-svex-eval-of-x
    (implies matchedp
             (equal (svex-eval x env)
                    (if sign-extend-p
                        (4vec-sign-ext (2vec width) (svex-eval lsbs env))
                      (4vec-zero-ext (2vec width) (svex-eval lsbs env)))))
    :hints(("Goal" :in-theory '(match-ext-correct))))

  (defret svex-count-of-match-ext-lsbs
    (implies matchedp
             (< (svex-count lsbs) (svex-count x)))
    :rule-classes :linear))



(define match-rsh ((x svex-p))
  :returns (mv (matchedp)
               (shift natp :rule-classes :type-prescription)
               (subexp svex-p))
  (b* ((x (svex-fix x)))
    (svex-case x
      :call (b* (((unless (and (eq x.fn 'rsh)
                               (eql (len x.args) 2)))
                  (mv nil 0 x))
                 (shift (car x.args)))
              (svex-case shift
                :quote (if (and (2vec-p shift.val)
                                (<= 0 (2vec->val shift.val)))
                           (mv t (2vec->val shift.val)
                               (second x.args))
                         (mv nil 0 x))
                :otherwise (mv nil 0 x)))
      :otherwise (mv nil 0 x)))
  ///
  (local (defthm 2vec-of-4vec->lower
           (implies (2vec-p x)
                    (equal (2vec (4vec->lower x))
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable 2vec 2vec-p)))))

  (defretd match-rsh-correct
    (equal (4vec-rsh (2vec shift) (svex-eval subexp env))
           (svex-eval x env))
    :hints(("Goal" :in-theory (enable svex-apply svexlist-eval 4veclist-nth-safe))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-rsh 4vec-shift-core)))))

  (defret vars-of-match-rsh
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars subexp))))
    :hints(("Goal" :in-theory (enable svexlist-vars)
            :expand ((svexlist-vars (cddr (svex-call->args x)))
                     (svexlist-vars (cdr (svex-call->args x)))
                     (svexlist-vars (svex-call->args x))))))

  ;; This is the rule to enable if you want to reason about this function's
  ;; semantics.
  (defretd match-rsh-correct-rewrite-svex-eval-of-x
    (implies matchedp
             (equal (svex-eval x env)
                    (4vec-rsh (2vec shift) (svex-eval subexp env))))
    :hints(("Goal" :in-theory '(match-rsh-correct))))

  (defret svex-count-of-match-rsh
    (implies matchedp
             (< (svex-count subexp) (svex-count x)))
    :rule-classes :linear))




(define svex-rsh ((sh natp) (x svex-p))
  :returns (rsh svex-p)
  :measure (svex-count x)
  (if (zp sh)
      (svex-fix x)
    (b* (((when (svex-case x :quote))
          (svex-quote (4vec-rsh (2vec sh) (svex-quote->val x))))
         ((mv matchedp shift subexp) (match-rsh x))
         ((when matchedp)
          (svex-call 'rsh (list (svex-quote (2vec (+ shift sh))) subexp)))
         ((mv matchedp width ?lsbs msbs) (match-concat x))
         ((when (and matchedp
                     (>= sh width)))
          (svex-rsh (- sh width) msbs))
         ((mv matchedp width ?lsbs signxp) (match-ext x))
         ((when (and matchedp (>= sh width) (not signxp)))
          0))
      (svex-call 'rsh (list (svex-quote (2vec sh)) x))))
  ///
  (deffixequiv svex-rsh)

  (local (defthm 4vec-rsh-of-zero-ext
           (implies (and (>= sh w) (natp sh) (natp w))
                    (equal (4vec-rsh (2vec sh) (4vec-zero-ext (2vec w) x))
                           0))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-zero-ext))
                  (logbitp-reasoning))))

  (defthm svex-rsh-correct
    (equal (svex-eval (svex-rsh sh x) env)
           (svex-eval (svex-call 'rsh (list (svex-quote (2vec (nfix sh))) x)) env))
    :hints(("Goal" :induct t)
           '(:in-theory (enable svex-apply 4veclist-nth-safe svexlist-eval
                                match-rsh-correct-rewrite-svex-eval-of-x
                                match-ext-correct-rewrite-svex-eval-of-x
                                match-concat-correct-rewrite-svex-eval-of-x)
             :expand ((:free (f a) (svex-eval (svex-call f a) env))
                      (svex-eval 0 env)))))

  (defthm svex-rsh-vars
    (implies (not (member v (svex-vars x)))
             (not (member v (svex-vars (svex-rsh sh x)))))))

(define svex-concat ((w natp) (x svex-p) (y svex-p))
  :returns (concat svex-p)
  :measure (+ (svex-count x) (svex-count y))
  :prepwork ((local (defthm svex-count-when-quote
                      (implies (svex-case x :quote)
                               (equal (svex-count x) 1))
                      :hints(("Goal" :in-theory (enable svex-count))))))
  (if (zp w)
      (svex-fix y)
    (b* (((when (and (svex-case x :quote)
                     (svex-case y :quote)))
          (svex-quote (4vec-concat (2vec w) (svex-quote->val x) (svex-quote->val y))))
         ((mv matched width xl ?xh) (match-concat x))
         ((when (and matched (<= w width)))
          (svex-concat w xl y))
         ((mv matched width xl ?signxp) (match-ext x))
         ((when (and matched (<= w width)))
          (svex-concat w xl y))
         ((unless (svex-case x :quote))
          (svex-call 'concat (list (svex-quote (2vec w)) x y)))
         ((mv matched width yl yh) (match-concat y))
         ((when (and matched (svex-case yl :quote)))
          (svex-concat (+ w width)
                       (svex-quote (4vec-concat (2vec w)
                                                (svex-quote->val x)
                                                (svex-quote->val yl)))
                       yh)))
      (svex-call 'concat (list (svex-quote (2vec w)) x y))))
  ///
  (deffixequiv svex-concat)

  (local (defthm 4vec-concat-of-zero-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-concat (2vec w1) (4vec-zero-ext (2vec w2) x) y)
                           (4vec-concat (2vec w1) x y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-concat-of-sign-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-concat (2vec w1) (4vec-sign-ext (2vec w2) x) y)
                           (4vec-concat (2vec w1) x y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-sign-ext))
                  (logbitp-reasoning))))

  (defthm svex-concat-correct
    (equal (svex-eval (svex-concat w x y) env)
           (svex-eval (svex-call 'concat (list (svex-quote (2vec (nfix w))) x y)) env))
    :hints(("Goal" :induct t)
           '(:in-theory (enable svex-apply 4veclist-nth-safe svexlist-eval
                                match-concat-correct-rewrite-svex-eval-of-x
                                match-ext-correct-rewrite-svex-eval-of-x)
             :expand ((:free (f a) (svex-eval (svex-call f a) env))
                      (svex-eval 0 env)))))

  (defthm svex-concat-vars
    (implies (and (not (member v (svex-vars x)))
                  (not (member v (svex-vars y))))
             (not (member v (svex-vars (svex-concat w x y)))))))


(define svex-zerox ((w natp) (x svex-p))
  :returns (concat svex-p)
  :measure (svex-count x)
  (if (zp w)
      0
    (b* (((when (svex-case x :quote))
          (svex-quote (4vec-zero-ext (2vec w) (svex-quote->val x))))
         ((mv matched width xl ?xh) (match-concat x))
         ((when (and matched (<= w width)))
          (svex-zerox w xl))
         ((mv matched width xl ?signxp) (match-ext x))
         ((when (and matched (<= w width)))
          (svex-zerox w xl)))
      (svex-call 'zerox (list (svex-quote (2vec w)) x))))
  ///
  (deffixequiv svex-zerox)

  (local (defthm 4vec-zero-ext-of-concat
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-zero-ext (2vec w1) (4vec-concat (2vec w2) x y))
                           (4vec-zero-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-zero-ext-of-sign-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-zero-ext (2vec w1) (4vec-sign-ext (2vec w2) x))
                           (4vec-zero-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-zero-ext-of-zero-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-zero-ext (2vec w1) (4vec-zero-ext (2vec w2) x))
                           (4vec-zero-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-zero-ext))
                  (logbitp-reasoning))))

  (local (Defthm 4vec-zero-ext-of-0
           (equal (4vec-zero-ext 0 x) 0)
           :hints(("Goal" :in-theory (enable 4vec-zero-ext)))))

  (defthm svex-zerox-correct
    (equal (svex-eval (svex-zerox w x) env)
           (svex-eval (svex-call 'zerox (list (svex-quote (2vec (nfix w))) x)) env))
    :hints(("Goal" :induct t)
           '(:in-theory (enable svex-apply 4veclist-nth-safe svexlist-eval
                                match-concat-correct-rewrite-svex-eval-of-x
                                match-ext-correct-rewrite-svex-eval-of-x)
             :expand ((:free (f a) (svex-eval (svex-call f a) env))
                      (svex-eval 0 env)))))

  (defthm svex-zerox-vars
    (implies (and (not (member v (svex-vars x))))
             (not (member v (svex-vars (svex-zerox w x)))))))

(define svex-signx ((w natp) (x svex-p))
  :returns (concat svex-p)
  :measure (svex-count x)
  (if (zp w)
      (svex-x)
    (b* (((when (svex-case x :quote))
          (svex-quote (4vec-sign-ext (2vec w) (svex-quote->val x))))
         ((mv matched width xl ?xh) (match-concat x))
         ((when (and matched (<= w width)))
          (svex-signx w xl))
         ((mv matched width xl signxp) (match-ext x))
         ((when matched)
          (if (<= w width)
              (svex-signx w xl)
            (if signxp
                (svex-signx width xl)
              (svex-zerox width xl)))))
      (svex-call 'signx (list (svex-quote (2vec w)) x))))
  ///
  (deffixequiv svex-signx)

  (local (defthm 4vec-sign-ext-of-concat
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-sign-ext (2vec w1) (4vec-concat (2vec w2) x y))
                           (4vec-sign-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-sign-ext-of-sign-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-sign-ext (2vec w1) (4vec-sign-ext (2vec w2) x))
                           (4vec-sign-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-sign-ext-of-zero-ext
           (implies (and (natp w1) (natp w2) (<= w1 w2))
                    (equal (4vec-sign-ext (2vec w1) (4vec-zero-ext (2vec w2) x))
                           (4vec-sign-ext (2vec w1) x)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-sign-ext-of-sign-ext-less
           (implies (and (natp w1) (natp w2) (> w1 w2))
                    (equal (4vec-sign-ext (2vec w1) (4vec-sign-ext (2vec w2) x))
                           (4vec-sign-ext (2vec w2) x)))
           :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-sign-ext-of-sign-ext-less-2
           (implies (and (natp w1)
                         (equal y (4vec-sign-ext (2vec w2) x))
                         (natp w2)
                         (> w1 w2))
                    (equal (4vec-sign-ext (2vec w1) y)
                           (4vec-sign-ext (2vec w2) x)))
           :hints(("Goal" :in-theory (enable 4vec-sign-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (defthm 4vec-sign-ext-of-zero-ext-less
           (implies (and (natp w1) (natp w2) (> w1 w2))
                    (equal (4vec-sign-ext (2vec w1) (4vec-zero-ext (2vec w2) x))
                           (4vec-zero-ext (2vec w2) x)))
           :hints(("Goal" :in-theory (enable 4vec-zero-ext 4vec-sign-ext))
                  (logbitp-reasoning))))

  (local (Defthm 4vec-sign-ext-of-0
           (equal (4vec-sign-ext 0 x) (4vec-x))
           :hints(("Goal" :in-theory (enable 4vec-sign-ext)))))

  (defthm svex-signx-correct
    (equal (svex-eval (svex-signx w x) env)
           (svex-eval (svex-call 'signx (list (svex-quote (2vec (nfix w))) x)) env))
    :hints(("Goal" :induct t)
           '(:in-theory (enable svex-apply 4veclist-nth-safe svexlist-eval
                                match-concat-correct-rewrite-svex-eval-of-x
                                match-ext-correct-rewrite-svex-eval-of-x)
             :expand ((:free (f a) (svex-eval (svex-call f a) env))
                      (svex-eval 0 env)))))

  (defthm svex-signx-vars
    (implies (and (not (member v (svex-vars x))))
             (not (member v (svex-vars (svex-signx w x)))))))


(define svex-call* ((fn fnsym-p)
                    (args svexlist-p))
  :returns (call svex-p)
  (b* ((fn (fnsym-fix fn))
       (args (svexlist-fix args))
       ((when (svexlist-quotesp args))
        (svex-quote (svex-apply fn (svexlist-unquote args))))
       ((unless (and (member fn '(concat rsh signx zerox))
                     (if (eq fn 'concat)
                         (eql (len args) 3)
                       (eql (len args) 2))))
        (svex-call fn args))
       (arg1 (car args))
       (arg1-val (svex-case arg1
                   :quote (and (2vec-p arg1.val)
                               (2vec->val arg1.val))
                   :otherwise nil))
       ((unless (and arg1-val (<= 0 arg1-val)))
        (svex-call fn args)))
    (case fn
      (concat (svex-concat arg1-val (cadr args) (caddr args)))
      (rsh    (svex-rsh arg1-val (cadr args)))
      (zerox  (svex-zerox arg1-val (cadr args)))
      (t ;; signx
       (svex-signx arg1-val (cadr args)))))
  ///
  (local (defthm 2vec-of-4vec->lower
           (implies (2vec-p x)
                    (equal (2vec (4vec->lower x))
                           (4vec-fix x)))))

  (defret svex-call*-correct
    (equal (svex-eval call env)
           (svex-eval (svex-call fn args) env))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-apply
                                     svexlist-eval
                                     4veclist-nth-safe)))))

  (defret svex-call*-vars
    (implies (not (member v (svexlist-vars args)))
             (not (member v (svex-vars call))))))


(defsection svcall*
  :parents (svex)
  :short "Safely construct an @(see svex) for a function call, with evaluation
          of quotes and simplification of concatenations and right-shifts."


  (defun svcall*-fn (fn args)
    (declare (xargs :guard t))
    (b* ((look (assoc fn *svex-op-table*))
         ((unless look)
          (er hard? 'svcall* "Svex function doesn't exist: ~x0" fn))
         (formals (third look))
         ((unless (eql (len formals) (len args)))
          (er hard? 'svcall* "Wrong arity for call of ~x0" fn)))
      `(svex-call* ',fn (list . ,args))))

  (defmacro svcall* (fn &rest args)
    (svcall*-fn fn args)))




