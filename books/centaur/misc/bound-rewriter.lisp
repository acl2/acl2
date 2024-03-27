; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; (depends-on "build/defrec-certdeps/REWRITE-CONSTANT.certdep" :dir :system)
; (depends-on "build/defrec-certdeps/PROVE-SPEC-VAR.certdep" :dir :system)

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :System)
(include-book "clause-processors/unify-subst" :dir :System)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)
(include-book "std/util/defaggrify-defrec" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "tools/match-tree" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


;; Linearly traverse an arithmetic comparison term and replace positive
;; occurrences with lower bounds and negative occurrences with upper bounds.

;; Terminology: If we are trying to prove the inequality
;; (< A B) or (<= A B),
;; then we can soundly [not necessarily completely] replace A by its upper
;; bound and/or B by its lower bound.  We say A is a negative occurrence and B
;; is a positive occcurrence.  If this inequality occurs in a hyp, then the
;; roles of A and B are switched.

;; Arithmetic operators +, *, -, / have simple rules:

;; If (+ A B) occurs positively then A and B are both positive occurrences, and
;; similarly for negative.
;; If (- A) occurs positively then this A is a negative occurrence, and vice versa.
;; If (* A B) occurs positively, then:
;;   - if A is known nonnegative, then B is a positive occurrence
;;   - if A is known nonpositive, then B is a negative occurrence
;; and symmetrically for B and for negative occurrences.
;; If (/ A) occurs positively, then A is a negative occurrence, and vice versa.



(defevaluator-fast boundrw-ev boundrw-ev-lst
  ;; required for meta-extract:
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)

   (cons a b) ;; required for unify

   ;; required for sublis-var
   (acl2-numberp x)
   (binary-* x y)
   (binary-+ x y)
   (unary-- x)
   (unary-/ x)
   (< x y)
   (car x)
   (cdr x)
   (char-code x)
   (characterp x)
   (code-char x)
   (complex x y)
   (complex-rationalp x)
   (coerce x y)
   (cons x y)
   (consp x)
   (denominator x)
   (equal x y)
   (imagpart x)
   (integerp x)
   (intern-in-package-of-symbol x y)
   (numerator x)
   (rationalp x)
   (realpart x)
   (stringp x)
   (symbol-name x)
   (symbol-package-name x)
   (symbolp x)
   (if x y z)
   (not x)

   (< a b)
   (binary-+ a b)
   (unary-- a)
   (binary-* a b)
   (unary-/ a)

   (hide a))
  :namedp t)

(def-meta-extract boundrw-ev boundrw-ev-lst)
(def-unify boundrw-ev boundrw-ev-alist)




(defthm boundrw-ev-of-sublis-var
  (implies (and (pseudo-termp x)
                (not (assoc nil alist)))
           (equal (boundrw-ev (sublis-var alist x) a)
                  (boundrw-ev x (append (boundrw-ev-alist alist a) a))))
  :hints (("goal" :use ((:functional-instance eval-of-sublis-var
                         (cterm-ev boundrw-ev)
                         (cterm-ev-lst boundrw-ev-lst)
                         (cterm-ev-alist boundrw-ev-alist))))
          (and stable-under-simplificationp
               '(:in-theory (enable boundrw-ev-of-fncall-args)))))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

;; defined everywhere
(local (defthm assoc-nonnil-of-append
         (implies x
                  (equal (assoc x (append a b))
                         (or (assoc x a) (assoc x b))))))

(defthm-simple-term-vars-flag
  (defthm boundrw-ev-of-append-substs
    (implies (and (all-keys-bound (simple-term-vars x) a)
                  (pseudo-termp x))
             (equal (boundrw-ev x (append a b))
                    (boundrw-ev x a)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((simple-term-vars x))))
            (and stable-under-simplificationp
                 '(:expand ((pseudo-termp x))
                   :in-theory (enable boundrw-ev-of-fncall-args))))
    :flag simple-term-vars)
  (defthm boundrw-ev-lst-of-append-substs
    (implies (and (all-keys-bound (simple-term-vars-lst x) a)
                  (pseudo-term-listp x))
             (equal (boundrw-ev-lst x (append a b))
                    (boundrw-ev-lst x a)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((simple-term-vars-lst x)))))
    :flag simple-term-vars-lst))




(local (in-theory (disable sublis-var)))

(std::defaggregate boundrw-subst
  ((lhs pseudo-termp)
   (rhs pseudo-termp)
   (alist pseudo-term-substp)))

(std::deflist boundrw-substlist-p (x)
  (boundrw-subst-p x))

(set-state-ok t)

(local (defthm alistp-when-pseudo-term-substp
         (implies (pseudo-term-substp x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable pseudo-term-substp)))))

; Matt K. mod, 1/7/2016: The use of (logbitp-reasoning) makes ACL2(p) with
; waterfall-parallelism enabled complain that "the form (LOGBITP-REASONING) was
; expected to represent an ordinary value, not an error triple (mv erp val
; state), as would be acceptable in a serial execution of ACL2.  So I'll turn
; off waterfall parallelism here.
(local (set-waterfall-parallelism nil))

;; Check whether a term's sign is known.  Returns :nonnegative, :nonpositive, or nil.
(define ts-check-sign ((x pseudo-termp)
                       mfc state)

  :returns (category symbolp)
  (b* ((ts (mfc-ts x mfc state :forcep nil))
       ((unless (integerp ts)) nil))
    (cond ((eql 0 (logand (lognot (logior *ts-positive-integer*
                                          *ts-positive-ratio*
                                          *ts-zero*))
                          ts))
           ;; Its typeset can't be anything other than a positive integer,
           ;; positive rational, or zero.  So it's nonnegative.
           :nonnegative)
          ((eql 0 (logand (lognot (logior *ts-negative-integer*
                                          *ts-negative-ratio*
                                          *ts-zero*))
                          ts))
           :nonpositive)
          (t nil)))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))

  (defret ts-check-sign-nonnegative-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonnegative)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= 0 val)
                    (equal (< 0 val)
                           (not (equal val 0))))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))

  (defret ts-check-sign-nonpositive-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonpositive)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= val 0)
                    (equal (< val 0)
                           (not (equal val 0))))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))

  (defthm ts-check-sign-nonnil-casesplit
    (implies (rewriting-negative-literal `(ts-check-sign ,x ,m ,s))
             (let ((category (ts-check-sign x m s)))
               (iff category
                    (or (equal category :nonpositive)
                        (equal category :nonnegative)))))))


(define ts-check-sign-strict ((x pseudo-termp)
                              mfc state)

  :returns (category symbolp)
  (b* ((ts (mfc-ts x mfc state :forcep nil))
       ((unless (integerp ts)) nil))
    (cond ((eql 0 (logand (lognot (logior *ts-positive-integer*
                                          *ts-positive-ratio*))
                          ts))
           ;; Its typeset can't be anything other than a positive integer,
           ;; positive rational, or zero.  So it's nonnegative.
           :positive)
          ((eql 0 (logand (lognot (logior *ts-negative-integer*
                                          *ts-negative-ratio*))
                          ts))
           :negative)
          (t nil)))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))

  (defret ts-check-sign-strict-positive-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :positive)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (< 0 val))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask
; Matt K. mod 5/2016 (type-set bit for {1}):
                                 bitp-loghead-1))
            (logbitp-reasoning)))

  (defret ts-check-sign-strict-negative-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :negative)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (< val 0))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning)))


  (defthm ts-check-sign-strict-nonnil-casesplit
    (implies (rewriting-negative-literal `(ts-check-sign-strict ,x ,m ,s))
             (let ((category (ts-check-sign-strict x m s)))
               (iff category
                    (or (equal category :positive)
                        (equal category :negative)))))))


(define ts-check-nonzero ((x pseudo-termp)
                       mfc state)

  :returns (nonzerop)
  (b* ((ts (mfc-ts x mfc state :forcep nil)))
    (and (integerp ts)
         (eql 0 (logand (logior *ts-zero*
                                (lognot (logior *ts-positive-integer*
                                                *ts-positive-ratio*
                                                *ts-negative-integer*
                                                *ts-negative-ratio*)))
                        ts))))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))

  (defret ts-check-sign-nonzero-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and nonzerop
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (not (equal 0 val)))))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask
; Matt K. mod 5/2016 (type-set bit for {1}):
                                 bitp-loghead-1))
            (logbitp-reasoning))))

(define ts-check-rational ((x pseudo-termp)
                       mfc state)

  :returns (rationalp)
  (b* ((ts (mfc-ts x mfc state :forcep nil)))
    (and (integerp ts)
         (eql 0 (logand (lognot (logior *ts-positive-integer*
                                        *ts-positive-ratio*
                                        *ts-negative-integer*
                                        *ts-negative-ratio*
                                        *ts-zero*))
                        ts))))
  ///
  (local (defthm logand-with-negative-when-negative
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))
           :hints (("goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                               bitops::ihsext-inductions)))))

  (defret ts-check-rational-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and rationalp
                    (boundrw-ev-meta-extract-contextual-facts a))
               (rationalp val)))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning))))


(define ts-check-sign/rational ((x pseudo-termp) mfc state)
  :returns (category symbolp)
  (or (ts-check-sign x mfc state)
      (ts-check-rational x mfc state))
  ///
  (defret ts-check-sign/rational-nonnegative-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonnegative)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= 0 val)
                    (equal (< 0 val)
                           (not (equal val 0)))))))

  (defret ts-check-sign/rational-nonpositive-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and (equal category :nonpositive)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (rationalp val)
                    (<= val 0)
                    (equal (< val 0)
                           (not (equal val 0)))))))


  (defret ts-check-sign/rational-rational-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and category
                    (boundrw-ev-meta-extract-contextual-facts a))
               (rationalp val)))))


(fty::defoption maybe-rational rationalp :pred maybe-rationalp)

(define maybe-boundp ((direction booleanp)
                      (orig)
                      (new maybe-rationalp))
  
  (b* ((new (maybe-rational-fix new)))
    (or (not new)
        (and (rationalp orig)
             (if direction
                 (<= (rfix orig) new)
               (<= new (rfix orig))))))
  ///
  (defthm maybe-boundp-transitive1
    (implies (and (maybe-boundp dir x1 x2)
                  (maybe-boundp dir x2 x3)
                  (rationalp x2))
             (maybe-boundp dir x1 x3))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (defthm maybe-boundp-transitive2
    (implies (and (maybe-boundp dir x2 x3)
                  (maybe-boundp dir x1 x2)
                  (rationalp x2))
             (maybe-boundp dir x1 x3))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (defthm maybe-boundp-of-nil
    (maybe-boundp dir orig nil))

  (defthm maybe-boundp-of-nonnil
    (implies bound
             (and (equal (maybe-boundp t orig bound)
                         (and (rationalp orig)
                              (<= orig (rfix bound))))
                  (equal (maybe-boundp nil orig bound)
                         (and (rationalp orig)
                              (<= (rfix bound) orig)))))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (defthm maybe-boundp-of-nonnil-direction
    (implies (and (syntaxp (not (equal direction ''t)))
                  direction)
             (equal (maybe-boundp direction orig bound)
                    (maybe-boundp t orig bound)))))

(defsection ts-bounds

  ;; rewriting theory for these ts-upper/lower-bounds correctness proofs
  (local (defun equal-0-of-logand-list (lst x)
           (if (atom lst)
               t
             (and (equal 0 (logand (car lst) x))
                  (equal-0-of-logand-list (cdr lst) x)))))
  (local (defun logior-list (lst)
           (if (atom lst)
               0
             (logior (car lst) (logior-list (Cdr lst))))))
  (local (defthmd equal-0-of-logand-list-implies-equal-0-logand-logior-list
           (iff (equal-0-of-logand-list lst x)
                (equal 0 (logand (logior-list lst) x)))
           :hints (("goal" :induct t)
                   (logbitp-reasoning))))

  (local (defthm equal-0-of-logand-list-open
           (implies (syntaxp (quotep lst))
                    (equal (equal-0-of-logand-list lst x)
                           (if (atom lst)
                               t
                             (and (equal 0 (logand (car lst) x))
                                  (equal-0-of-logand-list (cdr lst) x)))))))
  
  (local (defun find-logand-equal-0-hyp-list (x clause)
           (b* (((when (atom clause)) nil)
                (lit (car clause))
                (rest (find-logand-equal-0-hyp-list x (cdr clause)))
                (first
                 (case-match lit
                   (('not ('equal ''0 ('binary-logand ('quote n) xx)))
                    (and (equal xx x)
                         n))
                   (& nil))))
             (if first
                 (cons first rest)
               rest))))

  (local (defun equal-0-logand-bind-free (x mfc state)
           (declare (xargs :stobjs state
                           :verify-guards nil)
                    (ignore state))
           `((lst . ',(find-logand-equal-0-hyp-list x (mfc-clause mfc))))))
               
  
  (local (defthm equal-0-logand-by-others
           (implies (and (syntaxp (and (quotep c)
                                       (or (rewriting-positive-literal-fn
                                            `(equal '0 (binary-logand ,c ,x)) mfc state)
                                           (rewriting-positive-literal-fn
                                            `(equal (binary-logand ,c ,x) '0) mfc state))))
                         (bind-free (equal-0-logand-bind-free x mfc state) (lst))
                         (equal new-c (logandc2 c (logior-list lst)))
                         (syntaxp (not (equal c new-c)))
                         ;; (syntaxp (prog2$ (cw "x: ~x0~%lst: ~x1~%" x lst) t))
                         (equal-0-of-logand-list lst x)
                         ;; (syntaxp (prog2$ (cw "ok~%") t))
                         )
                    (iff (equal 0 (logand c x))
                         (equal 0 (logand new-c x))))
           :hints(("Goal" :in-theory (enable equal-0-of-logand-list-implies-equal-0-logand-logior-list))
                  (logbitp-reasoning))))


  (local (defthm logand-negatives-equal-0
           (implies (and (< (ifix x) 0)
                         (< (ifix y) 0))
                    (not (equal 0 (logand x y))))))

  (define ts-lower-bound ((x pseudo-termp) mfc state)
    :returns (lower maybe-rationalp :rule-classes :type-prescription)
    (b* ((ts (mfc-ts x mfc state :forcep nil))
         ((unless (integerp ts))
          nil)
         ;; The basic (single-bit) typesets are listed in the def-basic-type-sets form in type-set-a.lisp.
         ;; The ones that are subsets of the rationals are:
         ;; (*ts-)zero(*), one, integer>1, positive-ratio, negative-integer, negative-ratio.
         ;; We order these here by their lower bound: integer>1 has a lower
         ;; bound of 2, one has a lower bound of 1, zero and positive-ratio have
         ;; 0, and the rest have none.  So we take our original TS reflecting
         ;; the possible types of X and ANDC2 out each of these typesets in
         ;; turn.  E.g., first we ANDC2 this with *ts-integer>1* and check if
         ;; that equals 0 -- i.e., if X can be anything besides an integer>1.
         ;; If not, we return the bound this suggests.  If so, we continue with
         ;; the typeset(s) with the next-lower bounds.
         (ts-besides-2+ (logandc2 ts *ts-integer>1*))
         ((when (eql 0 ts-besides-2+)) 2)
         (ts-besides-1+ (logandc2 ts-besides-2+ *ts-one*))
         ((when (eql 0 ts-besides-1+)) 1)
         (ts-besides-0+ (logandc2 ts-besides-1+ (logior *ts-zero* *ts-positive-ratio*)))
         ((when (eql 0 ts-besides-0+)) 0))
      nil)
    ///
  
    (defret <fn>-correct
      (implies (boundrw-ev-meta-extract-contextual-facts a)
               (maybe-boundp nil (boundrw-ev x a) lower))
      :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                             (term x)))
               :in-theory (disable boundrw-ev-meta-extract-typeset
                                   bitops::logand-with-negated-bitmask
                                   bitops::logand-with-bitmask
                                   BITOPS::LOGAND->=-0-LINEAR-2
                                   BITOPS::LOGAND-<-0-LINEAR
                                   BITOPS::UPPER-BOUND-OF-LOGAND)))))

  (define ts-upper-bound ((x pseudo-termp) mfc state)
    :returns (upper maybe-rationalp :rule-classes :type-prescription)
    (b* ((ts (mfc-ts x mfc state :forcep nil))
         ((unless (integerp ts)) nil)
         ;; similar strategy to ts-lower-bound -- see comment there
         (ts-besides-neg1- (logandc2 ts *ts-negative-integer*))
         ((when (eql 0 ts-besides-neg1-)) -1)
         (ts-besides-0- (logandc2 ts-besides-neg1- (logior *ts-negative-ratio* *ts-zero*)))
         ((when (eql 0 ts-besides-0-)) 0)
         (ts-besides-1- (logandc2 ts-besides-0- *ts-one*))
         ((when (eql 0 ts-besides-1-)) 1))
      nil)
    ///
  
    (defret <fn>-correct
      (implies (boundrw-ev-meta-extract-contextual-facts a)
               (maybe-boundp t (boundrw-ev x a) upper))
      :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                             (term x)))
               :in-theory (disable boundrw-ev-meta-extract-typeset
                                   bitops::logand-with-negated-bitmask
                                   bitops::logand-with-bitmask
                                   BITOPS::LOGAND->=-0-LINEAR-2
                                   BITOPS::LOGAND-<-0-LINEAR
                                   BITOPS::UPPER-BOUND-OF-LOGAND)))))

  (define ts-bound ((x pseudo-termp) (direction booleanp) mfc state)
    :returns (bound maybe-rationalp :rule-classes :type-prescription)
    (if direction
        (ts-upper-bound x mfc state)
      (ts-lower-bound x mfc state))
    ///
  
    (defret <fn>-correct
      (implies (and (iff direction1 direction)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (maybe-boundp direction1 (boundrw-ev x a) bound)))

    (defret <fn>-upper-bound-correct-linear
      (implies (and bound
                    direction
                    (boundrw-ev-meta-extract-contextual-facts a))
               (<= (boundrw-ev x a) bound))
      :hints (("goal" :use ((:instance <fn>-correct (direction1 direction)))
               :in-theory (e/d (maybe-boundp) (<fn>-correct <fn>)))))

    (defret <fn>-lower-bound-correct-linear
      (implies (and bound
                    (not direction)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (<= bound (boundrw-ev x a)))
      :hints (("goal" :use ((:instance <fn>-correct (direction1 direction)))
               :in-theory (e/d (maybe-boundp) (<fn>-correct <fn>)))))))



(local
 (defthmd mult-both-sides-preserves-<=
   (implies (and ;; (rationalp x)
                 ;; (rationalp y)
                 (rationalp c)
                 (<= x y)
                 (<= 0 c))
            (<= (* c x) (* c y)))
   :hints (("goal" :nonlinearp t))))

(local
 (defthmd mult-both-sides-preserves-<
   (implies (and ;; (rationalp x)
                 ;; (rationalp y)
                 (rationalp c)
                 (< x y)
                 (< 0 c))
            (< (* c x) (* c y)))
   :hints (("goal" :nonlinearp t))))

(local
 (defthm assoc-in-boundrw-ev-alist
   (implies k
            (equal (assoc k (boundrw-ev-alist x a))
                   (and (assoc k x)
                        (cons k (boundrw-ev (cdr (assoc k x)) a)))))))

(local
 (defthm all-keys-bound-in-boundrw-ev-alist
   (implies (not (member nil keys))
            (equal (all-keys-bound keys (boundrw-ev-alist x a))
                   (all-keys-bound keys x)))
   :hints(("Goal" :in-theory (enable all-keys-bound)))))

(local
 (defthm all-keys-bound-when-subsetp
   (implies (and (subsetp x y)
                 (all-keys-bound y z))
            (all-keys-bound x z))
   :hints(("Goal" :in-theory (enable subsetp all-keys-bound)))))


(defthmd boundrw-dummy-rewrite
  (implies (= a b)
           (equal (< a b) nil)))

(define boundrw-check-bound ((x pseudo-termp)
                             (bound-term pseudo-termp)
                             (direction booleanp)
                             mfc state)
  :returns (ok)
  ;; (b* ((contra-term (if direction
  ;;                       ;; bound-term is upper bound
  ;;                       `(< ,bound-term ,x)
  ;;                     ;; bound-term is lower bound
  ;;                     `(< ,x ,bound-term))))
  ;;   (or (mfc-ap
  ;;        ;; term to contradict:
  ;;        contra-term
  ;;        mfc state
  ;;        :forcep nil)
  ;;       (cw "linear failed to solve: ~x0~%" contra-term)))
  (b* ((hyp-term (if direction
                     ;; `(not (< ,bound-term ,x))
                   ;; `(not (< ,x ,bound-term))
                     '(not (< bound-term x))
                   '(not (< x bound-term))))
       (alist `((bound-term . ,bound-term)
                (x . ,x))))
    (or (mfc-relieve-hyp
         hyp-term
         alist
         '(:rewrite boundrw-dummy-rewrite)
         '(< fake term) 1 mfc state
         :forcep nil :ttreep nil)
        (cw "relieve-hyp failed to solve: ~x0~%" (substitute-into-term hyp-term alist))))
  ///
  (std::defretd <fn>-correct
    (implies (and ok
                  (boundrw-ev-meta-extract-contextual-facts a)
                  (pseudo-termp x))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev bound-term a)))
                  (implies (not direction)
                           (<= (boundrw-ev bound-term a) (boundrw-ev x a))))))

  (defund boundrw-check-bound-hide (x bound-term direction mfc state)
    (declare (xargs :stobjs state
                    :verify-guards nil))
    (boundrw-check-bound x bound-term direction mfc state))

  (defthmd boundrw-check-bound-correct-rw
    (implies (and (rewriting-negative-literal `(boundrw-check-bound ,x ,bound-term ,direction ,mf ,st))
                  (bind-free '((a . a)) (a))
                  (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st)
                  (pseudo-termp x))
             (iff (boundrw-check-bound x bound-term direction mf st)
                  (and (boundrw-check-bound-hide x bound-term direction mf st)
                       (if direction
                           (<= (boundrw-ev x a) (boundrw-ev bound-term a))
                         (<= (boundrw-ev bound-term a) (boundrw-ev x a))))))
    :hints(("Goal" :in-theory (e/d (boundrw-check-bound-hide
                                    boundrw-check-bound-correct)
                                   (boundrw-check-bound))))))

(define boundrw-apply-bound ((x pseudo-termp)
                             (direction booleanp)
                             (bound-list boundrw-substlist-p)
                             mfc state)
  :returns (mv changedp
               (new-x pseudo-termp :hyp (and (pseudo-termp x)
                                             (boundrw-substlist-p bound-list))))
  (b* (((when (atom bound-list)) (mv nil x))
       ((boundrw-subst bound) (car bound-list))
       ((mv unify-ok subst) (simple-one-way-unify bound.lhs x bound.alist))
       ((unless unify-ok)
        (boundrw-apply-bound x direction (cdr bound-list) mfc state))
       (vars-ok (all-keys-bound (simple-term-vars bound.rhs) subst))
       ((unless vars-ok)
        (raise "Bad substitution: unbound vars in RHS: ~x0~%" bound.rhs)
        (boundrw-apply-bound x direction (cdr bound-list) mfc state))
       (subst-ok (not (assoc nil subst)))
       ((unless subst-ok)
        (raise "Bad substitution: NIL bound in unify-subst: ~x0~%" bound)
        (boundrw-apply-bound x direction (cdr bound-list) mfc state))
       ;; (- (cw "hyp was not relieved: ~x0~%" x))
       ;; (res (mfc-rw+ hyp subst 't nil mfc state :forcep nil))
       ;; (- (cw "result of rewriting: ~x0~%" res))

       ;; Is it overkill to call mfc-rw+ on this?  Could have unintended
       ;; consequences; perhaps we just want to evaluate it if variable-free?
       (new-x (mfc-rw+ bound.rhs subst '? nil mfc state :forcep nil :ttreep nil))
       ((unless (pseudo-termp new-x))
        (cw "mfc-rw+ produced non-pseudo-termp: ~x0~%" new-x)
        (boundrw-apply-bound x direction (cdr bound-list) mfc state))
       ((when (boundrw-check-bound x new-x direction mfc state))
        (cw "~x0: ap ~x1~%" x new-x)
        (mv t new-x)))
    (boundrw-apply-bound x direction (cdr bound-list) mfc state))
  ///
  (defret boundrw-apply-bound-correct
    (implies (and (boundrw-ev-meta-extract-contextual-facts a)
                  (pseudo-termp x)
                  (boundrw-substlist-p bound-list))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev new-x a)))
                  (implies (not direction)
                           (<= (boundrw-ev new-x a) (boundrw-ev x a)))))
    :hints (("goal" :induct <call> :expand (<call>)
             :in-theory (enable boundrw-check-bound-correct-rw)))))


;; match-free rune backchain-limit-lst concl max-term hyps nume
(std::defaggrify-defrec linear-lemma)
(std::defaggrify-defrec rewrite-constant)
(std::defaggrify-defrec metafunction-context)


(defthm maybe-rationalp-compound-recognizer
  (equal (maybe-rationalp x)
         (or (rationalp x)
             (not x)))
  :rule-classes :compound-recognizer)

(define boundrw-linear-relieve-hyps ((hyps pseudo-term-listp)
                                     (alist pseudo-term-substp)
                                     rune
                                     (target pseudo-termp)
                                     (bkptr natp)
                                     mfc state)
  :returns (ok)
  (b* (((when (atom hyps)) t)
       (ok (mfc-relieve-hyp (car hyps) alist rune target bkptr mfc state :forcep nil :ttreep nil)))
    (and ok
         (boundrw-linear-relieve-hyps
          (cdr hyps) alist rune target (+ 1 (lnfix bkptr)) mfc state)))
  ///
  (defret <fn>-correct
    :pre-bind ((state st)
               (mfc mf))
    (implies (and (acl2::rewriting-negative-literal `(boundrw-linear-relieve-hyps ,hyps ,alist ,rune ,target ,bkptr ,mf ,st))
                  (bind-free '((a . a)) (a))
                  (boundrw-ev-meta-extract-contextual-facts a)
                  (pseudo-term-listp hyps)
                  (not (assoc-equal nil alist)))
             (iff ok
                  (and (boundrw-ev (conjoin hyps)
                                   (append (boundrw-ev-alist alist a) a))
                       (hide ok))))
    :hints (("goal" :induct (boundrw-linear-relieve-hyps hyps alist rune target bkptr mf st)
             :expand ((:free (x) (hide x))
                      (substitute-into-list hyps alist)))
            ))
  )






(local (in-theory (e/d (match-tree-obj-equals-subst-when-successful
                        ;; match-tree-equals-match-tree-matchedp-when-successful
                        match-tree-alist-opener-theory
                        ;; match-tree-opener-theory
                        ;; equal-of-cons-hyp-open
                        )
                       ;; (match-tree-rewrite)
                       )))


;; (local (defthm assoc-equal-of-cons
;;          (implies (syntaxp (quotep key))
;;                   (equal (assoc-equal key (cons a b))
;;                          (if (equal key (car a))
;;                              a
;;                            (assoc-equal key b))))))

(local (in-theory (e/d (assoc-equal-of-cons-when-keys-known)
                       (assoc-equal))))


(define boundrw-linear-concl-decomp ((concl pseudo-termp))
  :returns (mv shape-okp negatedp
               (lhs pseudo-termp :hyp (pseudo-termp concl))
               (rhs pseudo-termp :hyp (pseudo-termp concl)))
  (treematch concl
             ((< (:? lhs) (:? rhs)) (mv t nil lhs rhs))
             ((not (< (:? lhs) (:? rhs))) (mv t t lhs rhs))
             ;; note not currently processing equality rules
             (& (mv nil nil nil nil)))
  ///
  (defret <fn>-correct
    (implies (and shape-okp
                  (boundrw-ev concl a))
             (and (implies (not negatedp)
                           (< (boundrw-ev lhs a)
                              (boundrw-ev rhs a)))
                  (implies negatedp
                           (<= (boundrw-ev rhs a)
                               (boundrw-ev lhs a)))))))

(local
 (Defsection boundrw-ev-of-append-non-vars
   (local (defthm assoc-equal-when-not-member-strip-cars
            (implies x
                     (iff (member-equal x (strip-cars a))
                          (assoc-equal x a)))
            :hints(("Goal" :in-theory (enable assoc-equal strip-cars)))))
   (defthm-simple-term-vars-flag
     (defthm boundrw-ev-of-append-non-vars
       (implies (not (intersectp-equal (strip-cars new) (simple-term-vars x)))
                (equal (boundrw-ev x (append new old))
                       (boundrw-ev x old)))
       :hints ('(:expand ((simple-term-vars x))
                 :in-theory (enable boundrw-ev-of-nonsymbol-atom
                                    boundrw-ev-of-fncall-args)))
       :flag simple-term-vars)
     (defthm boundrw-ev-lst-of-append-non-vars
       (implies (not (intersectp-equal (strip-cars new) (simple-term-vars-lst x)))
                (equal (boundrw-ev-lst x (append new old))
                       (boundrw-ev-lst x old)))
       :hints ('(:expand ((simple-term-vars-lst x))))
       :flag simple-term-vars-lst))

   (defthm-simple-term-vars-flag
     (defthm boundrw-ev-of-append-subset
       (implies (subsetp-equal (simple-term-vars x) (strip-cars new))
                (equal (boundrw-ev x (append new old))
                       (boundrw-ev x new)))
       :hints ('(:expand ((simple-term-vars x))
                 :in-theory (enable boundrw-ev-of-nonsymbol-atom
                                    boundrw-ev-of-fncall-args)))
       :flag simple-term-vars)
     (defthm boundrw-ev-lst-of-append-subset
       (implies (subsetp-equal (simple-term-vars-lst x) (strip-cars new))
                (equal (boundrw-ev-lst x (append new old))
                       (boundrw-ev-lst x new)))
       :hints ('(:expand ((simple-term-vars-lst x))))
       :flag simple-term-vars-lst))

   (defthm-simple-term-vars-flag
     (defthm boundrw-ev-of-true-list-fix
       (equal (boundrw-ev x (true-list-fix a))
              (boundrw-ev x a))
       :hints ('(:in-theory (enable boundrw-ev-of-nonsymbol-atom
                                    boundrw-ev-of-fncall-args)))
       :flag simple-term-vars)
     (defthm boundrw-ev-lst-of-true-list-fix
       (equal (boundrw-ev-lst x (true-list-fix a))
              (boundrw-ev-lst x a))
       :flag simple-term-vars-lst))))



(define boundrw-linear-eval-bound-term ((bound-term pseudo-termp)
                                        state)
  :returns (bound maybe-rationalp :rule-classes :type-prescription)
  (b* ((vars (simple-term-vars bound-term))
       ((when vars)
        nil)
       ((mv eval-err bound-value) (magic-ev bound-term nil state t nil))
       ((when eval-err)
        nil)
       ((when (not (rationalp bound-value)))
        nil))
    bound-value)
  ///
  (std::defretd <fn>-correct
    (implies (and (boundrw-ev-meta-extract-global-facts)
                  bound
                  (pseudo-termp bound-term))
             (equal bound (boundrw-ev bound-term a)))
    :hints (("Goal" :use ((:instance boundrw-ev-of-append-non-vars
                           (x bound-term) (old nil) (new a)))))))


(define boundrw-linear-candidate-reject-p (new (best maybe-rationalp) (direction booleanp))
  (or (not (rationalp new))
      (b* ((best (maybe-rational-fix best)))
        (and best
             (if direction
                 (<= best new)
               (<= new best))))))

(define boundrw-try-linear-lemma-aux (lemma
                                      (x pseudo-termp)
                                      (direction booleanp)
                                      (best maybe-rationalp)
                                      (ens enabled-structure-p)
                                      mfc state)
  :returns (new-bound maybe-rationalp :rule-classes :type-prescription)
  (b* ((best (maybe-rational-fix best))
       ((unless (weak-linear-lemma-p lemma))
        (raise "Bad linear lemma: ~x0~%" lemma)
        nil)
       ((linear-lemma lemma))
       ((unless (and (natp lemma.nume)
                     (enabled-numep lemma.nume ens)))
        nil)
       ((unless (and (pseudo-termp lemma.concl)
                     (pseudo-term-listp lemma.hyps)))
        (raise "Bad linear lemma (pseudo-terms): ~x0~%" lemma)
        nil)
       ((mv shape-ok negatedp lhs rhs) ;; (< lhs rhs) or (not (< lhs rhs))
        (boundrw-linear-concl-decomp lemma.concl))
       ((unless shape-ok) nil)
       ;; If direction, we are looking for upper bounds, so we want to unify x with LHS if not negated and RHS when negated.
       ((mv x-side other-side)
        (if (xor direction negatedp)
            (mv lhs rhs)
          (mv rhs lhs)))
       ((mv match alist) (simple-one-way-unify x-side x nil))
       ((unless match)
        ;; didn't unify
        nil)
       ((unless (subsetp-eq (simple-term-vars other-side)
                            (strip-cars alist)))
        ;; other-side has free vars
        nil)
       (bound-term (substitute-into-term other-side alist))
       (bound-value (boundrw-linear-eval-bound-term bound-term state))
       ((when (boundrw-linear-candidate-reject-p bound-value best direction))
        ;; already have a bound at least as good
        nil)
       (hyps-ok (boundrw-linear-relieve-hyps lemma.hyps alist lemma.rune x 1 mfc state))
       ((unless hyps-ok)
        nil))
    bound-value)
  ///
  (local (defthm maybe-rational-fix-when-nonnil
           (implies x
                    (equal (maybe-rational-fix x) (rfix x)))
           :hints(("Goal" :in-theory (enable maybe-rational-fix)))))



  (local (std::defret boundrw-linear-eval-bound-term-correct-rw
           (implies (and (bind-free '((a . a)) (a))
                         (boundrw-ev-meta-extract-global-facts)
                         bound
                         (pseudo-termp bound-term))
                    (and (equal (< val bound)
                                (< val (boundrw-ev bound-term a)))
                         (equal (< bound val)
                                (< (boundrw-ev bound-term a) val))))
           :hints (("Goal" :use boundrw-linear-eval-bound-term-correct))
           :fn boundrw-linear-eval-bound-term))


  (local (defthm strip-cars-of-boundrw-ev-alist
           (equal (strip-cars (boundrw-ev-alist x a))
                  (strip-cars x))
           :hints(("Goal" :in-theory (enable boundrw-ev-alist)))))

  (local
   (DEFTHM SIMPLE-ONE-WAY-UNIFY-WITH-BOUNDRW-EV-rw
     (MV-LET (OK SUBST)
       (SIMPLE-ONE-WAY-UNIFY PAT TERM ALIST)
       (IMPLIES
        (AND
         (BIND-FREE
          '((envs . (cons a 'nil)))
          (ENVS)))
        (IFF OK
             (AND (UNIFY-SUCCEEDED PAT TERM ALIST)
                  (BOUNDRW-EV-SIMPLE-ONE-WAY-UNIFY-EQUALITIES
                   PAT TERM SUBST ENVS)))))
     :HINTS (("goal" :use simple-one-way-unify-with-boundrw-ev))))

  (local (in-theory (disable simple-one-way-unify-with-boundrw-ev
                             rfix)))

  (local (in-theory (disable w)))

  (local (defthm candidate-reject-forward-rational
           (implies (not (boundrw-linear-candidate-reject-p bound-value best direction))
                    (rationalp bound-value))
           :hints(("Goal" :in-theory (enable boundrw-linear-candidate-reject-p)))
           :rule-classes :forward-chaining))

  (local (in-theory (disable enabled-numep)))
  
  (defret <fn>-correct
    (implies (and (boundrw-ev-meta-extract-global-facts)
                  (boundrw-ev-meta-extract-contextual-facts a)
                  new-bound
                  (pseudo-termp x)
                  (member-equal lemma
                                (getpropc (car x) 'linear-lemmas nil (w state))))
             (and (implies (and direction)
                           (<= (boundrw-ev x a) new-bound))
                  (implies (and (not direction))
                           (<= new-bound (boundrw-ev x a)))))
    :hints (("goal" :expand (<call>)
             :in-theory (e/d (;; boundrw-check-bound-correct-rw
                              )
                             (boundrw-ev-meta-extract-linear-lemma
                              boundrw-linear-concl-decomp-correct)))
            (and stable-under-simplificationp
                 '(
             :use ((:instance boundrw-ev-meta-extract-linear-lemma
                    (rule lemma)
                    (fn (car x))
                    (st state)
                    (a (APPEND
                        (BOUNDRW-EV-ALIST
                         (MV-NTH 1
                                 (SIMPLE-ONE-WAY-UNIFY
                                  (MV-NTH 3
                                          (BOUNDRW-LINEAR-CONCL-DECOMP (CADDDR LEMMA)))
                                  X NIL))
                         A)
                        A)))
                   (:instance boundrw-ev-meta-extract-linear-lemma
                    (rule lemma)
                    (fn (car x))
                    (st state)
                    (a (APPEND
                        (BOUNDRW-EV-ALIST
                         (MV-NTH 1
                                 (SIMPLE-ONE-WAY-UNIFY
                                  (MV-NTH 2
                                          (BOUNDRW-LINEAR-CONCL-DECOMP (CADDDR LEMMA)))
                                  X NIL))
                         A)
                        A)))
                   (:instance boundrw-linear-concl-decomp-correct
                    (concl (CADDDR LEMMA))
                    (a (append (BOUNDRW-EV-ALIST
                                (MV-NTH 1
                                        (SIMPLE-ONE-WAY-UNIFY
                                         (MV-NTH 3
                                                 (BOUNDRW-LINEAR-CONCL-DECOMP (CADDDR LEMMA)))
                                         X NIL))
                                a)
                               a)))
                   (:instance boundrw-linear-concl-decomp-correct
                    (concl (CADDDR LEMMA))
                    (a (append (BOUNDRW-EV-ALIST
                                (MV-NTH 1
                                        (SIMPLE-ONE-WAY-UNIFY
                                         (MV-NTH 2
                                                 (BOUNDRW-LINEAR-CONCL-DECOMP (CADDDR LEMMA)))
                                         X NIL))
                                a)
                               a)))))))))

(define boundrw-try-linear-lemma (lemma
                                  (x pseudo-termp)
                                  (direction booleanp)
                                  (best maybe-rationalp)
                                  (ens enabled-structure-p)
                                  mfc state)
  :returns (new-bound maybe-rationalp :rule-classes :type-prescription)
  (b* ((new-bound (boundrw-try-linear-lemma-aux lemma x direction best ens mfc state)))
    (or new-bound (maybe-rational-fix best)))
  ///
  (local (in-theory (enable maybe-rational-fix)))
  
  (defret <fn>-correct
    (implies (and (boundrw-ev-meta-extract-global-facts)
                  (boundrw-ev-meta-extract-contextual-facts a)
                  new-bound
                  (pseudo-termp x)
                  (member-equal lemma
                                (getpropc (car x) 'linear-lemmas nil (w state))))
             (and (implies (and direction
                                (or (not best)
                                    (<= (boundrw-ev x a) (rfix best))))
                           (<= (boundrw-ev x a) new-bound))
                  (implies (and (not direction)
                                
                                (or (not best)
                                    (<= (rfix best) (boundrw-ev x a))))
                           (<= new-bound (boundrw-ev x a)))))))



(define boundrw-try-linear-lemmas (lemmas
                                   (x pseudo-termp)
                                   (direction booleanp)
                                   (best maybe-rationalp)
                                   (ens enabled-structure-p)
                                   mfc state)
  :returns (new-best maybe-rationalp :rule-classes :type-prescription)
  (b* (((when (atom lemmas)) (maybe-rational-fix best))
       (new-best (boundrw-try-linear-lemma (car lemmas) x direction best ens mfc state)))
    (boundrw-try-linear-lemmas (cdr lemmas) x direction new-best ens mfc state))
  ///
  (local (in-theory (enable maybe-rational-fix)))
  (defret <fn>-correct
    (implies (and (boundrw-ev-meta-extract-global-facts)
                  (boundrw-ev-meta-extract-contextual-facts a)
                  new-best
                  (pseudo-termp x)
                  (subsetp-equal lemmas
                                 (getpropc (car x) 'linear-lemmas nil (w state))))
             (and (implies (and direction
                                (or (not best)
                                    (<= (boundrw-ev x a) (rfix best))))
                           (<= (boundrw-ev x a) new-best))
                  (implies (and (not direction)
                                (or (not best)
                                    (<= (rfix best) (boundrw-ev x a))))
                           (<= new-best (boundrw-ev x a)))))))


(define boundrw-apply-linear-bounds ((x pseudo-termp)
                                     (direction booleanp)
                                     mfc state)
  :prepwork ((local (defthm pseudo-termp-of-quote
                      (pseudo-termp (list 'quote x))
                      :hints(("Goal" :in-theory (enable pseudo-termp))))))
  :returns (mv changedp
               (new-x pseudo-termp :hyp (pseudo-termp x)))
  (b* (;; Start with the bound given by typeset, if any, and see if we can find better
       (ts-bound (ts-bound x direction mfc state))
       ((unless (and (consp x)
                     (symbolp (car x))
                     (not (eq (car x) 'quote))))
        (mv (and ts-bound t)
            (if ts-bound (kwote ts-bound) x)))
       (fn (car x))
       (lemmas (fgetprop fn 'linear-lemmas nil (w state)))
       ((unless (and (weak-metafunction-context-p mfc)
                     (weak-rewrite-constant-p (metafunction-context->rcnst mfc))))
        (raise "Error: bad MFC~%")
        (mv nil x))
       (ens (rewrite-constant->current-enabled-structure (metafunction-context->rcnst mfc)))
       ((unless (enabled-structure-p ens))
        (raise "Error: bad ENS~%")
        (mv nil x))
       (best-linear-bound
        (boundrw-try-linear-lemmas lemmas x direction ts-bound ens mfc state))
       ((unless best-linear-bound)
        ;; couldn't find any bounds
        (mv nil x))
       (new-x (kwote best-linear-bound))
       ;; ((unless (boundrw-check-bound x new-x direction mfc state))
       ;;  ;; (raise "Couldn't verify linear bound ~x0 for ~x1~%" new-x x)
       ;;  (mv nil x))
       )
    (mv t new-x))
  ///
  (defret boundrw-apply-linear-bounds-correct
    (implies (and (boundrw-ev-meta-extract-contextual-facts a)
                  (boundrw-ev-meta-extract-global-facts)
                  (pseudo-termp x))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev new-x a)))
                  (implies (not direction)
                           (<= (boundrw-ev new-x a) (boundrw-ev x a)))))
    :hints (("goal" :expand (<call>)
             :in-theory (enable boundrw-check-bound-correct-rw)))))



(define boundrw-find-bound ((x pseudo-termp)
                            (direction booleanp)
                            (bound-list boundrw-substlist-p)
                            mfc state)
  :returns (mv changedp
               explicitp
               (new-x pseudo-termp :hyp (and (pseudo-termp x)
                                             (boundrw-substlist-p bound-list))))
  (b* (((mv changedp new-x)
        (boundrw-apply-bound x direction bound-list mfc state))
       ((when changedp) (mv t t new-x))
       ((mv changedp new-x)
        (boundrw-apply-linear-bounds x direction mfc state)))
    (mv changedp nil new-x))
  ///
  (defret boundrw-find-bound-correct
    (implies (and (boundrw-ev-meta-extract-contextual-facts a)
                  (boundrw-ev-meta-extract-global-facts)
                  (pseudo-termp x)
                  (boundrw-substlist-p bound-list))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev new-x a)))
                  (implies (not direction)
                           (<= (boundrw-ev new-x a) (boundrw-ev x a))))))

  (defund boundrw-find-bound-changedp (x direction bound-list mfc state)
    (Declare (Xargs :stobjs state
                    :verify-guards nil))
    (non-exec (mv-nth 0 (boundrw-find-bound x direction bound-list mfc state))))

  (defthmd boundrw-find-bound-correct-rw
    (b* (((mv changedp & new-x) (boundrw-find-bound x direction bound-list mf st)))
      (implies (and (rewriting-negative-literal `(mv-nth '0 (boundrw-find-bound ,x ,direction ,bound-list ,mf ,st)))
                    (bind-free '((a . a)) (a))
                    (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st)
                    (boundrw-ev-meta-extract-global-facts :state st)
                    (pseudo-termp x)
                    (boundrw-substlist-p bound-list))
               (iff changedp
                    (and (boundrw-find-bound-changedp x direction bound-list mf st)
                         (if direction
                             (<= (boundrw-ev x a) (boundrw-ev new-x a))
                           (<= (boundrw-ev new-x a) (boundrw-ev x a)))))))
    :hints(("Goal" :in-theory (e/d (boundrw-find-bound-changedp
                                    boundrw-find-bound-correct)
                                   (boundrw-find-bound))))))



(define boundrw-apply ((fn symbolp)
                       (args pseudo-term-listp))
  :returns (call pseudo-termp :hyp (and (symbolp fn)
                                        (not (eq fn 'quote))
                                        (pseudo-term-listp args))
                 :hints (("goal" :expand ((:free (x y) (pseudo-termp (cons x y)))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((pseudo-term-listp args)
                                (pseudo-term-listp (cdr args))
                                (pseudo-termp (car args))
                                (pseudo-termp (cadr args))))))
  (if (quote-listp args)
      (case fn
        (unary--  (kwote (- (fix (unquote (car args))))))
        (unary-/  (kwote (let ((arg (fix (unquote (car args))))) (if (eql arg 0) 0 (/ arg)))))
        (binary-+ (kwote (+ (fix (unquote (car args)))
                            (fix (unquote (cadr args))))))
        (binary-* (kwote (* (fix (unquote (car args)))
                            (fix (unquote (cadr args))))))
        (otherwise (cons fn args)))
    (cons fn args))
  ///
  (defthm bound-rw-apply-correct
    (equal (boundrw-ev (boundrw-apply fn args) a)
           (boundrw-ev (cons fn args) a))))


(define boundrw-rewrite-measure ((x pseudo-termp))
  :measure (acl2-count x)
  :prepwork ((local (defthmd cdr-when-equal-cons
                      (implies (equal x (cons a b))
                               (equal (cdr x) b))))

             (local (defthmd car-when-equal-cons
                      (implies (equal x (cons a b))
                               (equal (car x) a))))
             (local (in-theory (disable default-car default-cdr))))
  :hints (("goal" :do-not-induct t))
  (cond ((atom x) 0)
        ((quotep x) 0)
        (t (treematch
            x
            ((binary-+ (:? a) (:? b))
             (+ 1 (boundrw-rewrite-measure a)
                (boundrw-rewrite-measure b)))
            ((unary-- (:? a))
             (+ 1 (boundrw-rewrite-measure a)))
            ((unary-/ (:? a))
             (+ 1 (boundrw-rewrite-measure a)))
            ((binary-* (:? a) (:? a))
             (+ 1 (boundrw-rewrite-measure a)))
            ((binary-* (:? a) (binary-* (:? a) (:? b)))
             ;; We want this to be greater than the measure of Q = `(binary-* (binary-* a a) b)
             ;; This may be an instance of the above pattern if b = (binary-* a a) in which case
             ;; this measure is (+ 2 (boundrw-rewrite-measure a)).
             ;; Otherwise if it is not an occurrence of this pattern, it is an occurrence of the next pattern,
             ;; in which case its measure is (+ 2 (boundrw-rewrite-measure a) (boundrw-rewrite-measure b)).
             ;; If it is an occurrence of this pattern, then we have b = (binary-* (binary-* a a) c).
             (+ 3 (boundrw-rewrite-measure a) (* 2 (boundrw-rewrite-measure b))))

            ((binary-* (:? a) (:? b))
             (+ 1 (boundrw-rewrite-measure a) (boundrw-rewrite-measure b)))

            (& 0))))
  ///
  (local (in-theory (disable (:d boundrw-rewrite-measure))))

  (defthm boundrw-rewrite-measure-decr-on-+-subterm
    (b* (((mv match ?alist) (match-tree '(binary-+ (:? a) (:? b)) x nil)))
      (implies match
               (and (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))
                    (< (boundrw-rewrite-measure (caddr x)) (boundrw-rewrite-measure x)))))
    :hints (("goal" :expand ((boundrw-rewrite-measure x))))
    :rule-classes :linear)

  (defthm boundrw-rewrite-measure-decr-on-minus-subterm
    (b* (((mv match ?alist) (match-tree '(unary-- (:? a)) x nil)))
      (implies match
               (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))))
    :hints (("goal" :expand ((boundrw-rewrite-measure x))))
    :rule-classes :linear)

  (defthm boundrw-rewrite-measure-decr-on-/-subterm
    (b* (((mv match ?alist) (match-tree '(unary-/ (:? a)) x nil)))
      (implies match
               (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))))
    :hints (("goal" :expand ((boundrw-rewrite-measure x))))
    :rule-classes :linear)

  (defthm boundrw-rewrite-measure-decr-on-square-subterm
    (b* (((mv match ?alist) (match-tree '(binary-* (:? a) (:? a)) x nil)))
      (implies match
               (and (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))
                    (< (boundrw-rewrite-measure (caddr x)) (boundrw-rewrite-measure x)))))
    :hints (("goal" :expand ((boundrw-rewrite-measure x))))
    :otf-flg t
    :rule-classes :linear)

  (local (defthmd equal-of-cons
           (equal (equal x (cons a b))
                  (and (consp x)
                       (equal (car x) a)
                       (equal (cdr x) b)))))


  ;; (local (defthm cadr-when-equal-list
  ;;          (implies (equal x (list* a b c))
  ;;                   (equal (cadr x) b))))

  ;; (local (defthm caddr-when-equal-list
  ;;          (implies (equal x (list* a b c d))
  ;;                   (equal (caddr x) c))))

  (local (defthm contradictory-shapes
           (and (implies (equal `(binary-* ,a ,a) x)
                         (not (equal `(binary-* ,c (binary-* ,c ,d)) x)))
                (implies (equal `(binary-* ,c (binary-* ,c ,d)) x)
                         (not (equal `(binary-* ,a ,a) x))))))




  (local (defthm binary-*-matches
           (implies (and (consp x)
                         (consp (cdr x))
                         (consp (cddr x))
                         (not (cdddr x))
                         (eq (car x) 'binary-*))
                    (mv-nth 0 (match-tree '(binary-* (:? a) (:? b)) x nil)))
           :hints(("Goal" :in-theory (enable match-tree-open
                                             match-tree-opener-theory)))))




  (local (defthm binary-*-a-a-matches
           (mv-nth 0 (match-tree '(binary-* (:? a) (:? a))
                                 (list 'binary-* a a) nil))
           :hints(("Goal" :in-theory (enable match-tree-open
                                             match-tree-opener-theory
                                             match-tree-alist-opener-theory)))))


  (local (defthm boundrw-rewrite-measure-of-special
           (implies (equal x `(binary-* ,a ,a))
                    (equal (boundrw-rewrite-measure x)
                           (+ 1 (boundrw-rewrite-measure a))))
           :hints (("goal" :expand ((:free (a b) (boundrw-rewrite-measure (cons a b))))
                    :in-theory (e/d (match-tree-obj-equals-subst-when-successful)
                                    (match-tree-opener-theory)))
                   ;; (and stable-under-simplificationp
                   ;;      '(:in-theory (enable match-tree-opener-theory)))
                   )))
  (local (in-theory (disable not)))

  (local (defthm boundrw-rewrite-measure-decr-on-caddr
           (implies (and (consp x)
                         (consp (cdr x))
                         (consp (cddr x))
                         (not (cdddr x))
                         (eq (car x) 'binary-*))
                    (< (boundrw-rewrite-measure (caddr x)) (boundrw-rewrite-measure x)))
           :hints (("goal" :induct (boundrw-rewrite-measure x)
                    :in-theory (e/d (match-tree-obj-equals-subst-when-successful)
                                    (match-tree-equals-match-tree-matchedp-when-successful
                                     match-tree-opener-theory))
                    :expand ((boundrw-rewrite-measure x)
                             (:free (a b) (BOUNDRW-REWRITE-MEASURE (LIST 'BINARY-* a b)))
                             :lambdas)
                    :do-not-induct t)
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (car-when-equal-cons
                                           cdr-when-equal-cons
                                           match-tree-obj-equals-subst-when-successful)
                                          (match-tree-equals-match-tree-matchedp-when-successful
                                           match-tree-opener-theory))))
                   )
                   ;; (and stable-under-simplificationp
                   ;;      '(:in-theory (enable match-tree-opener-theory)))
                   ))


  (defthm boundrw-rewrite-measure-square-assoc-case-1
    (b* (((mv match ?alist) (match-tree '(binary-* (:? a) (binary-* (:? a) (:? b))) x nil)))
      (implies match
               (b* ((a (cadr (caddr x)))
                    (b (caddr (caddr x))))
                 (< (boundrw-rewrite-measure `(binary-* (binary-* ,a ,a) ,b))
                    (boundrw-rewrite-measure x)))))
    :hints(("Goal" ;; :induct (boundrw-rewrite-measure-square-assoc-ind x)
            :expand ((boundrw-rewrite-measure x)
                     (:free (a b) (boundrw-rewrite-measure `(binary-* ,a ,b))))
            ;; :in-theory (enable match-tree-opener-theory)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:use ((:instance boundrw-rewrite-measure-decr-on-caddr
                         (x (caddr (caddr x)))))
                  :in-theory (e/d (equal-of-cons-hyp-open)
                                  (boundrw-rewrite-measure-decr-on-caddr))))
           )
    :otf-flg t
    :rule-classes :linear)

  (defthm boundrw-rewrite-measure-square-assoc-case-2
    (b* (((mv match ?alist) (match-tree '(binary-* (:? a) (binary-* (:? a) (:? b))) x nil)))
      (implies match
               (b* ((a (cadr x))
                    (b (caddr (caddr x))))
                 (< (boundrw-rewrite-measure `(binary-* (binary-* ,a ,a) ,b))
                    (boundrw-rewrite-measure x)))))
    :hints(("Goal" :use boundrw-rewrite-measure-square-assoc-case-1
            :in-theory (disable boundrw-rewrite-measure-square-assoc-case-1))))



  (defthm boundrw-rewrite-measure-decr-on-*-subterm
    (b* (((mv match ?alist) (match-tree '(binary-* (:? a) (:? b)) x nil)))
      (implies match
               (and (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))
                    (< (boundrw-rewrite-measure (caddr x)) (boundrw-rewrite-measure x)))))
    :hints (("goal" :expand ((boundrw-rewrite-measure x)
                             (:free (a b) (boundrw-rewrite-measure `(binary-* ,a ,b))))
             :in-theory (enable car-when-equal-cons
                                cdr-when-equal-cons)
             :do-not-induct t))
    :otf-flg t
    :rule-classes :linear)

  ;; (defthm boundrw-rewrite-measure-decr-on-*-subterm-2
  ;;   (b* (((mv match ?alist) (match-tree '(binary-* (:? a) (:? b)) x nil)))
  ;;     (implies match
  ;;              (and (< (boundrw-rewrite-measure (cadr x)) (boundrw-rewrite-measure x))
  ;;                   (< (boundrw-rewrite-measure (caddr x)) (boundrw-rewrite-measure x)))))
  ;;   :hints (("goal" :expand ((boundrw-rewrite-measure x)
  ;;                            (:free (a b) (boundrw-rewrite-measure `(binary-* ,a ,b))))
  ;;            :in-theory (enable car-when-equal-cons
  ;;                               cdr-when-equal-cons)
  ;;            :do-not-induct t))
  ;;   :otf-flg t
  ;;   :rule-classes :linear)
  )



;; (local (in-theory (e/d (match-tree-obj-equals-subst-when-successful
;;                         ;; match-tree-equals-match-tree-matchedp-when-successful
;;                         match-tree-alist-opener-theory

;;                         )
;;                        (match-tree-opener-theory)
;;                        ;; (match-tree-obj-equals-subst-when-successful)
;;                        )))

(encapsulate
  (((boundrw-rewrite-trace * * * state) => *
    :formals (x upper lower state)
    :guard (and (pseudo-termp x)
                (maybe-rationalp upper)
                (maybe-rationalp lower))))
  (local (defun boundrw-rewrite-trace (x upper lower state)
           (declare (xargs :stobjs state)
                    (ignorable x upper lower state))
           nil)))

(define boundrw-rewrite-trace-default ((x pseudo-termp)
                                       (upper maybe-rationalp)
                                       (lower maybe-rationalp)
                                       state)
  (declare (ignore x upper lower state))
  nil
  ///
  (defattach boundrw-rewrite-trace boundrw-rewrite-trace-default))

(define boundrw-choose-best-bound ((bound1 pseudo-termp)
                                   (bound2 pseudo-termp)
                                   (original pseudo-termp)
                                   (direction booleanp))
  :returns (new-bound pseudo-termp :hyp (and (pseudo-termp bound1)
                                             (pseudo-termp bound2)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable pseudo-termp))))
  ;; Bound1 is from boundrw-find-bound on some term x, resulting from finding a
  ;; linear bound -- note it is NOT the result of finding a bound from the
  ;; bound-alist, which would be selected automatically.  Bound2 is either the
  ;; original term or the result of bounding subterms.  We choose bound1 if
  ;; bound2 is unchanged from original, the best bound if both are constants,
  ;; otherwise bound1 if it is constant, but bound2 otherwise -- in particular,
  ;; if both are non-constant terms, we figure that processing subterms is
  ;; likely to get a more specific bound.
  (cond ((equal bound2 original) bound1)
        ((and (quotep bound1) (rationalp (unquote bound1)))
         (if (and (quotep bound2) (rationalp (unquote bound2)))
             (if direction
                 ;; best upper bound is the least
                 (if (< (unquote bound1) (unquote bound2))
                     bound1
                   bound2)
               ;; best lower bound is the greatest
               (if (< (unquote bound1) (unquote bound2))
                   bound2
                 bound1))
           bound1))
        (t ;; Bound1 is not a quoted rational and bound2 is different from original, so choose bound2.
         bound2))
  ///
  (defthm boundrw-choose-best-bound-correct
    ;; Note: direction is actually immaterial for this theorem, but maybe
    ;; considering it as a hyp will prevent useless attempts to apply this
    ;; rule.
    (b* ((new-bound (boundrw-choose-best-bound bound1 bound2 original direction)))
      (and (implies (and direction
                         (<= (boundrw-ev original a) (boundrw-ev bound1 a))
                         (<= (boundrw-ev original a) (boundrw-ev bound2 a)))
                    (<= (boundrw-ev original a) (boundrw-ev new-bound a)))
           (implies (and (not direction)
                         (<= (boundrw-ev bound1 a) (boundrw-ev original a))
                         (<= (boundrw-ev bound2 a) (boundrw-ev original a)))
                    (<= (boundrw-ev new-bound a) (boundrw-ev original a)))))
    :rule-classes :linear))




(define boundrwc-choose-best-bound ((x1 maybe-rationalp)
                                    (x2 maybe-rationalp)
                                    (direction booleanp))
  :returns (best maybe-rationalp :rule-classes :type-prescription)
  (b* ((x1 (maybe-rational-fix x1))
       (x2 (maybe-rational-fix x2)))
    (if x1
        (if x2
            (if direction
                (min x1 x2)
              (max x1 x2))
          x1)
      x2))
  ///
  (defret boundrwc-choose-best-bound-correct
    (implies (and (iff direction direction1)
                  (maybe-boundp direction x x1)
                  (maybe-boundp direction x x2))
             (maybe-boundp direction1 x best))
    :hints(("Goal" :in-theory (enable maybe-boundp)))))

(define subst-tree-from-tree (pat x)
  :verify-guards nil
  (b* (((when (atom pat)) pat)
       ((unless (match-tree-binder-p pat))
        (cons (subst-tree-from-tree (car pat) (car x))
              (subst-tree-from-tree (cdr pat) (cdr x)))))
    x)
  ///
  (local (defthm subst-tree-when-all-binders-bound2
           (implies (and (keys-subset (match-tree-binders pat) alist0)
                         (match-tree-matchedp pat1 x alist0))
                    (equal (subst-tree pat (match-tree-alist pat1 x alist0))
                           (subst-tree pat alist0)))
           :hints (("goal" :use subst-tree-when-all-binders-bound
                    :in-theory (e/d ()
                                    (subst-tree-when-all-binders-bound))))))

  (local (defthm match-tree-alist-all-binders-bound
           (implies (and (match-tree-matchedp pat x alist)
                         (subsetp keys (match-tree-binders pat)))
                    (keys-subset keys
                                 (match-tree-alist pat x alist)))
           :hints(("Goal" :use match-tree-all-binders-bound                                 
                   :in-theory (e/d ()
                                   (subst-tree-when-all-binders-bound))))))
  
  (defthm subst-tree-of-match-tree-alist-is-subst-tree-from-tree
    (implies (match-tree-matchedp pat x alist)
             (equal (subst-tree pat (match-tree-alist pat x alist))
                    (subst-tree-from-tree pat x)))
    :hints(("Goal" :in-theory (enable match-tree-alist
                                      match-tree-matchedp
                                      subst-tree)
            :induct (match-tree-alist pat x alist))
           (and stable-under-simplificationp
                '(:expand ((:free (k v rest) (assoc-equal k (cons (Cons k v) rest))))))))

  (defthm subst-tree-from-tree-open
    (implies (syntaxp (quotep pat))
             (equal (subst-tree-from-tree pat x)
                    (b* (((when (atom pat)) pat)
                         ((unless (match-tree-binder-p pat))
                          (cons (subst-tree-from-tree (car pat) (car x))
                                (subst-tree-from-tree (cdr pat) (cdr x)))))
                      x)))))


;;;;;;;;;;;;;;;;;;;;; Bounds for multiply ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Note: We have two alternative algorithms for bounding multiply.  I believe
;; these are both equivalent.  I'm not sure which to keep.

;; 1 (boundrwc-multiply-bounds): If we have either a nonnegative lower bound or
;;    nonpositive upper bound, then this determines which bound of the other
;;    argument matters for a given direction.  Then, that bound of the other
;;    argument determines which bound of the original argument to use.  These
;;    cases are worked out in boundrwc-multiply-bound-when-nonneg and
;;    boundrwc-multiply-bound-when-nonpos. Otherwise we need all four bounds to
;;    determine anything; if we have them, then the max of lower*lower and
;;    upper*upper is the upper bound, and the min of lower*upper and
;;    upper*lower is the lower bound.

;; 2 (boundrwc-multiply-bounds-extrat) If we have upper and lower bounds for
;;   both, then the max and min of all four pairwise multiplications (u*u, u*l,
;;   l*u, l*l) gives the bounds.  If we don't, a similar theorem holds for
;;   extended rationals, i.e. where if we don't have an upper bound, then we
;;   consider the upper bound +infinity, and if we don't have a lower bound, we
;;   consider the lower bound -infinity.  (This is the same as the use of
;;   extended rationals in tau/bounders/elementary-bounders.)  So we just
;;   conver our input bounds into these extended rationals, do the four
;;   pairwise multiplications, take the min and max, and convert these back to
;;   bounds.

(define boundrwc-multiply-bound-when-nonneg ((a-upper maybe-rationalp)
                                             (a-lower rationalp)
                                             (b-upper maybe-rationalp)
                                             (b-lower maybe-rationalp))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* ((a-upper (maybe-rational-fix a-upper))
       (a-lower (mbe :logic (rfix a-lower) :exec a-lower))
       (b-upper (maybe-rational-fix b-upper))
       (b-lower (maybe-rational-fix b-lower))
       (upper (and b-upper
                   (cond ((< 0 b-upper) (and a-upper (* a-upper b-upper)))
                         ((eql b-upper 0) 0)
                         (t (* a-lower b-upper)))))
       (lower (and b-lower
                   (cond ((< 0 b-lower) (* a-lower b-lower))
                         ((eql b-lower 0) 0)
                         (t (and a-upper (* a-upper b-lower)))))))
    (mv upper lower))
  ///
  

  (local (defthm mult-monotonic-pos-pos-lower
           (implies (and (<= 0 b)
                         (<= c a)
                         (<= 0 c)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))


  (local (defthm mult-monotonic-neg-pos-upper
           (implies (and (<= b 0)
                         (<= c a)
                         (<= 0 c)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (defret <fn>-correct
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper)
                  a-lower
                  (<= 0 (rfix a-lower)))
             (and (maybe-boundp nil (* a b) lower)
                  (maybe-boundp t (* a b) upper)))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  

  (defret <fn>-correct2
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper)
                  a-lower
                  (<= 0 (rfix a-lower)))
             (and (maybe-boundp nil (* b a) lower)
                  (maybe-boundp t (* b a) upper)))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (fty::deffixequiv boundrwc-multiply-bound-when-nonneg))


(define boundrwc-multiply-bound-when-nonpos ((a-upper rationalp)
                                             (a-lower maybe-rationalp)
                                             (b-upper maybe-rationalp)
                                             (b-lower maybe-rationalp))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* ((a-upper (mbe :logic (rfix a-upper) :exec a-upper))
       (a-lower (maybe-rational-fix a-lower))
       (b-upper (maybe-rational-fix b-upper))
       (b-lower (maybe-rational-fix b-lower))
       (upper (and b-lower
                   (cond ((< 0 b-lower) (* a-upper b-lower))
                         ((eql b-lower 0) 0)
                         (t (and a-lower (* a-lower b-lower))))))
       (lower (and b-upper
                   (cond ((< 0 b-upper) (and a-lower (* a-lower b-upper)))
                         ((eql b-upper 0) 0)
                         (t (* a-upper b-upper))))))
    (mv upper lower))
  ///
  

  (local (defthm mult-monotonic-pos-neg-upper
           (implies (and (<= 0 b)
                         (<= a c)
                         (<= c 0)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))
  

  (local (defthm mult-monotonic-neg-neg-lower
           (implies (and (<= b 0)
                         (<= a c)
                         (<= c 0)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))
  
  (defret <fn>-correct
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper)
                  a-upper
                  (<= (rfix a-upper) 0))
             (and (maybe-boundp nil (* a b) lower)
                  (maybe-boundp t (* a b) upper)))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (defret <fn>-correct2
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper)
                  a-upper
                  (<= (rfix a-upper) 0))
             (and (maybe-boundp nil (* b a) lower)
                  (maybe-boundp t (* b a) upper)))
    :hints(("Goal" :in-theory (enable maybe-rational-fix))))

  (fty::deffixequiv boundrwc-multiply-bound-when-nonpos))


(define boundrwc-multiply-bound ((a-upper maybe-rationalp)
                                 (a-lower maybe-rationalp)
                                 (b-upper maybe-rationalp)
                                 (b-lower maybe-rationalp))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* ((a-upper (maybe-rational-fix a-upper))
       (a-lower (maybe-rational-fix a-lower))
       (b-upper (maybe-rational-fix b-upper))
       (b-lower (maybe-rational-fix b-lower))
       ((when (and a-lower (<= 0 a-lower)))
        (boundrwc-multiply-bound-when-nonneg a-upper a-lower b-upper b-lower))
       ((when (and a-upper (<= a-upper 0)))
        (boundrwc-multiply-bound-when-nonpos a-upper a-lower b-upper b-lower))
       ((when (and b-lower (<= 0 b-lower)))
        (boundrwc-multiply-bound-when-nonneg b-upper b-lower a-upper a-lower))
       ((when (and b-upper (<= b-upper 0)))
        (boundrwc-multiply-bound-when-nonpos b-upper b-lower a-upper a-lower))
       ((unless (and a-upper a-lower b-upper b-lower))
        (mv nil nil)))
    ;; If we get here, the uppers are positive and the lowers are negative.
    (mv (max (* a-upper b-upper)
             (* a-lower b-lower))
        (min (* a-upper b-lower)
             (* a-lower b-upper))))
  ///
  (local (in-theory (disable rfix)))
  (local (defthm maybe-rational-fix-when-nonnil
           (implies x
                    (equal (maybe-rational-fix x) (rfix x)))
           :hints(("Goal" :in-theory (enable maybe-rational-fix)))))

    (local (defthm mult-monotonic-cross
           (implies (and (<= b bmax)
                         (<= bmin b)
                         (<= a amax)
                         (<= amin a)
                         (<= amin 0)
                         (<= 0 amax)
                         (<= bmin 0)
                         (<= 0 bmax)
                         (rationalp a)
                         (rationalp b)
                         (rationalp amin)
                         (rationalp amax)
                         (rationalp bmin)
                         (rationalp bmax))
                    (and (implies (<= (* amax bmax) (* amin bmin))
                                  (<= (* a b) (* amin bmin)))
                         (implies (<= (* amin bmin) (* amax bmax))
                                  (<= (* a b) (* amax bmax)))
                         (implies (<= (* amax bmin) (* amin bmax))
                                  (<= (* amax bmin) (* a b)))
                         (implies (<= (* amin bmax) (* amax bmin))
                                  (<= (* amin bmax) (* a b)))))
           :hints (("goal" :cases ((< 0 a)
                                   (< a 0)))
                   '(:cases ((< 0 b)
                             (< b 0)))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))
  
  (defret <fn>-correct
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper))
             (and (maybe-boundp nil (* a b) lower)
                  (maybe-boundp t (* a b) upper)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable rfix))))))




(define extratp (x)
  (or (rationalp x)
      (eq x t)
      (eq x nil))
  ///
  (defthm extratp-compound-recognizer
    (iff (extratp x)
       (or (rationalp x)
           (eq x t)
           (eq x nil)))
    :rule-classes :compound-recognizer))

(define extrat-fix ((x extratp))
  :returns (new-x extratp :rule-classes :type-prescription)
  (mbe :logic (if (extratp x) x 0)
       :exec x)
  ///
  (defthm extrat-fix-when-extratp
    (implies (extratp x)
             (equal (extrat-fix x) x)))

  (fty::deffixtype extrat :pred extratp :fix extrat-fix :equiv extrat-equiv :define t))

(define extrat-<= ((x extratp) (y extratp))
  :hooks (:fix)
  (b* ((x (extrat-fix x))
       (y (extrat-fix y))
       ((when (eq y t)) t)
       ((when (eq x nil)) t)
       ((when (eq y nil)) nil)
       ((when (eq x t)) nil))
    (<= x y))
  ///
  (defthm extrat-<=-refl
    (extrat-<= x x))

  (defthm extrat-<=-asymm
    (implies (not (equal (extrat-fix x)
                         (extrat-fix y)))
             (iff (extrat-<= y x)
                  (not (extrat-<= x y)))))

  (defthm extrat-<=-trans
    (implies (and (extrat-<= x y)
                  (extrat-<= y z))
             (extrat-<= x z)))

  (defthm extrat-<=-trans-non/strict
    (implies (and (extrat-<= x y)
                  (not (extrat-<= z y)))
             (and (extrat-<= x z)
                  (not (extrat-<= z x)))))

  (defthm extrat-<=-trans-strict/non
    (implies (and (not (extrat-<= y x))
                  (extrat-<= y z))
             (and (extrat-<= x z)
                  (not (extrat-<= z x)))))

  (defthm extrat-<=-trans-strict/strict
    (implies (and (not (extrat-<= y x))
                  (not (extrat-<= z y)))
             (and (extrat-<= x z)
                  (not (extrat-<= z x))))))


(define extrat-max ((x extratp) (y extratp))
  :returns (max extratp :rule-classes :type-prescription)
  :hooks (:fix)
  (if (extrat-<= x y) (extrat-fix y) (extrat-fix x))
  ///
  (defret extrat-max-greater-when-either-greater
    (implies (or (extrat-<= q x)
                 (extrat-<= q y))
             (extrat-<= q max)))

  (defret extrat-max-less-when-both-less
    (implies (and (extrat-<= x q)
                  (extrat-<= y q))
             (extrat-<= max q))))

(define extrat-min ((x extratp) (y extratp))
  :returns (max extratp :rule-classes :type-prescription)
  :hooks (:fix)
  (if (extrat-<= x y) (extrat-fix x) (extrat-fix y))
  ///
  (defret extrat-max-greater-when-both-greater
    (implies (and (extrat-<= q x)
                  (extrat-<= q y))
             (extrat-<= q max)))

  (defret extrat-max-less-when-either-less
    (implies (or (extrat-<= x q)
                 (extrat-<= y q))
             (extrat-<= max q))))

(define extrat-* ((x extratp) (y extratp))
  (b* ((x (extrat-fix x))
       (y (extrat-fix y))
       ((when (eql y 0)) 0)
       ((when (eql x 0)) 0)
       ((when (and (rationalp x)
                   (rationalp y)))
        (* x y))
       (x-pos (cond ((eq x t) t)
                    ((eq x nil) nil)
                    (t (< 0 x))))
       (y-pos (cond ((eq y t) t)
                    ((eq y nil) nil)
                    (t (< 0 y)))))
    (iff x-pos y-pos)))


(defthm upper-bound-for-mul-extrat
  (not (and (rationalp x)
            (rationalp y)
            (extratp xmin)
            (extratp xmax)
            (extratp ymin)
            (extratp ymax)
            (extrat-<= xmin x)
            (extrat-<= x xmax)
            (extrat-<= ymin y)
            (extrat-<= y ymax)
            (not (extrat-<= (* x y) (extrat-* xmin ymin)))
            (not (extrat-<= (* x y) (extrat-* xmin ymax)))
            (not (extrat-<= (* x y) (extrat-* xmax ymin)))
            (not (extrat-<= (* x y) (extrat-* xmax ymax)))))
  :hints (("goal" :cases ((<= 0 x))
           :in-theory (enable extrat-<= extrat-*  ;; upper-bound-for-mul
                              ))
          '(:cases ((<= 0 y)))
          '(:nonlinearp t)
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ('(:cases ((<= 0 xmax)))
                  '(:cases ((<= 0 ymin)))
                  '(:cases ((<= 0 ymax))))
                 :cases ((<= 0 xmin)))))
  :rule-classes nil
  :otf-flg t)

(defthm extrat-max-is-upper-bound-for-mul
  (implies (and (rationalp x)
                (rationalp y)
                (extratp xmin)
                (extratp xmax)
                (extratp ymin)
                (extratp ymax)
                (extrat-<= xmin x)
                (extrat-<= x xmax)
                (extrat-<= ymin y)
                (extrat-<= y ymax))
           (extrat-<= (* x y)
                      (extrat-max (extrat-max (extrat-* xmin ymin)
                                              (extrat-* xmin ymax))
                                  (extrat-max (extrat-* xmax ymin)
                                              (extrat-* xmax ymax)))))
  :hints (("goal" :use upper-bound-for-mul-extrat)))


(defthm lower-bound-for-mul-extrat
  (not (and (rationalp x)
            (rationalp y)
            (extratp xmin)
            (extratp xmax)
            (extratp ymin)
            (extratp ymax)
            (extrat-<= xmin x)
            (extrat-<= x xmax)
            (extrat-<= ymin y)
            (extrat-<= y ymax)
            (not (extrat-<= (extrat-* xmin ymin) (* x y)))
            (not (extrat-<= (extrat-* xmin ymax) (* x y)))
            (not (extrat-<= (extrat-* xmax ymin) (* x y)))
            (not (extrat-<= (extrat-* xmax ymax) (* x y)))))
  :hints (("goal" :cases ((<= 0 x))
           :in-theory (enable extrat-<= extrat-*))
          '(:cases ((<= 0 y)))
          '(:nonlinearp t)
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ('(:cases ((<= 0 xmax)))
                  '(:cases ((<= 0 ymin)))
                  '(:cases ((<= 0 ymax))))
                 :cases ((<= 0 xmin)))))
  :rule-classes nil
  :otf-flg t)

(defthm extrat-min-is-lower-bound-for-mul
  (implies (and (rationalp x)
                (rationalp y)
                (extratp xmin)
                (extratp xmax)
                (extratp ymin)
                (extratp ymax)
                (extrat-<= xmin x)
                (extrat-<= x xmax)
                (extrat-<= ymin y)
                (extrat-<= y ymax))
           (extrat-<= (extrat-min (extrat-min (extrat-* xmin ymin)
                                              (extrat-* xmin ymax))
                                  (extrat-min (extrat-* xmax ymin)
                                              (extrat-* xmax ymax)))
                      (* x y)))
  :hints (("goal" :use lower-bound-for-mul-extrat)))

(define upper-bound-to-extrat ((bound maybe-rationalp))
  :returns (extrat-bound extratp :rule-classes :type-prescription)
  (or (maybe-rational-fix bound) t)
  ///
  (defret maybe-boundp-implies-extrat-<=-of-<fn>
    (implies (maybe-boundp t x bound)
             (extrat-<= x extrat-bound))
    :hints(("Goal" :in-theory (enable maybe-boundp extrat-<=)))))

(define lower-bound-to-extrat ((bound maybe-rationalp))
  :returns (extrat-bound extratp :rule-classes :type-prescription)
  (maybe-rational-fix bound)
  ///
  (defret maybe-boundp-implies-extrat-<=-of-<fn>
    (implies (maybe-boundp nil x bound)
             (extrat-<= extrat-bound x))
    :hints(("Goal" :in-theory (enable maybe-boundp extrat-<=)))))

(define extrat-to-bound ((extrat-bound extratp))
  :returns (bound maybe-rationalp :rule-classes :type-prescription)
  (and (rationalp extrat-bound) extrat-bound)
  ///
  (defthm maybe-boundp-of-extrat-to-bound-lower
    (implies (and (extrat-<= y x)
                  (rationalp x))
             (maybe-boundp nil x (extrat-to-bound y)))
    :hints(("Goal" :in-theory (enable extrat-<= maybe-boundp extrat-fix extratp maybe-rational-fix))))

  (defthm maybe-boundp-of-extrat-to-bound-upper
    (implies (and (extrat-<= x y)
                  (rationalp x))
             (maybe-boundp t x (extrat-to-bound y)))
    :hints(("Goal" :in-theory (enable extrat-<= maybe-boundp extrat-fix extratp maybe-rational-fix)))))


(define boundrwc-multiply-bounds-extrat  ((a-upper maybe-rationalp)
                                         (a-lower maybe-rationalp)
                                         (b-upper maybe-rationalp)
                                         (b-lower maybe-rationalp))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))

  (b* ((amin (lower-bound-to-extrat a-lower))
       (amax (upper-bound-to-extrat a-upper))
       (bmin (lower-bound-to-extrat b-lower))
       (bmax (upper-bound-to-extrat b-upper))
       (upper (extrat-max (extrat-max (extrat-* amin bmin)
                                      (extrat-* amin bmax))
                          (extrat-max (extrat-* amax bmin)
                                      (extrat-* amax bmax))))
       (lower (extrat-min (extrat-min (extrat-* amin bmin)
                                      (extrat-* amin bmax))
                          (extrat-min (extrat-* amax bmin)
                                      (extrat-* amax bmax)))))
    (mv (extrat-to-bound upper)
        (extrat-to-bound lower)))
  
  ///

  (local (defthm rfix-when-rationalp
           (implies (rationalp x)
                    (Equal (rfix x) x))))
  (local (in-theory (disable rfix
                             maybe-boundp-of-nonnil)))

  (local (defthm maybe-boundp-when-not-rationalp
           (implies (not (rationalp x))
                    (equal (maybe-boundp dir x y)
                           (not y)))
           :hints(("Goal" :in-theory (enable maybe-boundp
                                             maybe-rational-fix)))))

  (local (defthm extrat-to-bound-of-non-rational
           (implies (not (rationalp x))
                    (equal (extrat-to-bound x) nil))
           :hints(("Goal" :in-theory (enable extrat-to-bound)))))

  (local (defthm not-rationalp-of-extrat-min
           (implies (and (not (rationalp (extrat-fix x)))
                         (not (rationalp (extrat-fix y))))
                    (not (rationalp (extrat-min x y))))
           :hints(("Goal" :in-theory (enable extrat-min)))))

  (local (defthm not-rationalp-of-extrat-max
           (implies (and (not (rationalp (extrat-fix x)))
                         (not (rationalp (extrat-fix y))))
                    (not (rationalp (extrat-max x y))))
           :hints(("Goal" :in-theory (enable extrat-max)))))

  ;; (local (defthm not-rationalp-of-extrat-*-1
  ;;          (implies (and (not (Rationalp (extrat-fix x)))
  ;;                        (case-split (not (equal 0 (extrat-fix y)))))
  ;;                   (not (rationalp (extrat-* x y))))
  ;;          :hints(("Goal" :in-theory (enable extrat-* extrat-fix)))))

  ;; (local (defthm not-rationalp-of-extrat-*-2
  ;;          (implies (and (not (Rationalp (extrat-fix y)))
  ;;                        (case-split (not (equal 0 (extrat-fix x)))))
  ;;                   (not (rationalp (extrat-* x y))))
  ;;          :hints(("Goal" :in-theory (enable extrat-* extrat-fix)))))

  (local (defthm lower-bound-to-extrat-equal-0
           (equal (Equal (lower-bound-to-extrat x) 0)
                  (equal (maybe-rational-fix x) 0))
           :hints(("Goal" :in-theory (enable lower-bound-to-extrat)))))
  (local (defthm upper-bound-to-extrat-equal-0
           (equal (Equal (upper-bound-to-extrat x) 0)
                  (equal (maybe-rational-fix x) 0))
           :hints(("Goal" :in-theory (enable upper-bound-to-extrat)))))
  
  (defret <fn>-correct
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper)
                  (maybe-boundp nil b b-lower)
                  (maybe-boundp t b b-upper))
             (and (maybe-boundp nil (* a b) lower)
                  (maybe-boundp t (* a b) upper)))
    :hints (("Goal" :cases ((not (rationalp a))))
            '(:cases ((rationalp b)))
            ;; ugh -- deal with the (nil nil 0 0) case
            (and stable-under-simplificationp
                 '(:expand ((:free (x) (extrat-* nil x))
                            (:free (x) (extrat-* t x))
                            (:free (x) (extrat-* x nil))
                            (:free (x) (extrat-* x t)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable maybe-boundp))))
    :otf-flg t))


;; (local (include-book
;;         "projects/apply/top" :dir :system))

;; (defwarrant boundrwc-multiply-bound-extrat)
;; (defwarrant boundrwc-multiply-bound)

;; (let ((lower-uppers '((nil nil)
;;                       (nil -5)
;;                       (nil 0)
;;                       (nil 5)
;;                       (-5 nil)
;;                       (-5 -3)
;;                       (-5 0)
;;                       (-5 3)
;;                       (0 nil)
;;                       (0 0)
;;                       (0 5)
;;                       (3 nil)
;;                       (3 5))))
;;   (loop$ for xbounds in lower-uppers always
;;          (loop$ for ybounds in lower-uppers always
;;                 (b* ((x-lower (first xbounds))
;;                      (x-upper (second xbounds))
;;                      (y-lower (first xbounds))
;;                      (y-upper (second xbounds))
;;                      ((mv ext-upper ext-lower)
;;                       (boundrwc-multiply-bound-extrat x-upper x-lower y-upper y-lower))
;;                      ((mv orig-upper orig-lower)
;;                       (boundrwc-multiply-bound x-upper x-lower y-upper y-lower)))
;;                   (and (Equal ext-upper orig-upper)
;;                        (equal ext-lower orig-lower))))))
  





                                              

(define boundrwc-square-bound-aux ((a-upper maybe-rationalp)
                                   (a-lower maybe-rationalp))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* ((a-upper (maybe-rational-fix a-upper))
       (a-lower (maybe-rational-fix a-lower))
       (upper (and a-upper a-lower (max (* a-upper a-upper) (* a-lower a-lower))))
       (lower (cond ((and a-lower (<= 0 a-lower))
                     (* a-lower a-lower))
                    ((and a-upper (<= a-upper 0))
                     (* a-upper a-upper))
                    (t nil))))
    (mv upper lower))
  ///

  (local (in-theory (disable rfix)))


  (local (defthm square-monotonic-upper
           (implies (and (<= a amax)
                         (<= amin a)
                         (rationalp a)
                         (rationalp amin)
                         (rationalp amax))
                    (and (implies (<= (* amax amax) (* amin amin))
                                  (<= (* a a) (* amin amin)))
                         (implies (<= (* amin amin) (* amax amax))
                                  (<= (* a a) (* amax amax)))))
           :hints (("goal" :cases ((< 0 a)
                                   (< a 0)))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))
  
  (defret <fn>-correct
    (implies (and (maybe-boundp nil a a-lower)
                  (maybe-boundp t a a-upper))
             (and (maybe-boundp nil (* a a) lower)
                  (maybe-boundp t (* a a) upper)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable rfix maybe-rational-fix))))))

(define boundrwc-square-bound ((a-upper maybe-rationalp)
                               (a-lower maybe-rationalp)
                               (a pseudo-termp)
                               &key (mfc 'mfc) (state 'state))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* (((mv upper lower1) (boundrwc-square-bound-aux a-upper a-lower))
       (lower (or lower1
                  (and (ts-check-rational a mfc state)
                       0))))
    (mv upper lower))
  ///

  (local (defund ts-check-rational-hyp (x mf st)
           (non-exec (Ts-check-rational x mf st))))

  (local (defthm ts-check-rational-when-ts-check-rational-hyp
           (implies (ts-check-rational-hyp x mf st)
                    (ts-check-rational x mf st))
           :hints(("Goal" :in-theory (enable ts-check-rational-hyp)))))

  (local (defthm ts-check-rational-rw
           (b* ((val (boundrw-ev x a))
                (rationalp (ts-check-rational x mf st)))
             (implies (and (rewriting-negative-literal
                            `(ts-check-rational ,x ,mf ,st))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (iff rationalp
                           (and (ts-check-rational-hyp x mf st)
                                (rationalp val)))))
           :hints (("goal" :in-theory (enable ts-check-rational-hyp)))))
  (defret <fn>-correct
    (b* ((a (boundrw-ev a al)))
      (implies (and (boundrw-ev-meta-extract-contextual-facts al)
                    (maybe-boundp nil a a-lower)
                    (maybe-boundp t a a-upper))
               (and (maybe-boundp nil (* a a) lower)
                    (maybe-boundp t (* a a) upper))))))
                               

(define boundrwc-recip-bound ((a-upper maybe-rationalp)
                              (a-lower maybe-rationalp)
                              (a pseudo-termp)
                              &key (mfc 'mfc) (state 'state))
  :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
               (lower maybe-rationalp :rule-classes :type-prescription))
  (b* ((a-upper (maybe-rational-fix a-upper))
       (a-lower (maybe-rational-fix a-lower))
       (sign (and (not (and a-lower (< 0 a-lower)))
                  (not (and a-upper (< a-upper 0)))
                  (ts-check-sign-strict a mfc state)))
       (upper (and a-lower
                   (not (eql 0 a-lower))
                   (or (< 0 a-lower)
                       (and a-upper (< a-upper 0))
                       (eq sign :negative))
                   (/ a-lower)))
       (lower (and a-upper
                   (not (eql 0 a-upper))
                   (or (< a-upper 0)
                       (and a-lower (< 0 a-lower))
                       (eq sign :positive))
                   (/ a-upper))))
    (mv upper lower))
  ///
  (local (defthm reciprocal-antimonotonic-pos
           (implies (and (case-split (< 0 a))
                         (<= a b)
                         (rationalp a)
                         (rationalp b))
                    (<= (/ b) (/ a)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))



  (local (defthm reciprocal-antimonotonic-neg
           (implies (and (case-split (< b 0))
                         (<= a b)
                         (rationalp a)
                         (rationalp b))
                    (<= (/ b) (/ a)))
           :hints (("goal" :use ((:instance mult-both-sides-preserves-<
                                  (x (/ a)) (y (/ b))
                                  (c (* a b)))))
                   (and stable-under-simplificationp
                        '(:nonlinearp t)))))


  (local (defund-nx ts-check-sign-strict-hide (x mfc state)
           (ts-check-sign-strict x mfc state)))

  (local (defret ts-check-sign-strict-positive-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':positive))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :positive)
                             (and (equal (ts-check-sign-strict-hide x mf st) :positive)
                                  (rationalp val)
                                  (< 0 val)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
           :fn ts-check-sign-strict))

  (local (defret ts-check-sign-strict-negative-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':negative))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :negative)
                             (and (equal (ts-check-sign-strict-hide x mf st) :negative)
                                  (rationalp val)
                                  (> 0 val)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
           :fn ts-check-sign-strict))

  (local (in-theory (disable rfix)))
  (local (defthm maybe-rational-fix-when-nonnil
           (implies x
                    (equal (maybe-rational-fix x) (rfix x)))
           :hints(("Goal" :in-theory (enable maybe-rational-fix)))))
  (local (defthm rfix-when-rationalp
           (implies (rationalp x)
                    (equal (rfix x) x))
           :hints(("Goal" :in-theory (enable rfix)))))
  
  (defret <fn>-correct
    (b* ((a (boundrw-ev a al)))
      (implies (and (boundrw-ev-meta-extract-contextual-facts al)
                    (maybe-boundp nil a a-lower)
                    (maybe-boundp t a a-upper))
               (and (maybe-boundp nil (/ a) lower)
                    (maybe-boundp t (/ a) upper))))))

(defines constbounds-rec
  (define constbounds-rec ((x pseudo-termp)
                            (upper-bound-substs boundrw-substlist-p)
                            (lower-bound-substs boundrw-substlist-p)
                            &key (mfc 'mfc) (state 'state))
    :irrelevant-formals-ok t
    :verify-guards nil
    :measure (two-nats-measure (boundrw-rewrite-measure x) 1)
    :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
                 (lower maybe-rationalp :rule-classes :type-prescription))
    :ruler-extenders :all ;; (:lambdas)
    (b* (((mv changed-u ?explicitp-u upper1) (boundrw-find-bound x t upper-bound-substs mfc state))
         ((mv changed-l ?explicitp-l lower1) (boundrw-find-bound x nil lower-bound-substs mfc state))
         (upper1 (and changed-u (consp upper1) (quotep upper1) (rationalp (unquote upper1))
                      (unquote upper1)))
         (lower1 (and changed-l (consp lower1) (quotep lower1) (rationalp (unquote lower1))
                      (unquote lower1)))
         ;; ((when (and upper1 lower1 explicitp-u explicitp-l
         ;;             (ts-check-rational x mfc state)))
         ;;  (mv upper1 lower1))
         ((mv upper2 lower2) (constbounds-rec-operator x upper-bound-substs lower-bound-substs))
         (rat-check (and (or upper1 lower1)
                         (ts-check-rational x mfc state)))
         (upper (if (and upper1 rat-check)
                    (if upper2 ;; (and upper2 (not explicitp-u))
                        (boundrwc-choose-best-bound upper1 upper2 t)
                      upper1)
                  upper2))
         (lower (if (and lower1 rat-check)
                    (if lower2 ;; (and lower2 (not explicitp-l))
                        (boundrwc-choose-best-bound lower1 lower2 nil)
                      lower1)
                  lower2)))
      (mv upper lower)))

  (define constbounds-rec-operator ((x pseudo-termp)
                                     (upper-bound-substs boundrw-substlist-p)
                                     (lower-bound-substs boundrw-substlist-p)
                                     &key (mfc 'mfc) (state 'state))
    :irrelevant-formals-ok t
    :verify-guards nil
    :measure (two-nats-measure (boundrw-rewrite-measure x) 0)
    :returns (mv (upper maybe-rationalp :rule-classes :type-prescription)
                 (lower maybe-rationalp :rule-classes :type-prescription))
    (cond ((atom x) (mv nil nil))
          ((quotep x) (b* ((val (unquote x))
                           (val (and (rationalp val) val)))
                        (mv val val)))
          (t
           (treematch
            x
            ((binary-+ (:? a) (:? b))
             (b* (((mv a-upper a-lower) (constbounds-rec a upper-bound-substs lower-bound-substs))
                  (- (boundrw-rewrite-trace a a-upper a-lower state))
                  ((mv b-upper b-lower) (constbounds-rec b upper-bound-substs lower-bound-substs))
                  (- (and (not (treematch b ((binary-+ (:? a) (:? b)) t) (& nil)))
                          (boundrw-rewrite-trace b b-upper b-lower state))))
               (mv (and a-upper b-upper (+ a-upper b-upper))
                   (and a-lower b-lower (+ a-lower b-lower)))))
            ((unary-- (:? a))
             (b* (((mv a-upper a-lower) (constbounds-rec a upper-bound-substs lower-bound-substs)))
               (mv (and a-lower (- a-lower))
                   (and a-upper (- a-upper)))))
            ((unary-/ (:? a))
             (b* (;; (a-sign (ts-check-sign-strict a mfc state))
                  ;; ((unless a-sign) x)
                  ((mv a-upper a-lower) (constbounds-rec a upper-bound-substs lower-bound-substs)))
               (boundrwc-recip-bound a-upper a-lower a)))
            ((binary-* (:? a) (:? a))
             ;; Special case for square.
             (b* (((mv a-upper a-lower) (constbounds-rec a upper-bound-substs lower-bound-substs)))
               (boundrwc-square-bound a-upper a-lower a)))
            ((binary-* (:? a) (binary-* (:? a) (:? b)))
             (constbounds-rec ;; (pseudo-term-call 'binary-* (list (pseudo-term-call 'binary-* (list a a)) b))
              `(binary-* (binary-* ,a ,a) ,b)
              upper-bound-substs lower-bound-substs))

            ((binary-* (:? a) (:? b))
             ;; The generic answer here is
             ;; (min/max (* a-upper b-upper)
             ;;          (* a-upper b-lower)
             ;;          (* a-lower b-upper)
             ;;          (* a-lower b-lower))
             ;; But in some cases not all 4 limits need to exist to get an
             ;; upper or lower bound.  For example, we can do without b-upper
             ;; for the maximum if a-upper is nonpositive so that (* a-upper
             ;; b-lower) is guaranteed to be greater than (* a-upper b-upper).
             ;; We can further do without a-lower if b-lower is nonnegative.
             
             (b* (((mv a-upper a-lower) (constbounds-rec a upper-bound-substs lower-bound-substs))
                  ((mv b-upper b-lower) (constbounds-rec b upper-bound-substs lower-bound-substs)))
               (boundrwc-multiply-bounds-extrat a-upper a-lower b-upper b-lower)))
            (& (mv nil nil))))))

  ///
  (local (in-theory (disable (:d constbounds-rec)
                             (:t ts-check-rational)
                             (:t ts-check-sign)
                             (:t boundrw-substlist-p)
                             <-*-left-cancel
                             rationalp-implies-acl2-numberp
                             ;; not
                             )))


  ;; (local (defthm reciprocal-antimonotonic-pos
  ;;          (implies (and (case-split (< 0 a))
  ;;                        (<= a b)
  ;;                        (rationalp a)
  ;;                        (rationalp b))
  ;;                   (<= (/ b) (/ a)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))



  ;; (local (defthm reciprocal-antimonotonic-neg
  ;;          (implies (and (case-split (< b 0))
  ;;                        (<= a b)
  ;;                        (rationalp a)
  ;;                        (rationalp b))
  ;;                   (<= (/ b) (/ a)))
  ;;          :hints (("goal" :use ((:instance mult-both-sides-preserves-<
  ;;                                 (x (/ a)) (y (/ b))
  ;;                                 (c (* a b)))))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))


  ;; (local (defthm mult-monotonic-pos
  ;;          (implies (and (rationalp a)
  ;;                        (<= 0 a)
  ;;                        (<= b c))
  ;;                   (<= (* a b) (* a c)))
  ;;          :hints (("goal" :nonlinearp t))))

  ;; (local (defthm mult-monotonic-neg
  ;;          (implies (and (rationalp a)
  ;;                        (<= a 0)
  ;;                        (<= b c))
  ;;                   (<= (* a c) (* a b)))
  ;;          :hints (("goal" :nonlinearp t))))

  ;; ;; Each of these covers a case where we replace a with c, then b with d.
  ;; (local (defthm mult-monotonic-pos-pos-upper
  ;;          (implies (and (<= 0 b)
  ;;                        (<= a c)
  ;;                        (<= 0 c)
  ;;                        (<= b d)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* a b) (* c d)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-pos-pos-lower
  ;;          (implies (and (<= 0 b)
  ;;                        (<= c a)
  ;;                        (<= 0 c)
  ;;                        (<= d b)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* c d) (* a b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-pos-neg-upper
  ;;          (implies (and (<= 0 b)
  ;;                        (<= a c)
  ;;                        (<= c 0)
  ;;                        (<= d b)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* a b) (* c d)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-pos-neg-lower
  ;;          (implies (and (<= 0 b)
  ;;                        (<= c a)
  ;;                        (<= c 0)
  ;;                        (<= b d)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* c d) (* a b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-neg-pos-upper
  ;;          (implies (and (<= b 0)
  ;;                        (<= c a)
  ;;                        (<= 0 c)
  ;;                        (<= b d)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* a b) (* c d)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-neg-pos-lower
  ;;          (implies (and (<= b 0)
  ;;                        (<= a c)
  ;;                        (<= 0 c)
  ;;                        (<= d b)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* c d) (* a b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-neg-neg-upper
  ;;          (implies (and (<= b 0)
  ;;                        (<= c a)
  ;;                        (<= c 0)
  ;;                        (<= d b)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* a b) (* c d)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-neg-neg-lower
  ;;          (implies (and (<= b 0)
  ;;                        (<= a c)
  ;;                        (<= c 0)
  ;;                        (<= b d)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp c)
  ;;                        (rationalp d))
  ;;                   (<= (* c d) (* a b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mult-monotonic-cross
  ;;          (implies (and (<= b bmax)
  ;;                        (<= bmin b)
  ;;                        (<= a amax)
  ;;                        (<= amin a)
  ;;                        (<= amin 0)
  ;;                        (<= 0 amax)
  ;;                        (<= bmin 0)
  ;;                        (<= 0 bmax)
  ;;                        (rationalp a)
  ;;                        (rationalp b)
  ;;                        (rationalp amin)
  ;;                        (rationalp amax)
  ;;                        (rationalp bmin)
  ;;                        (rationalp bmax))
  ;;                   (and (implies (<= (* amax bmax) (* amin bmin))
  ;;                                 (<= (* a b) (* amin bmin)))
  ;;                        (implies (<= (* amin bmin) (* amax bmax))
  ;;                                 (<= (* a b) (* amax bmax)))
  ;;                        (implies (<= (* amax bmin) (* amin bmax))
  ;;                                 (<= (* amax bmin) (* a b)))
  ;;                        (implies (<= (* amin bmax) (* amax bmin))
  ;;                                 (<= (* amin bmax) (* a b)))))
  ;;          :hints (("goal" :cases ((< 0 a)
  ;;                                  (< a 0)))
  ;;                  '(:cases ((< 0 b)
  ;;                            (< b 0)))
  ;;                  ;; '(:cases ((< 0 bmax)
  ;;                  ;;           (< bmax 0)))
  ;;                  ;; '(:cases ((< 0 bmin)
  ;;                  ;;           (< bmin 0)))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))


  ;; (local (defthm square-monotonic-upper
  ;;          (implies (and (<= a amax)
  ;;                        (<= amin a)
  ;;                        (rationalp a)
  ;;                        (rationalp amin)
  ;;                        (rationalp amax))
  ;;                   (and (implies (<= (* amax amax) (* amin amin))
  ;;                                 (<= (* a a) (* amin amin)))
  ;;                        (implies (<= (* amin amin) (* amax amax))
  ;;                                 (<= (* a a) (* amax amax)))))
  ;;          :hints (("goal" :cases ((< 0 a)
  ;;                                  (< a 0)))
  ;;                  (and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; ;; (local (defthm mult-monotonic-neg-upper
  ;; ;;          (implies (and (<= a amax)
  ;; ;;                        (<= amax 0)
  ;; ;;                        (<= bmin b)
  ;; ;;                        (rationalp a)
  ;; ;;                        (rationalp b)
  ;; ;;                        (rationalp amax)
  ;; ;;                        (rationalp bmin))
  ;; ;;                   (<= (* a b) (* amax bmin)))
  ;; ;;          :hints (("goal" :cases ((< amax 0)))
  ;; ;;                  '(:cases ((< b 0)
  ;; ;;                            (equal b 0)))
  ;; ;;                  (and stable-under-simplificationp
  ;; ;;                       '(:nonlinearp t)))))

  ;; (local (defthm mfc-ap-rewrite
  ;;          (implies (and (rewriting-negative-literal `(mfc-ap-fn ,term ,mf ,st 'nil))
  ;;                        (boundrw-ev-meta-extract-contextual-facts a :state st :mfc mf))
  ;;                   (iff (mfc-ap-fn term mf st nil)
  ;;                        (and (hide (mfc-ap-fn term mf st nil))
  ;;                             (not (boundrw-ev term a)))))
  ;;          :hints (("goal" :expand ((:free  (x) (hide x)))))))

  ;; (local (in-theory (disable BOUNDRW-EV-META-EXTRACT-MFC-AP)))

  ;; (local (defthm ts-check-sign/rational-nonnegative-rw
  ;;          (b* ((val (boundrw-ev x a))
  ;;               (category (ts-check-sign/rational x mf st)))
  ;;            (implies (and (rewriting-negative-literal
  ;;                           `(equal (ts-check-sign/rational ,x ,mf ,st) ':nonnegative))
  ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
  ;;                     (iff (equal category :nonnegative)
  ;;                          (and (hide (equal category :nonnegative))
  ;;                               category
  ;;                               (<= 0 val)))))
  ;;          :hints (("goal" :expand ((:free (x) (hide x)))))))

  ;; (local (defthm ts-check-sign/rational-nonpositive-rw
  ;;          (b* ((val (boundrw-ev x a))
  ;;               (category (ts-check-sign/rational x mf st)))
  ;;            (implies (and (rewriting-negative-literal
  ;;                           `(equal (ts-check-sign/rational ,x ,mf ,st) ':nonpositive))
  ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
  ;;                     (iff (equal category :nonpositive)
  ;;                          (and (hide (equal category :nonpositive))
  ;;                               category
  ;;                               (<= val 0)))))
  ;;          :hints (("goal" :expand ((:free (x) (hide x)))))))

  ;; (local (defthm ts-check-sign/rational-rational-rw
  ;;          (b* ((val (boundrw-ev x a))
  ;;               (category (ts-check-sign/rational x mf st)))
  ;;            (implies (and (rewriting-negative-literal
  ;;                           `(ts-check-sign/rational ,x ,mf ,st))
  ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
  ;;                     (iff category
  ;;                          (and (hide category)
  ;;                               (rationalp val)))))
  ;;          :hints (("goal" :expand ((:free (x) (hide x)))))))

  ;; (local (defund ts-check-rational-hyp (x mf st)
  ;;          (non-exec (Ts-check-rational x mf st))))

  ;; (local (defthm ts-check-rational-when-ts-check-rational-hyp
  ;;          (implies (ts-check-rational-hyp x mf st)
  ;;                   (ts-check-rational x mf st))
  ;;          :hints(("Goal" :in-theory (enable ts-check-rational-hyp)))))

  ;; (local (defthm ts-check-rational-rw
  ;;          (b* ((val (boundrw-ev x a))
  ;;               (rationalp (ts-check-rational x mf st)))
  ;;            (implies (and (rewriting-negative-literal
  ;;                           `(ts-check-rational ,x ,mf ,st))
  ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
  ;;                     (iff rationalp
  ;;                          (and (ts-check-rational-hyp x mf st)
  ;;                               (rationalp val)))))
  ;;          :hints (("goal" :in-theory (enable ts-check-rational-hyp)))))


  ;; (local (defthm square-monotonic-nonneg
  ;;          (implies (and (rationalp a)
  ;;                        (rationalp b)
  ;;                        (<= 0 a)
  ;;                        (<= a b))
  ;;                   (<= (* a a) (* b b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm square-lemma1
  ;;          (implies (and (<= (- c) b)
  ;;                        (rationalp a) (rationalp b) (rationalp c)
  ;;                        (<= a b)
  ;;                        (<= c a)
  ;;                        )
  ;;                   (<= (* a a) (* b b)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  ;; (local (defthm square-lemma2
  ;;          (implies (and (<= c (- b))
  ;;                        (rationalp a) (rationalp b) (rationalp c)
  ;;                        (<= a b)
  ;;                        (<= c a)
  ;;                        )
  ;;                   (<= (* a a) (* c c)))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       '(:nonlinearp t)))))

  (local (defthm boundrw-ev-when-match-tree-matchedp
           (implies (match-tree-matchedp pat x alist)
                    (equal (boundrw-ev x a)
                           (boundrw-ev (subst-tree-from-tree pat x) a)))
           :hints(("Goal" :in-theory (e/d (match-tree-matchedp-rw))
                   :use match-tree-is-subst-tree))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  (local (defthm pseudo-termp-when-match-tree-matchedp
           (implies (match-tree-matchedp pat x alist)
                    (equal (pseudo-termp x)
                           (pseudo-termp (subst-tree-from-tree pat x))))
           :hints(("Goal" :in-theory (e/d (match-tree-matchedp-rw))
                   :use match-tree-is-subst-tree))
           :rule-classes ((:rewrite :backchain-limit-lst 0))))

  ;; (local (in-theory (e/d (MATCH-TREE-EQUALS-MATCH-TREE-MATCHEDP-WHEN-SUCCESSFUL)
  ;;                        (match-tree-obj-equals-subst-when-successful))))

  (local (in-theory (disable default-car default-cdr
                             cancel_times-equal-correct
                             cancel_plus-equal-correct
                             pseudo-termp-of-lookup
                             pseudo-termp-cdr-assoc-equal)))

  ;; (local (in-theory (enable match-tree-when-matchedp)))
  ;; (local (defthm match-tree-when-not-matchedp
  ;;          (implies (not (match-tree-matchedp pat x alist))
  ;;                   (not (mv-nth 0 (match-tree pat x alist))))
  ;;          :hints(("Goal" :in-theory (enable match-tree-matchedp-rw)))))

  (local (in-theory (disable constbounds-rec
                             constbounds-rec-operator
                             mv-nth-of-cons
                             not
                             (force)
                             ;; commutativity-of-*
                             (:t boundrw-apply))))

  (local (defund-nx ts-check-sign-hide (x mfc state)
           (ts-check-sign x mfc state)))



  (local (defret ts-check-sign-nonnegative-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign ,x ,mf ,st)  ':nonnegative))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :nonnegative)
                             (and (equal (ts-check-sign-hide x mf st) :nonnegative)
                                  (rationalp val)
                                  (<= 0 val)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
           :fn ts-check-sign))

  (local (defret ts-check-sign-nonpositive-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign ,x ,mf ,st)  ':nonpositive))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :nonpositive)
                             (and (equal (ts-check-sign-hide x mf st) :nonpositive)
                                  (rationalp val)
                                  (<= val 0)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
           :fn ts-check-sign))

  (local (defund-nx ts-check-sign-strict-hide (x mfc state)
           (ts-check-sign-strict x mfc state)))

  (local (defret ts-check-sign-strict-positive-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':positive))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :positive)
                             (and (equal (ts-check-sign-strict-hide x mf st) :positive)
                                  (rationalp val)
                                  (< 0 val)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
           :fn ts-check-sign-strict))

  (local (defret ts-check-sign-strict-negative-correct-rw
           :pre-bind ((mfc mf)
                      (state st))
           (b* ((val (boundrw-ev x a)))
             (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':negative))
                           (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
                      (equal (equal category :negative)
                             (and (equal (ts-check-sign-strict-hide x mf st) :negative)
                                  (rationalp val)
                                  (> 0 val)))))
           :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
           :fn ts-check-sign-strict))

  
  (local (defthm pseudo-termp-implies-consp-cdr
           (implies (and (equal (car x) 'quote)
                         (pseudo-termp x)
                         (consp x))
                    (consp (cdr x)))
           :hints(("Goal" :expand ((pseudo-termp x))))))
  
  (verify-guards+ constbounds-rec
                  :hints(("Goal" :in-theory (disable constbounds-rec
                                                     pseudo-termp-when-match-tree-matchedp)))
                  :guard-debug t)
  
  
  ;; (local (defret ts-check-sign-nil-correct-rw
  ;;          :pre-bind ((mfc mf)
  ;;                     (state st))
  ;;          (b* ((val (boundrw-ev x a)))
  ;;            (implies (and (rewriting-positive-literal `(ts-check-sign ,x ,mf ,st))
  ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
  ;;                     (iff category
  ;;                          (ts-check-sign-hide x mf st))))
  ;;          :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
  ;;          :fn ts-check-sign))

  ;; (defund ts-sign-is (x y)
  ;;   (case y
  ;;     (:nonpositive (and x (not (equal x :nonnegative))))
  ;;     (t (equal x y))))


  ;; (local (defthm ts-sign-is-of-ts-check-sign
  ;;          (equal (ts-sign-is (ts-check-sign x mfc state) y)
  ;;                 (ts-sign-is (ts-check-sign-hide x mfc state) y))
  ;;          :hints(("Goal" :in-theory (enable ts-check-sign-hide)))))

  (local (defthm times-zero-2
           (equal (* x 0) 0)))

  (local (in-theory (disable pseudo-termp-opener)))
  (local (defthm pseudo-termp-opener2
           (implies (and (symbolp fn)
                         (not (equal fn 'quote)))
                    (equal (pseudo-termp (cons fn args))
                           (pseudo-term-listp args)))
           :hints(("Goal" :in-theory (enable pseudo-termp-opener)))))
  (local (in-theory (disable (:t pseudo-termp))))


  ;; (local (defthm cadr-when-quote
  ;;          (implies (and (consp x) (equal (car x) 'quote)
  ;;                        (bind-free '((a . a)) (a))
  ;;                        (equal xx (boundrw-ev x a))
  ;;                        (syntaxp (not (equal xx `(car (cdr ,x))))))
  ;;                   (equal (cadr x)
  ;;                          (boundrw-ev x a)))))


  (local (in-theory (disable pseudo-termp-car)))

  ;; (local (in-theory (disable subst-tree-open)))
  
  ;; (local (in-theory (disable match-tree-alist-opener-theory)))

  
  (std::defret-mutual constbounds-rec-correct
    (defret <fn>-correct
      (b* ((old (boundrw-ev x a)))
        (implies (and (pseudo-termp x)
                      (boundrw-substlist-p upper-bound-substs)
                      (boundrw-substlist-p lower-bound-substs)
                      (boundrw-ev-meta-extract-contextual-facts a)
                      (boundrw-ev-meta-extract-global-facts))
                 (and (maybe-boundp t old upper)
                      (maybe-boundp nil old lower))))
      :hints ('(:do-not-induct t
                :expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable boundrw-find-bound-correct-rw))))
      :fn constbounds-rec)

    (defret <fn>-correct
      (b* ((old (boundrw-ev x a)))
        (implies (and (pseudo-termp x)
                      (boundrw-substlist-p upper-bound-substs)
                      (boundrw-substlist-p lower-bound-substs)
                      (boundrw-ev-meta-extract-contextual-facts a)
                      (boundrw-ev-meta-extract-global-facts))
                 (and (maybe-boundp t old upper)
                      (maybe-boundp nil old lower))))
      :hints ('(:do-not-induct t
                :expand (<call>)
                :in-theory (e/d (match-tree-open-when-successful
                                 boundrw-find-bound-correct-rw)
                                (match-tree-opener-theory
                                 <-*-right-cancel
                                 )))
              (and stable-under-simplificationp
                   '(:in-theory (e/d (match-tree-opener-theory)
                                     (<-*-right-cancel)))))
      :fn constbounds-rec-operator))


  (defret <fn>-upper-bound-linear
    (b* ((old (boundrw-ev x a)))
      (implies (and upper
                    (pseudo-termp x)
                    (boundrw-substlist-p upper-bound-substs)
                    (boundrw-substlist-p lower-bound-substs)
                    (boundrw-ev-meta-extract-contextual-facts a)
                    (boundrw-ev-meta-extract-global-facts))
               (<= old upper)))
    :hints (("goal" :use <fn>-correct
             :in-theory (enable maybe-boundp)))
    :fn constbounds-rec
    :rule-classes :linear)

  (defret <fn>-lower-bound-linear
    (b* ((old (boundrw-ev x a)))
      (implies (and lower
                    (pseudo-termp x)
                    (boundrw-substlist-p upper-bound-substs)
                    (boundrw-substlist-p lower-bound-substs)
                    (boundrw-ev-meta-extract-contextual-facts a)
                    (boundrw-ev-meta-extract-global-facts))
               (<= lower old)))
    :hints (("goal" :use <fn>-correct
             :in-theory (enable maybe-boundp)))
    :fn constbounds-rec
    :rule-classes :linear))





;; (defines boundrw-rewrite
;;   (define boundrw-rewrite ((x pseudo-termp)
;;                            (direction booleanp)
;;                            (bound-alist boundrw-substlist-p)
;;                            (negative-bound-alist boundrw-substlist-p)
;;                            &key (mfc 'mfc) (state 'state))
;;     :irrelevant-formals-ok t
;;     :verify-guards nil
;;     :measure (two-nats-measure (boundrw-rewrite-measure x) 1)
;;     :returns (new-x pseudo-termp
;;                     :hyp (and (pseudo-termp x)
;;                               (boundrw-substlist-p bound-alist)
;;                               (boundrw-substlist-p negative-bound-alist)))
;;     :ruler-extenders (:lambdas)
;;     (b* (((mv changed explicitp new-x1) (boundrw-find-bound x direction bound-alist mfc state))
;;          ((when (and changed explicitp)) new-x1)
;;          (new-x2 (boundrw-rewrite-operator x direction bound-alist negative-bound-alist))
;;          ((unless changed) new-x2))
;;       (boundrw-choose-best-bound new-x1 new-x2 x direction)))

;;   (define boundrw-rewrite-operator ((x pseudo-termp)
;;                                     (direction booleanp)
;;                                     (bound-alist boundrw-substlist-p)
;;                                     (negative-bound-alist boundrw-substlist-p)
;;                                     &key (mfc 'mfc) (state 'state))
;;     :irrelevant-formals-ok t
;;     :verify-guards nil
;;     :measure (two-nats-measure (boundrw-rewrite-measure x) 0)
;;     :returns (new-x pseudo-termp
;;                     :hyp (and (pseudo-termp x)
;;                               (boundrw-substlist-p bound-alist)
;;                               (boundrw-substlist-p negative-bound-alist)))
;;     (cond ((atom x) x)
;;           ((quotep x) x)
;;           (t
;;            (treematch
;;             x
;;             ((binary-+ (:? a) (:? b))
;;              (b* ((new-a (boundrw-rewrite a direction bound-alist negative-bound-alist))
;;                   (new-b (boundrw-rewrite b direction bound-alist negative-bound-alist)))
;;                (boundrw-rewrite-trace a new-a state)
;;                (boundrw-rewrite-trace b new-b state)
;;                (boundrw-apply 'binary-+ (list new-a new-b))))
;;             ((unary-- (:? a))
;;              (boundrw-apply 'unary-- (list
;;                                       (boundrw-rewrite a (not direction) negative-bound-alist bound-alist))))
;;             ((unary-/ (:? a))
;;              (b* (;; (a-sign (ts-check-sign-strict a mfc state))
;;                   ;; ((unless a-sign) x)
;;                   (b (boundrw-rewrite a (not direction) negative-bound-alist bound-alist))
;;                   ;; ((when (or (and (eq a-sign :positive) (not direction))
;;                   ;;            (and (eq a-sign :negative) direction)))
;;                   ;;  ;; a is positive and b is greater or equal, or a is negative
;;                   ;;  ;; and b is less or equal, just by correctness of this
;;                   ;;  ;; function.
;;                   ;;  (if (ts-check-rational b mfc state)
;;                   ;;      (boundrw-apply 'unary-/ (list b))
;;                   ;;    x))
;;                   (a-rat (ts-check-rational a mfc state))
;;                   ((unless a-rat) x)
;;                   (b-sign (ts-check-sign-strict b mfc state))
;;                   ((when
;;                        ;; E.g. we want an upper bound for (/ a) and we have a positive lower bound for a -- return the recip of this bound
;;                        (if direction
;;                            (eq b-sign :positive)
;;                          (eq b-sign :negative)))
;;                    (boundrw-apply 'unary-/ (list b)))
;;                   ((unless (or b-sign (ts-check-rational b mfc state)))
;;                    x)
;;                   ;; E.g. we want an upper bound for (/ a) and we have a potentially
;;                   ;; negative lower bound for a -- need to bound a away from 0
;;                   ;; before we can use the reciprocal of its lower bound.
;;                   ;; Cheap way: check the sign of a
;;                   (a-sign (ts-check-sign-strict a mfc state))
;;                   ((when (if direction
;;                              (eq a-sign :negative)
;;                            (eq a-sign :positive)))
;;                    (boundrw-apply 'unary-/ (list b)))
;;                   ((when a-sign)
;;                    ;; If we got the sign of a but it's not what we want --
;;                    ;; e.g. we want an upper bound for (/ a), have a potentially
;;                    ;; negative lower bound but now know a is positive -- then we
;;                    ;; might as well give up because we don't know how to bound a
;;                    ;; away from 0.
;;                    x)
;;                   ;; More expensive way to bound a away from 0:
;;                   (c (boundrw-rewrite  a (not (not direction)) bound-alist negative-bound-alist))
;;                   (c-sign (ts-check-sign-strict c mfc state))
;;                   ((when (or (and (eq c-sign :positive) (not direction))
;;                              (and (eq c-sign :negative) direction)))
;;                    (boundrw-apply 'unary-/ (list b))))
;;                  x))
;;             ((binary-* (:? a) (:? a))
;;              ;; Special case for square.
;;              (b* (((unless (ts-check-rational a mfc state)) x)
;;                   ;; If we know the sign of a, then we can check just min or max, depending.
;;                   (max-a (boundrw-rewrite a t
;;                                           (if direction bound-alist negative-bound-alist)
;;                                           (if direction negative-bound-alist bound-alist)))
;;                   (min-a (boundrw-rewrite a nil
;;                                           (if direction negative-bound-alist bound-alist)
;;                                           (if direction bound-alist negative-bound-alist)))
;;                   (max-a-sign (ts-check-sign/rational max-a mfc state))
;;                   (min-a-sign (ts-check-sign/rational min-a mfc state))
;;                   ((when (eq max-a-sign :nonpositive))
;;                    (b* ((new-a (if direction min-a max-a))
;;                         (rational (if direction min-a-sign max-a-sign))
;;                         ((unless rational) x))
;;                      (boundrw-apply 'binary-* (list new-a new-a))))
;;                   ((when (eq min-a-sign :nonnegative))
;;                    (b* ((new-a (if direction max-a min-a))
;;                         (rational (if direction max-a-sign min-a-sign))
;;                         ((unless rational)
;;                          x))
;;                      (boundrw-apply 'binary-* (list new-a new-a))))
;;                   ((unless direction)
;;                    ;; As far as we know, A could be positive or negative, but
;;                    ;; this means its square is at least 0.
;;                    ''0)
;;                   ;; Trying to maximize.  Check whether (< (- min) max)
;;                   ((unless (and max-a-sign min-a-sign))
;;                    x)
;;                   (max-abs-gte (mfc-ap
;;                                 `(< ,max-a (unary-- ,min-a))
;;                                 mfc state
;;                                 :forcep nil))
;;                   ((when max-abs-gte)
;;                    (boundrw-apply 'binary-* (list max-a max-a)))
;;                   (min-abs-gte (mfc-ap
;;                                 `(< (unary-- ,max-a) ,min-a)
;;                                 mfc state
;;                                 :forcep nil))
;;                   ((when min-abs-gte)
;;                    (boundrw-apply 'binary-* (list min-a min-a))))
;;                x))
;;             ((binary-* (:? a) (binary-* (:? a) (:? b)))
;;              (boundrw-rewrite ;; (pseudo-term-call 'binary-* (list (pseudo-term-call 'binary-* (list a a)) b))
;;               `(binary-* (binary-* ,a ,a) ,b)
;;               direction bound-alist negative-bound-alist))

;;             ((binary-* (:? a) (:? b))
;;              ;; First rewrite a based on b's type, then rewrite b based on a's
;;              ;; type, then if necessary, go back and look at a again.
;;              (b* (((unless (and (ts-check-rational a mfc state)
;;                                 (ts-check-rational b mfc state)))
;;                    x)
;;                   ;; (b-type (ts-check-sign b mfc state))
;;                   ((mv new-a b-type) (boundrw-rewrite-factor a b direction bound-alist negative-bound-alist))
;;                   ;; (a-type (ts-check-sign new-a mfc state))
;;                   ((mv new-b a-type) (boundrw-rewrite-factor b new-a direction bound-alist negative-bound-alist))
;;                   ((when (or b-type (not a-type)))
;;                    (boundrw-apply 'binary-* (list new-a new-b)))
;;                   ;; (b-type (ts-check-sign new-b mfc state))
;;                   ((mv new-a ?b-type) (boundrw-rewrite-factor a new-b direction bound-alist negative-bound-alist)))
;;                (boundrw-apply 'binary-* (list new-a new-b))))

;;             (& x)))))

;;   (define boundrw-rewrite-factor ((x pseudo-termp)
;;                                   (y pseudo-termp)
;;                                   (direction booleanp)
;;                                   (bound-alist boundrw-substlist-p)
;;                                   (negative-bound-alist boundrw-substlist-p)
;;                                   &key (mfc 'mfc) (state 'state))
;;     :irrelevant-formals-ok t
;;     :verify-guards nil
;;     :measure (two-nats-measure (boundrw-rewrite-measure x) 2)
;;     :returns (mv (new-x pseudo-termp
;;                         :hyp (and (pseudo-termp x)
;;                                   (boundrw-substlist-p bound-alist)
;;                                   (boundrw-substlist-p negative-bound-alist)))
;;                  (y-type symbolp))
;;     (b* ((y-type (ts-check-sign y mfc state)))
;;       (mv (if y-type
;;               (b* (((mv x-dir x-bound-alist x-negative-bound-alist)
;;                     (if (eq y-type :nonnegative)
;;                         (mv direction bound-alist negative-bound-alist)
;;                       (mv (not direction) negative-bound-alist bound-alist)))
;;                    (res
;;                     (boundrw-rewrite x x-dir x-bound-alist x-negative-bound-alist)))
;;                 (if (ts-check-rational res mfc state)
;;                     res
;;                   x))
;;             x)
;;           y-type)))

;;   ///
;;   (local (in-theory (disable (:d boundrw-rewrite)
;;                              (:t ts-check-rational)
;;                              (:t ts-check-sign)
;;                              (:t boundrw-substlist-p)
;;                              <-*-left-cancel
;;                              rationalp-implies-acl2-numberp
;;                              ;; not
;;                              )))

;;   (verify-guards+ boundrw-rewrite
;;                   :hints(("Goal" :in-theory (disable boundrw-rewrite))))

;;   (local (defthm reciprocal-antimonotonic-pos
;;            (implies (and (case-split (< 0 a))
;;                          (<= a b)
;;                          (rationalp a)
;;                          (rationalp b))
;;                     (<= (/ b) (/ a)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))



;;   (local (defthm reciprocal-antimonotonic-neg
;;            (implies (and (case-split (< b 0))
;;                          (<= a b)
;;                          (rationalp a)
;;                          (rationalp b))
;;                     (<= (/ b) (/ a)))
;;            :hints (("goal" :use ((:instance mult-both-sides-preserves-<
;;                                   (x (/ a)) (y (/ b))
;;                                   (c (* a b)))))
;;                    (and stable-under-simplificationp
;;                         '(:nonlinearp t)))))


;;   (local (defthm mult-monotonic-pos
;;          (implies (and (rationalp a)
;;                        (<= 0 a)
;;                        (<= b c))
;;                   (<= (* a b) (* a c)))
;;          :hints (("goal" :nonlinearp t))))

;;   (local (defthm mult-monotonic-neg
;;            (implies (and (rationalp a)
;;                          (<= a 0)
;;                          (<= b c))
;;                     (<= (* a c) (* a b)))
;;            :hints (("goal" :nonlinearp t))))

;;   ;; Each of these covers a case where we replace a with c, then b with d.
;;   (local (defthm mult-monotonic-pos-pos-upper
;;            (implies (and (<= 0 b)
;;                          (<= a c)
;;                          (<= 0 c)
;;                          (<= b d)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* a b) (* c d)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-pos-pos-lower
;;            (implies (and (<= 0 b)
;;                          (<= c a)
;;                          (<= 0 c)
;;                          (<= d b)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* c d) (* a b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-pos-neg-upper
;;            (implies (and (<= 0 b)
;;                          (<= a c)
;;                          (<= c 0)
;;                          (<= d b)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* a b) (* c d)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-pos-neg-lower
;;            (implies (and (<= 0 b)
;;                          (<= c a)
;;                          (<= c 0)
;;                          (<= b d)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* c d) (* a b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-neg-pos-upper
;;            (implies (and (<= b 0)
;;                          (<= c a)
;;                          (<= 0 c)
;;                          (<= b d)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* a b) (* c d)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-neg-pos-lower
;;            (implies (and (<= b 0)
;;                          (<= a c)
;;                          (<= 0 c)
;;                          (<= d b)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* c d) (* a b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-neg-neg-upper
;;            (implies (and (<= b 0)
;;                          (<= c a)
;;                          (<= c 0)
;;                          (<= d b)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* a b) (* c d)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mult-monotonic-neg-neg-lower
;;            (implies (and (<= b 0)
;;                          (<= a c)
;;                          (<= c 0)
;;                          (<= b d)
;;                          (rationalp a)
;;                          (rationalp b)
;;                          (rationalp c)
;;                          (rationalp d))
;;                     (<= (* c d) (* a b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm mfc-ap-rewrite
;;            (implies (and (rewriting-negative-literal `(mfc-ap-fn ,term ,mf ,st 'nil))
;;                          (boundrw-ev-meta-extract-contextual-facts a :state st :mfc mf))
;;                     (iff (mfc-ap-fn term mf st nil)
;;                          (and (hide (mfc-ap-fn term mf st nil))
;;                               (not (boundrw-ev term a)))))
;;            :hints (("goal" :expand ((:free  (x) (hide x)))))))

;;   (local (in-theory (disable BOUNDRW-EV-META-EXTRACT-MFC-AP)))

;;   (local (defthm ts-check-sign/rational-nonnegative-rw
;;            (b* ((val (boundrw-ev x a))
;;                 (category (ts-check-sign/rational x mf st)))
;;              (implies (and (rewriting-negative-literal
;;                             `(equal (ts-check-sign/rational ,x ,mf ,st) ':nonnegative))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (iff (equal category :nonnegative)
;;                            (and (hide (equal category :nonnegative))
;;                                 category
;;                                 (<= 0 val)))))
;;            :hints (("goal" :expand ((:free (x) (hide x)))))))

;;   (local (defthm ts-check-sign/rational-nonpositive-rw
;;            (b* ((val (boundrw-ev x a))
;;                 (category (ts-check-sign/rational x mf st)))
;;              (implies (and (rewriting-negative-literal
;;                             `(equal (ts-check-sign/rational ,x ,mf ,st) ':nonpositive))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (iff (equal category :nonpositive)
;;                            (and (hide (equal category :nonpositive))
;;                                 category
;;                                 (<= val 0)))))
;;            :hints (("goal" :expand ((:free (x) (hide x)))))))

;;   (local (defthm ts-check-sign/rational-rational-rw
;;            (b* ((val (boundrw-ev x a))
;;                 (category (ts-check-sign/rational x mf st)))
;;              (implies (and (rewriting-negative-literal
;;                             `(ts-check-sign/rational ,x ,mf ,st))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (iff category
;;                            (and (hide category)
;;                                 (rationalp val)))))
;;            :hints (("goal" :expand ((:free (x) (hide x)))))))

;;   (local (defund ts-check-rational-hyp (x mf st)
;;            (non-exec (Ts-check-rational x mf st))))

;;   (local (defthm ts-check-rational-when-ts-check-rational-hyp
;;            (implies (ts-check-rational-hyp x mf st)
;;                     (ts-check-rational x mf st))
;;            :hints(("Goal" :in-theory (enable ts-check-rational-hyp)))))

;;   (local (defthm ts-check-rational-rw
;;            (b* ((val (boundrw-ev x a))
;;                 (rationalp (ts-check-rational x mf st)))
;;              (implies (and (rewriting-negative-literal
;;                             `(ts-check-rational ,x ,mf ,st))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (iff rationalp
;;                            (and (ts-check-rational-hyp x mf st)
;;                                 (rationalp val)))))
;;            :hints (("goal" :in-theory (enable ts-check-rational-hyp)))))


;;   (local (defthm square-monotonic-nonneg
;;            (implies (and (rationalp a)
;;                          (rationalp b)
;;                          (<= 0 a)
;;                          (<= a b))
;;                     (<= (* a a) (* b b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm square-lemma1
;;            (implies (and (<= (- c) b)
;;                          (rationalp a) (rationalp b) (rationalp c)
;;                          (<= a b)
;;                          (<= c a)
;;                          )
;;                     (<= (* a a) (* b b)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm square-lemma2
;;            (implies (and (<= c (- b))
;;                          (rationalp a) (rationalp b) (rationalp c)
;;                          (<= a b)
;;                          (<= c a)
;;                          )
;;                     (<= (* a a) (* c c)))
;;            :hints ((and stable-under-simplificationp
;;                         '(:nonlinearp t)))))

;;   (local (defthm boundrw-ev-when-match-tree-matchedp
;;            (implies (match-tree-matchedp pat x alist)
;;                     (equal (boundrw-ev x a)
;;                            (boundrw-ev (subst-tree pat
;;                                                    (match-tree-alist pat x alist)) a)))
;;            :hints(("Goal" :in-theory (e/d (match-tree-matchedp-rw))
;;                    :use match-tree-is-subst-tree))))

;;   (local (defthm pseudo-termp-when-match-tree-matchedp
;;            (implies (match-tree-matchedp pat x alist)
;;                     (equal (pseudo-termp x)
;;                            (pseudo-termp (subst-tree pat
;;                                                    (match-tree-alist pat x alist)))))
;;            :hints(("Goal" :in-theory (e/d (match-tree-matchedp-rw))
;;                    :use match-tree-is-subst-tree))))

;;   ;; (local (in-theory (e/d (MATCH-TREE-EQUALS-MATCH-TREE-MATCHEDP-WHEN-SUCCESSFUL)
;;   ;;                        (match-tree-obj-equals-subst-when-successful))))

;;   (local (in-theory (disable default-car default-cdr
;;                              cancel_times-equal-correct
;;                              cancel_plus-equal-correct
;;                              pseudo-termp-of-lookup
;;                              pseudo-termp-cdr-assoc-equal)))

;;   ;; (local (in-theory (enable match-tree-when-matchedp)))
;;   ;; (local (defthm match-tree-when-not-matchedp
;;   ;;          (implies (not (match-tree-matchedp pat x alist))
;;   ;;                   (not (mv-nth 0 (match-tree pat x alist))))
;;   ;;          :hints(("Goal" :in-theory (enable match-tree-matchedp-rw)))))

;;   (local (in-theory (disable boundrw-rewrite
;;                              boundrw-rewrite-operator
;;                              boundrw-rewrite-factor
;;                              mv-nth-of-cons
;;                              not
;;                              (force)
;;                              ;; commutativity-of-*
;;                              (:t boundrw-apply))))

;;   (local (defund-nx ts-check-sign-hide (x mfc state)
;;            (ts-check-sign x mfc state)))



;;   (local (defret ts-check-sign-nonnegative-correct-rw
;;            :pre-bind ((mfc mf)
;;                       (state st))
;;            (b* ((val (boundrw-ev x a)))
;;              (implies (and (rewriting-negative-literal `(equal (ts-check-sign ,x ,mf ,st)  ':nonnegative))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (equal (equal category :nonnegative)
;;                              (and (equal (ts-check-sign-hide x mf st) :nonnegative)
;;                                   (rationalp val)
;;                                   (<= 0 val)))))
;;            :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
;;            :fn ts-check-sign))

;;   (local (defret ts-check-sign-nonpositive-correct-rw
;;            :pre-bind ((mfc mf)
;;                       (state st))
;;            (b* ((val (boundrw-ev x a)))
;;              (implies (and (rewriting-negative-literal `(equal (ts-check-sign ,x ,mf ,st)  ':nonpositive))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (equal (equal category :nonpositive)
;;                              (and (equal (ts-check-sign-hide x mf st) :nonpositive)
;;                                   (rationalp val)
;;                                   (<= val 0)))))
;;            :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
;;            :fn ts-check-sign))

;;   (local (defund-nx ts-check-sign-strict-hide (x mfc state)
;;            (ts-check-sign-strict x mfc state)))

;;   (local (defret ts-check-sign-strict-positive-correct-rw
;;            :pre-bind ((mfc mf)
;;                       (state st))
;;            (b* ((val (boundrw-ev x a)))
;;              (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':positive))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (equal (equal category :positive)
;;                              (and (equal (ts-check-sign-strict-hide x mf st) :positive)
;;                                   (rationalp val)
;;                                   (< 0 val)))))
;;            :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
;;            :fn ts-check-sign-strict))

;;   (local (defret ts-check-sign-strict-negative-correct-rw
;;            :pre-bind ((mfc mf)
;;                       (state st))
;;            (b* ((val (boundrw-ev x a)))
;;              (implies (and (rewriting-negative-literal `(equal (ts-check-sign-strict ,x ,mf ,st) ':negative))
;;                            (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;                       (equal (equal category :negative)
;;                              (and (equal (ts-check-sign-strict-hide x mf st) :negative)
;;                                   (rationalp val)
;;                                   (> 0 val)))))
;;            :hints(("Goal" :in-theory (enable ts-check-sign-strict-hide)))
;;            :fn ts-check-sign-strict))

  
;;   ;; (local (defret ts-check-sign-nil-correct-rw
;;   ;;          :pre-bind ((mfc mf)
;;   ;;                     (state st))
;;   ;;          (b* ((val (boundrw-ev x a)))
;;   ;;            (implies (and (rewriting-positive-literal `(ts-check-sign ,x ,mf ,st))
;;   ;;                          (boundrw-ev-meta-extract-contextual-facts a :mfc mf :state st))
;;   ;;                     (iff category
;;   ;;                          (ts-check-sign-hide x mf st))))
;;   ;;          :hints(("Goal" :in-theory (enable ts-check-sign-hide)))
;;   ;;          :fn ts-check-sign))

;;   ;; (defund ts-sign-is (x y)
;;   ;;   (case y
;;   ;;     (:nonpositive (and x (not (equal x :nonnegative))))
;;   ;;     (t (equal x y))))


;;   ;; (local (defthm ts-sign-is-of-ts-check-sign
;;   ;;          (equal (ts-sign-is (ts-check-sign x mfc state) y)
;;   ;;                 (ts-sign-is (ts-check-sign-hide x mfc state) y))
;;   ;;          :hints(("Goal" :in-theory (enable ts-check-sign-hide)))))

;;   (local (defthm times-zero-2
;;                 (equal (* x 0) 0)))

;;   (local (in-theory (disable pseudo-termp-opener)))
;;   (local (defthm pseudo-termp-opener2
;;            (implies (and (symbolp fn)
;;                          (not (equal fn 'quote)))
;;                     (equal (pseudo-termp (cons fn args))
;;                            (pseudo-term-listp args)))
;;            :hints(("Goal" :in-theory (enable pseudo-termp-opener)))))
;;   (local (in-theory (disable (:t pseudo-termp))))

;;   (std::defret-mutual boundrw-rewrite-correct
;;     (defret <fn>-correct
;;       (b* ((old (boundrw-ev x a))
;;            (new (boundrw-ev new-x a)))
;;         (implies (and (pseudo-termp x)
;;                       (boundrw-substlist-p bound-alist)
;;                       (boundrw-substlist-p negative-bound-alist)
;;                       (boundrw-ev-meta-extract-contextual-facts a))
;;                  (and (implies direction
;;                                (<= old new))
;;                       (implies (not direction)
;;                                (<= new old)))))
;;       :hints ('(:do-not-induct t
;;                 :expand ((:free (direction) <call>))))
;;       :fn boundrw-rewrite
;;       :rule-classes :linear)

;;     (defret <fn>-correct
;;       (b* ((old (boundrw-ev x a))
;;            (new (boundrw-ev new-x a)))
;;         (implies (and (pseudo-termp x)
;;                       (boundrw-substlist-p bound-alist)
;;                       (boundrw-substlist-p negative-bound-alist)
;;                       (boundrw-ev-meta-extract-contextual-facts a))
;;                  (and (implies direction
;;                                (<= old new))
;;                       (implies (not direction)
;;                                (<= new old)))))
;;       :hints ('(:do-not-induct t
;;                 :expand ((:free (direction) <call>))
;;                 :in-theory (e/d (match-tree-open-when-successful
;;                                  boundrw-find-bound-correct-rw)
;;                                 (match-tree-opener-theory
;;                                  <-*-right-cancel
;;                                  )))
;;               ;; '(:cases (direction))
;;               (and stable-under-simplificationp
;;                    '(:in-theory (e/d (match-tree-opener-theory)
;;                                      (<-*-right-cancel)))))
;;       :fn boundrw-rewrite-operator)

;;     (defret <fn>-correct
;;       (b* ((x-val (boundrw-ev x a))
;;            (y-val (boundrw-ev y a))
;;            (new-x-val (boundrw-ev new-x a)))
;;         (implies (and (pseudo-termp x)
;;                       (pseudo-termp y)
;;                       (boundrw-substlist-p bound-alist)
;;                       (boundrw-substlist-p negative-bound-alist)
;;                       (boundrw-ev-meta-extract-contextual-facts a))
;;                  (and (implies (rationalp x-val)
;;                                (and (implies direction
;;                                              (<= (* x-val y-val)
;;                                                  (* new-x-val y-val)))
;;                                     (implies (not direction)
;;                                              (<= (* new-x-val y-val)
;;                                                  (* x-val y-val)))
;;                                     (rationalp new-x-val)))
;;                       (implies (not y-type)
;;                                (equal new-x-val x-val))
;;                       )))
;;       :hints ('(:do-not-induct t
;;                 ;; :in-theory (enable ts-sign-is)
;;                 :expand ((:free (direction) <call>)))
;;               '(:cases (direction))
;;               )
;;       :fn boundrw-rewrite-factor)))






(local (defthm boundrw-ev-of-hide
         (equal (boundrw-ev `(hide ,x) a)
                (boundrw-ev x a))
         :hints (("goal" :expand ((:free (x) (hide x)))))))


(local (in-theory (disable metafunction-context->ancestors
                           metafunction-context->rcnst
                           rewrite-constant->current-literal
                           weak-metafunction-context-p
                           weak-rewrite-constant-p)))


(define bound-rewrite-check-current-literal (x curr-lit)
  (and (consp curr-lit)
       (equal (cdr curr-lit) x))
  ///
  (defthm bound-rewrite-check-current-literal-fwd
    (implies (bound-rewrite-check-current-literal x curr-lit)
             (Consp curr-lit))
    :rule-classes :forward-chaining))

(define bound-rewrite-metafn ((x pseudo-termp) mfc state)
  :returns (new-x)
  :prepwork ((local (defthm dumb-unquote-guard-lemma
                      (implies (and (pseudo-termp x)
                                    (quotep x))
                               (consp (cdr x)))
                      :hints(("Goal" :in-theory (enable pseudo-termp))))))
  (b* (((unless (and (consp x) (eq (car x) '<)))
        (cw "Bound-rewrite: applied to wrong term: ~x0~%" x)
        x)
       ((unless (and (weak-metafunction-context-p mfc)
                     (weak-rewrite-constant-p
                      (metafunction-context->rcnst mfc))))
        (cw "Bound-rewrite: malformed mfc/rnst?~%")
        x)
       ((when (metafunction-context->ancestors mfc)) ;; don't use this for backchaining
        ;; this is supposed to happen so don't print a warning
        x)
       (curr-lit (rewrite-constant->current-literal
                  (metafunction-context->rcnst mfc)))
       ((unless (bound-rewrite-check-current-literal x curr-lit)
          ;; (and (consp curr-lit)
          ;;            (equal (cdr curr-lit) x))
          )
        ;; this is supposed to happen so don't print a warning
        x)
       (hyp-p (car curr-lit))
       ;; OK, now we've established that we're rewriting a clause literal and
       ;; if hyp-p, it's negated, otherwise not.

       ;; (< a b) can be replaced in a clause by
       ;; (or (hide (< a b))
       ;;     (< au bl))
       ;; where au is an upper bound for a, bl is a lower bound for b.
       ;; This equals (< a b) because (< au bl) implies (< a b).

       ;; (not (< a b)) can be replaced in a clause by
       ;; (not (and (hide (< a b))
       ;;           (< al bu)))
       ;; This is equal because (< a b) implies (< al bu).
       ((unless (and (boundp-global 'boundrw-upper-bounds state)
                     (boundp-global 'boundrw-lower-bounds state)))
        (cw "Bound-rewrite: Bounds lists don't exist~%")
        x)
       (upper-bounds (@ boundrw-upper-bounds))
       (lower-bounds (@ boundrw-lower-bounds))
       ;; ((unless (or (consp upper-bounds) (consp lower-bounds)))
       ;;  (cw "Bound-rewrite: Bounds lists are empty~%")
       ;;  x)
       ((unless (and (boundrw-substlist-p upper-bounds)
                     (boundrw-substlist-p lower-bounds)))
        (cw "Bound-rewrite: Bounds lists are not both boundrw-substlist-ps.~%")
        x)

       ((list a b) (cdr x))
       (a-bound (b* (((mv upper lower) (constbounds-rec a upper-bounds lower-bounds)))
                  (if hyp-p
                      ;; (not (< a b)) case -- replace a by lower bound
                      lower
                    ;; (< a b) case -- replace a by upper bound
                    upper)))
       (b-bound (b* (((mv upper lower) (constbounds-rec b upper-bounds lower-bounds)))
                  (if hyp-p
                      ;; (not (< a b)) case -- replace b by upper bound
                     upper
                    ;; (< a b) case -- replace b by lower bound
                    lower)))

       ((unless (or a-bound b-bound))
        ;; failed to do any replacement, stick with current term
        (cw "failed to do any replacement~%")
        x)
       ((when (and a-bound b-bound
                   ;; If it's going to reduce to just the HIDE term below, then skip it.
                   (if hyp-p
                       (< a-bound b-bound)
                     (<= b-bound a-bound))))
        (cw "Unhelpful result -- ~x0~%"
            (if hyp-p
                `(< ,a-bound ,b-bound)
              `(<= ,b-bound ,a-bound)))
        ;; Reduced it to NIL -- skip instead.
        x)
       (new-a (if a-bound (kwote a-bound) a))
       (new-b (if b-bound (kwote b-bound) b))
       ((when (and (equal new-a a) (equal new-b b)))
        x))

    (if hyp-p
        ;; (not (< a b)) -- use AND
        `(if (hide ,x)
             (< ,new-a ,new-b)
           'nil)
      ;; (< a b) -- use OR
      `(if (hide ,x)
           (hide ,x)
         (< ,new-a ,new-b))))
  ///
  (defthmd bound-rewrite
    (implies (and (pseudo-termp x)
                  (alistp a)
                  (boundrw-ev-meta-extract-contextual-facts a)
                  (boundrw-ev-meta-extract-global-facts))
             (equal (boundrw-ev x a)
                    (boundrw-ev (bound-rewrite-metafn x mfc state) a)))
    :hints (("Goal" :do-not-induct t))
    :rule-classes ((:meta :trigger-fns (<)))))


(define boundrw-translate-subst (cmp lhs rhs freevars state)
  :returns (mv upperp (subst t))
  :mode :program
  (b* (((unless (member cmp '(< <= > >=)))
        (raise "Boundrw-hint: Malformed comparison in substitutions: ~x0~%" cmp)
        (mv nil nil))
       ((mv errp lhs) (translate-cmp lhs t nil nil 'boundrw-hint (w state)
                                     (default-state-vars t)))
       ((when errp) (er hard? errp "~@0~%" lhs) (mv nil nil))
       ((mv errp rhs) (translate-cmp rhs t nil nil 'boundrw-hint (w state)
                                     (default-state-vars t)))
       ((when errp) (er hard? errp "~@0~%" rhs) (mv nil nil))
       (lhs-vars (all-vars lhs))
       (rhs-vars (all-vars rhs))
       ((unless (symbol-listp freevars))
        (raise "Boundrw-hint: freevars must be a symbol list: ~x0~%" freevars)
        (mv nil nil))
       ((unless (subsetp (intersection$ freevars rhs-vars) lhs-vars))
        (raise
         "Boundrw-hint: Free variables must appear in the LHS if they appear in the RHS~%")
        (mv nil nil))
       (bound-vars (set-difference$ (union-eq lhs-vars rhs-vars) freevars))
       (alist (pairlis$ bound-vars bound-vars))
       (subst (make-boundrw-subst :lhs lhs :rhs rhs :alist alist)))
    (mv (consp (member cmp '(< <=))) subst)))

(define boundrw-translate-substs
  ((substs "A list of inequalities, each either the form @('(<= lhs rhs)'), @('(<
            lhs rhs)'), @('(>= lhs rhs)'), or @('(> lhs rhs)'). These are used
            as substitution rules for contexts in which @('lhs') may be replaced
            by its upper or lower bound.")
   state)
  :mode :program
  :returns (mv (upper-bounds)
               (lower-bounds))
  (b* (((when (atom substs)) (mv nil nil))
       ((mv rest-upper rest-lower)
        (boundrw-translate-substs (cdr substs) state))
       (subst (car substs))
       ((mv upperp bound)
        (case-match subst
          ((':free vars (cmp lhs rhs))
           (boundrw-translate-subst cmp lhs rhs vars state))
          ((cmp lhs rhs)
           (boundrw-translate-subst cmp lhs rhs nil state))
          (& (prog2$ (raise "Boundrw-hint: Malformed comparison in substitutions: ~x0~%" subst)
                     (mv nil nil))))))
    (if upperp
        (mv (cons bound rest-upper) rest-lower)
      (mv rest-upper (cons bound rest-lower)))))






(define boundrw-check-add-const-subst (a ;; variable/term
                                       b ;; value
                                       acc
                                       (omit pseudo-term-listp)
                                       upperp)
  (b* (((unless (and (pseudo-termp a)
                     (rationalp b)))
        acc)
       ((when (member-equal a omit)) acc)
       (look (hons-get a acc))
       ((when (or (not look)
                  (not (rationalp (cdr look)))
                  (if upperp
                      (< b (cdr look))
                    (< (cdr look) b))))
        (hons-acons a b acc)))
    acc))


(local (defthmd pseudo-term-listp-when-symbol-listp
         (implies (symbol-listp x)
                  (pseudo-term-listp x))
         :hints(("Goal" :in-theory (enable pseudo-term-listp
                                           pseudo-termp)))))


(define boundrw-const-bound-alist-to-substlist (x (acc boundrw-substlist-p))
  :returns (final-acc boundrw-substlist-p :hyp (boundrw-substlist-p acc)
                      :hints (("goal" :expand ((pseudo-termp (caar x))
                                               (pseudo-termp (list 'quote (cdar x))))
                               :in-theory (enable pseudo-term-listp-when-symbol-listp))))
  :guard-hints (("goal" :expand ((pseudo-termp (caar x))
                                 (pseudo-termp (list 'quote (cdar x))))
                 :in-theory (enable pseudo-term-listp-when-symbol-listp
                                    )))
  (if (atom x)
      acc
    (boundrw-const-bound-alist-to-substlist
     (cdr x)
     (if (and (consp (car x))
              (rationalp (cdar x))
              (pseudo-termp (caar x)))
         (cons (make-boundrw-subst :lhs (caar x) :rhs (kwote (cdar x))
                                   :alist (b* ((vars (simple-term-vars (caar x))))
                                            (pairlis$ vars vars)))
               acc)
       acc))))




(define boundrw-clause-auto-bounds ((clause "clause we're parsing for assumptions")
                                    (upper-bound-acc "alist mapping each variable to its upper bound")
                                    (lower-bound-acc "alist mapping each variable to its lower bound")
                                    (omit pseudo-term-listp))
  :returns (mv new-upper-bound-acc new-lower-bound-acc)
  (b* (((when (atom clause))
        (mv upper-bound-acc lower-bound-acc))
       (lit (car clause))
       ((mv upper-bound-acc lower-bound-acc)
        (case-match lit
          (('< a ('quote b)) ;; hyp form (<= 'b a)
           (mv upper-bound-acc (boundrw-check-add-const-subst a b lower-bound-acc omit nil)))
          (('< ('quote b) a) ;; hyp form (<= a 'b)
           (mv (boundrw-check-add-const-subst a b upper-bound-acc omit t) lower-bound-acc))
          (('not ('< a ('quote b))) ;; hyp form (< a 'b)
           (mv (boundrw-check-add-const-subst a b upper-bound-acc omit t) lower-bound-acc))
          (('not ('< ('quote b) a)) ;; hyp form (< 'b a)
           (mv upper-bound-acc (boundrw-check-add-const-subst a b lower-bound-acc omit nil)))
          (& (mv upper-bound-acc lower-bound-acc)))))
    (boundrw-clause-auto-bounds (cdr clause) upper-bound-acc lower-bound-acc omit)))



(std::defaggrify-defrec prove-spec-var)
;; otf-flg orig-hints displayed-goal user-supplied-term gat-state pool
;; tau-completion-alist hint-settings tag-tree induction-concl-term
;; induction-hyp-terms rewrite-constant

(local (in-theory (disable enabled-structure-p
                           enabled-numep)))


(define boundrw-check-linear-lemma ((x "linear lemma")
                                    (obj pseudo-termp)
                                    (upper-bound-acc "mapping each term to its best upper bound")
                                    (lower-bound-acc "mapping each term to its best lower bound")
                                    (ens enabled-structure-p)
                                    (state))
  :returns (mv new-upper-bound-acc
               new-lower-bound-acc)
  (b* (((unless (weak-linear-lemma-p x))
        (raise "Bad linear lemma: ~x0~%" x)
        (mv upper-bound-acc lower-bound-acc))
       ((linear-lemma x))
       ((unless (and (pseudo-termp x.concl)
                     (not x.hyps)
                     (natp x.nume)
                     (enabled-numep x.nume ens)))
        (mv upper-bound-acc lower-bound-acc))
       ((mv shape-ok negatedp lhs rhs) ;; (< lhs rhs) or (not (< lhs rs))
        (treematch x.concl
         ((< (:? lhs) (:? rhs)) (mv t nil lhs rhs))
         ((not (< (:? lhs) (:? rhs))) (mv t t lhs rhs))
         (& (mv nil nil nil nil))))
       ((unless shape-ok) (mv upper-bound-acc lower-bound-acc))
       ((mv lhs-match alist) (simple-one-way-unify lhs obj nil))
       ((when lhs-match)
        (b* ((rhs-subst (substitute-into-term rhs alist))
             (rhs-vars (all-vars rhs-subst))
             ((when rhs-vars) ;; not constant
              (mv upper-bound-acc lower-bound-acc))
             ((mv eval-err rhs-val) (magic-ev rhs-subst nil state t nil))
             ((when eval-err)
              (mv upper-bound-acc lower-bound-acc)))
          (if negatedp
              (mv upper-bound-acc (boundrw-check-add-const-subst obj rhs-val lower-bound-acc nil nil))
            (mv (boundrw-check-add-const-subst obj rhs-val upper-bound-acc nil t) lower-bound-acc))))
       ((mv rhs-match alist) (simple-one-way-unify rhs obj alist))
       ((when rhs-match)
        (b* ((lhs-subst (substitute-into-term lhs alist))
             (lhs-vars (all-vars lhs-subst))
             ((when lhs-vars) ;; not constant
              (mv upper-bound-acc lower-bound-acc))
             ((mv eval-err lhs-val) (magic-ev lhs-subst nil state t nil))
             ((when eval-err)
              (mv upper-bound-acc lower-bound-acc)))
          (if negatedp
              (mv (boundrw-check-add-const-subst obj lhs-val upper-bound-acc nil t) lower-bound-acc)
            (mv upper-bound-acc (boundrw-check-add-const-subst obj lhs-val lower-bound-acc nil nil))))))
    (mv upper-bound-acc lower-bound-acc)))

(define boundrw-check-linear-lemmas (linear-lemmas
                                     (obj pseudo-termp)
                                     (upper-bound-acc "mapping each term to its best upper bound")
                                     (lower-bound-acc "mapping each term to its best lower bound")
                                     (ens enabled-structure-p)
                                     (state))
  :returns (mv new-upper-bound-acc new-lower-bound-acc)
  (b* (((when (atom linear-lemmas))
        (mv upper-bound-acc lower-bound-acc))
       ((mv upper-bound-acc lower-bound-acc)
        (boundrw-check-linear-lemma (car linear-lemmas) obj upper-bound-acc lower-bound-acc ens state)))
    (boundrw-check-linear-lemmas (cdr linear-lemmas) obj upper-bound-acc lower-bound-acc ens state)))

(local (in-theory (disable w)))

(define boundrw-find-linear-lemmas-for-subterm ((obj pseudo-termp)
                                                (omit pseudo-term-listp)
                                                (upper-bound-acc "mapping each term to its best upper bound")
                                                (lower-bound-acc "mapping each term to its best lower bound")
                                                (ens enabled-structure-p)
                                                (state))
  :returns (mv new-lower-bound-acc new-lower-bound-acc)
  (b* (((unless (and (consp obj)
                     (symbolp (car obj))
                     (not (eq (car obj) 'quote))
                     (not (member-equal obj omit))))
        (mv upper-bound-acc lower-bound-acc))
       (fn (car obj))
       (lemmas (fgetprop fn 'linear-lemmas nil (w state))))
    (boundrw-check-linear-lemmas lemmas obj upper-bound-acc lower-bound-acc ens state)))


(define boundrw-find-linear-lemmas-rec ((x pseudo-termp)
                                        (omit pseudo-term-listp)
                                        (upper-bound-acc "mapping each term to its best upper bound")
                                        (lower-bound-acc "mapping each term to its best lower bound")
                                        (ens enabled-structure-p)
                                        (state))
  :measure (boundrw-rewrite-measure x)
  :prepwork ((local (defthmd cdr-when-equal-cons
                      (implies (equal x (cons a b))
                               (equal (cdr x) b))))

             (local (defthmd car-when-equal-cons
                      (implies (equal x (cons a b))
                               (equal (car x) a))))
             (local (in-theory (disable default-car default-cdr))))
  :hints (("goal" :do-not-induct t))
  (b* (((when(atom x)) (mv upper-bound-acc lower-bound-acc))
       ((When (quotep x)) (mv upper-bound-acc lower-bound-acc))
       ((mv upper-bound-acc lower-bound-acc)
        (boundrw-find-linear-lemmas-for-subterm
         x omit upper-bound-acc lower-bound-acc ens state)))
    (treematch
     x
     ((binary-+ (:? a) (:? b))
      (b* (((mv upper-bound-acc lower-bound-acc)
            (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state)))
        (boundrw-find-linear-lemmas-rec b omit upper-bound-acc lower-bound-acc ens state)))
     ((unary-- (:? a))
      (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state))
     ((unary-/ (:? a))
      (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state))
     ((binary-* (:? a) (:? a))
      (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state))
     ((binary-* (:? a) (binary-* (:? a) (:? b)))
      (boundrw-find-linear-lemmas-rec `(binary-* (binary-* ,a ,a) ,b)
                                      omit upper-bound-acc lower-bound-acc ens state))

     ((binary-* (:? a) (:? b))
      (b* (((mv upper-bound-acc lower-bound-acc)
            (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state)))
        (boundrw-find-linear-lemmas-rec b omit upper-bound-acc lower-bound-acc ens state)))

     (& (mv upper-bound-acc lower-bound-acc)))))


(define boundrw-find-linear-lemmas-clause ((clause pseudo-term-listp)
                                           (omit pseudo-term-listp)
                                           (upper-bound-acc "mapping each term to its best upper bound")
                                           (lower-bound-acc "mapping each term to its best lower bound")
                                           (ens enabled-structure-p)
                                           (state))
  :returns (mv new-upper-bound-acc new-lower-bound-acc)
  (b* (((when (atom clause)) (mv upper-bound-acc lower-bound-acc))
       (lit (car clause))
       ((mv ok a b)
        (treematch
         lit
         ((not (< (:? a) (:? b))) (mv t a b))
         ((< (:? a) (:? b))       (mv t a b))
         (&             (mv nil nil nil))))
       ((unless ok)
        (boundrw-find-linear-lemmas-clause (cdr clause) omit upper-bound-acc lower-bound-acc ens state))
       ((mv upper-bound-acc lower-bound-acc)
        (boundrw-find-linear-lemmas-rec a omit upper-bound-acc lower-bound-acc ens state))
       ((mv upper-bound-acc lower-bound-acc)
        (boundrw-find-linear-lemmas-rec b omit upper-bound-acc lower-bound-acc ens state)))
    (boundrw-find-linear-lemmas-clause (cdr clause) omit upper-bound-acc lower-bound-acc ens state)))




(local (in-theory (disable weak-prove-spec-var-p)))


(define get-ens-from-pspv (pspv)
  :returns (mv err
               (ens (implies (not err) (enabled-structure-p ens))))
  (b* (((unless (weak-prove-spec-var-p pspv))
        (mv "Bad PSPV!~%" nil))
       (rcnst (prove-spec-var->rewrite-constant pspv))
       ((unless (weak-rewrite-constant-p rcnst))
        (mv "Bad RCNST!~%" nil))
       (ens (rewrite-constant->current-enabled-structure rcnst))
       ((unless (enabled-structure-p ens))
        (mv "Bad ENS!~%" nil)))
    (mv nil ens)))

(define boundrw-linear-auto-bounds ((clause pseudo-term-listp)
                                    (upper-bound-acc)
                                    (lower-bound-acc)
                                    (auto-bounds-omit pseudo-term-listp)
                                    (ens enabled-structure-p)
                                    state)
  :returns (mv new-upper-bound-acc new-lower-bound-acc)
  (boundrw-find-linear-lemmas-clause clause auto-bounds-omit upper-bound-acc lower-bound-acc ens state))


(define boundrw-auto-bounds ((clause pseudo-term-listp)
                             (auto-bounds-omit pseudo-term-listp)
                             clause-auto-bounds
                             linear-auto-bounds
                             (ens enabled-structure-p)
                             state)
  :returns (mv (upper-bound-subst boundrw-substlist-p)
               (lower-bound-subst boundrw-substlist-p))
  (b* ((upper-bound-acc nil)
       (lower-bound-acc nil)
       ((mv upper-bound-acc lower-bound-acc)
        (if clause-auto-bounds
            (boundrw-clause-auto-bounds clause upper-bound-acc lower-bound-acc auto-bounds-omit)
          (mv upper-bound-acc lower-bound-acc)))
       ((mv upper-bound-acc lower-bound-acc)
        (if linear-auto-bounds
            (boundrw-linear-auto-bounds clause upper-bound-acc lower-bound-acc auto-bounds-omit ens state)
          (mv upper-bound-acc lower-bound-acc))))
    (mv (boundrw-const-bound-alist-to-substlist (fast-alist-clean upper-bound-acc) nil)
        (boundrw-const-bound-alist-to-substlist (fast-alist-clean lower-bound-acc) nil))))


(define boundrw-translate-omits (omits state)
  :returns (omit-terms)
  :mode :program
  (b* (((when (atom omits)) nil)
       ((mv errp omit) (translate-cmp (car omits) t nil nil 'boundrw-omit (w state)
                                      (default-state-vars t)))
       ((when errp) (er hard? errp "~@0~%" omit)))
    (cons omit (boundrw-translate-omits (cdr omits) state))))



(define rewrite-bounds-fn (substs
                           in-theory-override
                           wait-til-stablep
                           stablep
                           auto-bounds
                           clause-auto-bounds
                           linear-auto-bounds
                           auto-bounds-omit
                           clause
                           pspv
                           state)
  :mode :program
  (b* (((unless (or (not wait-til-stablep) stablep))
        (value nil))
       ((mv user-upper-bounds user-lower-bounds) (boundrw-translate-substs substs state))
       (auto-bounds-omit (boundrw-translate-omits auto-bounds-omit state))
       ((mv err ens) (get-ens-from-pspv pspv))
       ((when err)
        (er soft __function__ err))
       ((mv auto-upper-bounds auto-lower-bounds)
        (boundrw-auto-bounds clause
                             auto-bounds-omit
                             (or auto-bounds clause-auto-bounds)
                             (or auto-bounds linear-auto-bounds)
                             ens state))
       (upper-bounds (append user-upper-bounds auto-upper-bounds))
       (lower-bounds (append user-lower-bounds auto-lower-bounds))
       (state (f-put-global 'boundrw-upper-bounds upper-bounds state))
       (state (f-put-global 'boundrw-lower-bounds lower-bounds state)))
    (value `(:in-theory ,(or in-theory-override
                             '(enable bound-rewrite))
             ;; (cons 'bound-rewrite ,in-theory) -- this is much slower!
             ))))

(defmacro rewrite-bounds (substs
                        &key
                        (in-theory-override 'nil)
                        (wait-til-stablep 't)
                        (stablep 'stable-under-simplificationp)
                        (auto-bounds 'nil)
                        (clause-auto-bounds 'nil)
                        (linear-auto-bounds 'nil)
                        (auto-bounds-omit 'nil))
  `(rewrite-bounds-fn ',substs ',in-theory-override ,wait-til-stablep ,stablep
                      ,auto-bounds
                      ,clause-auto-bounds
                      ,linear-auto-bounds
                      ,auto-bounds-omit
                      clause pspv state))





(encapsulate nil
  (local
   (defthm hard-nonlinear-problem
     (implies (and (rationalp a)
                   (rationalp b)
                   (rationalp c)
                   (<= 0 a)
                   (<= 0 b)
                   (<= 1 c)
                   (<= a 10)
                   (<= b 20)
                   (<= c 30))
              (<= (+ (* a b c)
                     (* a b)
                     (* b c)
                     (* a c))
                  (+ (* 10 20 30)
                     (* 10 20)
                     (* 20 30)
                     (* 10 30))))
     :hints (;; (and stable-under-simplificationp
             ;;      '(:nonlinearp t))
             (rewrite-bounds ((<= a 10)
                              (<= b 20)
                              (<= c 30)))))))

(encapsulate nil
  (local
   (defthm hard-nonlinear-problem
     (implies (and (rationalp a)
                   (rationalp b)
                   (rationalp c)
                   (<= 0 a)
                   (<= 0 b)
                   (<= 1 c)
                   (<= a 10)
                   (<= b 20)
                   (<= c 30))
              (<= (+ (* a b c)
                     (* a b)
                     (* b c)
                     (* a c))
                  (+ (* 10 20 30)
                     (* 10 20)
                     (* 20 30)
                     (* 10 30))))
     :hints (;; (and stable-under-simplificationp
             ;;      '(:nonlinearp t))
             (rewrite-bounds nil :auto-bounds t)))))

(defxdoc rewrite-bounds
  :short "Substitute upper bounds and lower bounds for subterms in comparisons."
  :parents (proof-automation)
  :long " <p>Try to solve inequalities by replacing their subexpressions with
upper and lower bounds.  Usage, as a computed hint:</p>

@({
 (rewrite-bounds
   ;; optional list of user-suggested bounds, of the forms
   ;; (rel bounded-term bound) or (:free (vars) (rel bounded-term bound))
   ((<= a 10)
    ;; use 10 as the upper bound for variable A if we can prove it by backchaining

    (:free (b) (> (foo b c) (bar b)))
    ;; use (bar b) as the lower bound for (foo b c), for any b,
    ;; as long as (bar b) is a ground term that evaluates to a rational
    ;; and we can prove it by backchaining.

    ...)

   ;; optional keywords:

   ;; theory to use in addition to the bound-rewrite meta rule
   ;; -- default is (enable bound-rewrite), i.e., the ambient theory for the
   ;; event plus the bound-rewrite rule.  Must result in bound-rewrite enabled
   ;; or this won't work.
   :in-theory-override (enable foo bar bound-rewrite)

   ;; wait until stable under simplification (default t)
   :wait-til-stablep nil

   ;; look for constant bounds assumed in the clause (recommended)
   :clause-auto-bounds nil
   ;; look for constant bounds from linear rules (not recommended)
   :linear-auto-bounds nil
   ;; use both of these kinds of automatic bounds (not recommended)
   :auto-bounds nil

   ;; do not let auto-bounds add bounds for these terms
   :auto-bounds-omit ((+ a b) (foo c)))
  })

<p>This form enables a meta rule that tries to rewrite literals of the goal
clause that are inequalities so as to prove the clause.  Specifically, it tries
to replace the two sides of each inequality with constant upper or lower
bounds.  The replacement depends on the sense of the literal.  For a
non-negated literal @('(< a b)') -- that is, a conclusion @('(< a b)') or
hypothesis @('(<= b a)') -- we replace @('a') by an upper bound and @('b') by a
lower bound; for a negated such literal we do the opposite.  The resulting new
clause then implies the old one.  Actually, this isn't quite true -- we do the
replacement via a meta rule, which replaces a non-negated literal @('(< a b)')
by @('(or (hide (< a b)) (< a-upper b-lower))'), or a negated literal @('(< a
b)') by @('(and (hide (< a b)) (< a-lower b-upper))').  These replacements are
equivalent to the input literals because @('(< a-upper b-lower)') implies @('(<
a b)') and @('(< a b)') implies @('(< a-lower b-upper)').</p>


<p>Note that performing such replacements (if we remove the @('hide') terms
from consideration) may change a theorem to a non-theorem.  It therefore is
best to be careful to apply this strategy only in the right places.</p>

<p> The bounds for each such literal are determined by an abstract
interpretation of the term, which recursively finds upper and lower bounds. For
a term that is an application of a supported arithmetic operator, we first find
upper and lower bounds for each argument and then use those bounds to determine
the bounds for that operator application.  For other terms, bounds may be found
by user suggestions (verified using backchaining), linear rules, and type
reasoning.</p>

<h3>Details</h3>

<p>ACL2 has a powerful nonlinear arithmetic decision procedure, but
often it stalls on relatively simple proofs.  For example, it goes out to
lunch on this problem:</p>

@({
 (defthm hard-nonlinear-problem
   (implies (and (rationalp a)
                 (rationalp b)
                 (rationalp c)
                 (<= 0 a)
                 (<= 0 b)
                 (<= 1 c)
                 (<= a 10)
                 (<= b 20)
                 (<= c 30))
            (<= (+ (* a b c)
                   (* a b)
                   (* b c)
                   (* a c))
                (+ (* 10 20 30)
                   (* 10 20)
                   (* 20 30)
                   (* 10 30))))
   :hints ((and stable-under-simplificationp
                '(:nonlinearp t))))
 })

<p>This can be proved using a fairly simple argument: each variable only occurs
in the conclusion in a context where the LHS expression increases monotonically
as it increases (because the rest of the variables are nonnegative).
Therefore, to find the upper bound for the LHS expression, set each variable to
its upper bound.  This upper bound is the same as the RHS, and the comparison
is non-strict, so the conclusion holds.</p>

<p>The computed hint @('rewrite-bounds') can run this sort of proof: it
replaces subterms within comparisons with user-provided upper or lower bounds,
depending on the context in which they occur.  In this theorem all of the
occurrences of the variables in the conclusion are upper-boundable instances,
because replacing them by some larger expression results in a new conjecture
that implies the original conjecture.  So we can use the following hint to
prove the theorem instantaneously:</p>

@({
 (rewrite-bounds ((<= a 10)
                  (<= b 20)
                  (<= c 30)))
 })

<p>This instructs our metafunction to replace @('a') by 10, @('b') by 20, and
@('c') by 30 when it encounters them in upper-boundable contexts.  It will also
only do the replacement if it can prove that the inequality holds in its
context.</p>

<p>A final detail: Observe that the occurrence of @('a') in @('(<= 0 a)') is
also an upper-boundable context.  However, performing the replacement here
would be bad because it would destroy the information that @('a') is
nonnegative.  In particular, replacing @('a') by its bound here would result in
a trivially true hypothesis.  The meta rule avoids making such replacements
when it can determine that they are trivial.</p>

<h3>Future work</h3>

<ul>
<li>Add better control over replacements</li>
<li>Add more boundable contexts</li>
<li>Add more smarts to prevent bad replacements.</li>
</ul>")


;; (local
;;  (progn
;;    (defstub a () nil)
;;    (defstub b () nil)
;;    (defstub c () nil)
;;    (defstub dd () nil)

;;    (in-theory (disable <-*-left-cancel
;;                        <-*-right-cancel
;;                        commutativity-of-*
;;                        (tau-system)))

;;    (defthm mult-monotonic-neg-pos-lower-foo
;;      (implies (and (<= (b) 0)
;;                    (<= (a) (c))
;;                    (<= 0   (c))
;;                    (<= (dd) (b))
;;                    (rationalp (a))
;;                    (rationalp (b))
;;                    (rationalp (c))
;;                    (rationalp (dd)))
;;               (<= (* (c) (dd)) (* (a) (b))))
;;      :hints ((rewrite-bounds ((<= (a) (c))
;;                             (<= (dd) (b))))))

;;    (defthm mult-monotonic-neg-pos-lower-foo2
;;      (implies (and (<= b 0)
;;                    (<= a c)
;;                    (<= 0   c)
;;                    (<= d b)
;;                    (rationalp a)
;;                    (rationalp b)
;;                    (rationalp c)
;;                    (rationalp d))
;;               (<= (* c d) (* a b)))
;;      :hints ((rewrite-bounds ((<= a c)
;;                             (<= d b)))))))




#||

dead code
(define boundrw-alist-okp ((alist boundrw-substlist-p)
                           (direction booleanp)
                           a)
  ;; Each key of alist is a term and each value is that term's bound.
  ;; If direction is T, then they are upper bounds, and if NIL, lower bounds.
  :returns (ok)
  (b* (((when (atom alist)) t)
       ((unless (mbt (consp (car alist))))
        (boundrw-alist-okp (cdr alist) direction a))
       ((cons key val) (car alist))
       (kv (boundrw-ev key a))
       (vv (boundrw-ev val a)))
    (and (rationalp kv)
         (rationalp vv)
         (if direction
             (<= kv vv)
           (<= vv kv))
         (boundrw-alist-okp (cdr alist) direction a)))
  ///
  (defret boundrw-alist-ok-correct
    (implies (and ok
                  (hons-assoc-equal x alist))
             (let ((bound (cdr (hons-assoc-equal x alist))))
               (and (rationalp (boundrw-ev bound a))
                    (implies direction
                             (not (< (boundrw-ev bound a)
                                     (boundrw-ev x a))))
                    (implies (not direction)
                             (not (< (boundrw-ev x a)
                                     (boundrw-ev bound a))))))))

  (defcong iff equal (boundrw-alist-okp alist direction a) 2))

||#


(local
 (progn
   (defun trunc32 (x)
     (loghead 32 x))
   (defthm trunc32-upper-bound
     (< (trunc32 x) (expt 2 32))
     :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                            (size1 32) (size 32) (i x)))
              :in-theory (e/d (unsigned-byte-p)
                              (unsigned-byte-p-of-loghead))))
     :rule-classes :linear)
   (defthm trunc32-upper-bound2
     (<= (trunc32 x) (1- (expt 2 32)))
     :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                            (size1 32) (size 32) (i x)))
              :in-theory (e/d (unsigned-byte-p)
                              (unsigned-byte-p-of-loghead))))
     :rule-classes :linear)))




;; MFC fields:
;; (rdepth type-alist obj geneqv wrld fnstack ancestors backchain-limit
;;           simplify-clause-pot-lst rcnst gstack ttree unify-subst)

;; Most of these are probably not important.  probably the important ones:

;; - Type-alist needs to account for any hyps.

;; - Wrld, obviously.
;; - Geneqv, might as well set for equal.
;; - Rcnst -- has a lot of stuff but seems like we mostly just need to populate
;;   it with an ENS.  At least that's what we do in easy-simplify.

;; Closely following what is done in easy-simplify here.
(define mfc-for-rewrite-bounds (hyps ;; translated klist
                                hint
                                state)
  :mode :program

  :returns (mv err-msg mfc new-state)
  (b* ((wrld (w state))
       ((er hint-settings)
        (translate-hint-settings
         'mfc-for-rewrite-bounds ;; name-tree (??)
         "Goal"                  ;; goal-spec string
         hint                   ;; key-val-lst
         __function__
         wrld state))
       (ens (ens state))
       (base-rcnst
        (change rewrite-constant
                *empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t)) ;; ??
       ((er rcnst)
        (load-hint-settings-into-rcnst
         hint-settings base-rcnst
         :mfc-for-rewrite-bounds ;; incrmt-array-name-info
         wrld __function__ state))
       ;; fetch changed ens back out of rcnst
       (ens (access rewrite-constant rcnst :current-enabled-structure))
       ((mv contra-flg hyps-type-alist ?ttree)
        (hyps-type-alist hyps ens wrld state))
       ((when contra-flg)
        (er soft __function__ "Contradiction in hypotheses!")))
    (value
     (make metafunction-context
           :rdepth 1000
           :type-alist hyps-type-alist
           :obj '?
           :geneqv nil ;; equal
           :wrld wrld
           :fnstack nil
           :ancestors nil
           :backchain-limit nil
           :simplify-clause-pot-lst nil
           :rcnst rcnst
           :gstack nil
           :ttree nil
           :unify-subst nil))))



(define rewrite-bounds-find-bounds-fn (term
                                       hyp
                                       hint
                                       substs
                                       auto-bounds
                                       clause-auto-bounds
                                       linear-auto-bounds
                                       auto-bounds-omit
                                       state)
  :mode :program
  (b* ((wrld (w state))
       ((er trans-term)
        (translate term t nil t __function__ wrld state))
       ((er trans-hyp-term)
        (translate hyp t nil t __function__ wrld state))
       (hyps (expand-assumptions-1 trans-hyp-term))
       (fake-clause (append (dumb-negate-lit-lst hyps) (list `(< ,trans-term ,trans-term))))
       ((mv user-upper-bounds user-lower-bounds) (boundrw-translate-substs substs state))
       (auto-bounds-omit (boundrw-translate-omits auto-bounds-omit state))
       (ens (ens state))
       ((mv auto-upper-bounds auto-lower-bounds)
        (boundrw-auto-bounds fake-clause
                             auto-bounds-omit
                             (or auto-bounds clause-auto-bounds)
                             (or auto-bounds linear-auto-bounds)
                             ens state))
       (upper-bounds (append user-upper-bounds auto-upper-bounds))
       (lower-bounds (append user-lower-bounds auto-lower-bounds))
       (state (f-put-global 'boundrw-upper-bounds upper-bounds state))
       (state (f-put-global 'boundrw-lower-bounds lower-bounds state))
       ((er mfc) (mfc-for-rewrite-bounds hyps hint state)))
    (trust-mfc
     (b* (((mv upper lower) (constbounds-rec trans-term upper-bounds lower-bounds)))
       (value (list (if lower (kwote lower) trans-term)
                    (if upper (kwote upper) trans-term)))))))


(defmacro rewrite-bounds-find-bounds (term
                                      &key
                                      (hyp 't)
                                      (hint 'nil)
                                      (substs 'nil)
                                      (auto-bounds 'nil)
                                      (clause-auto-bounds 'nil)
                                      (linear-auto-bounds 'nil)
                                      (auto-bounds-omit 'nil))
  `(rewrite-bounds-find-bounds-fn
    ',term ',hyp ',hint ',substs ',auto-bounds ',clause-auto-bounds ',linear-auto-bounds ',auto-bounds-omit state))


(local
 (encapsulate nil

   (local
    (progn
      (defthm loghead-upper-bound
        (< (loghead n x) (expt 2 (nfix n)))
        :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                               (size1 (nfix n)) (size n) (i x)))
                 :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-loghead))))
        :rule-classes :linear)

      (defthm loghead-lower-bound
        (<= 0 (loghead n x))
        :rule-classes :linear)))

   (assert-event
    (b* (((er bounds) (rewrite-bounds-find-bounds (loghead 32 x) :linear-auto-bounds t)))
      (value (equal bounds (list (kwote 0) (kwote (expt 2 32))))))
    :stobjs-out :auto)

   (assert-event
    (b* (((er bounds) (rewrite-bounds-find-bounds (loghead 32 x) :linear-auto-bounds nil)))
      (value (equal bounds (list (kwote 0) (kwote (expt 2 32))))))
    :stobjs-out :auto)))

(local
 (encapsulate nil

   (local
    (progn
      (defthm loghead-upper-bound
        (<= (loghead n x) (1- (expt 2 (nfix n))))
        :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                               (size1 (nfix n)) (size n) (i x)))
                 :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-of-loghead))))
        :rule-classes :linear)

      (defthm loghead-lower-bound
        (<= 0 (loghead n x))
        :rule-classes :linear)))

   (assert-event
    (b* (((er bounds) (rewrite-bounds-find-bounds (loghead 32 x) :linear-auto-bounds t)))
      (value (equal bounds (list (kwote 0) (kwote (1- (expt 2 32)))))))
    :stobjs-out :auto)

   (assert-event
    (b* (((er bounds) (rewrite-bounds-find-bounds (loghead 32 x) :linear-auto-bounds nil)))
      (value (equal bounds (list (kwote 0) (kwote (1- (expt 2 32)))))))
    :stobjs-out :auto)))







    


