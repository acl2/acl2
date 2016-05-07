; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :System)
(include-book "clause-processors/unify-subst" :dir :System)
(include-book "std/lists/mfc-utils" :dir :system)
(include-book "clause-processors/sublis-var-meaning" :dir :system)
(include-book "std/util/defaggrify-defrec" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
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
  
  (defret ts-check-sign-rational-correct
    (b* ((val (boundrw-ev x a)))
      (implies (and rationalp
                    (boundrw-ev-meta-extract-contextual-facts a))
               (rationalp val)))
    :hints (("goal" :use ((:instance boundrw-ev-meta-extract-typeset
                           (term x)))
             :in-theory (disable boundrw-ev-meta-extract-typeset
                                 bitops::logand-with-negated-bitmask))
            (logbitp-reasoning))))




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
       ;; Check that the substitution is ok using relieve-hyp.
       (hyp (if direction
                ;; rhs is upper bound
                `(not (< ,bound.rhs ,bound.lhs))
              ;; rhs is lower bound
              `(not (< ,bound.lhs ,bound.rhs))))
       ;; (- (cw "Checking hyp: ~x0 under substitution: ~x1~%" hyp subst))
       (bound-ok
        (mfc-relieve-hyp
         hyp
         subst '(:rewrite boundrw-dummy-rewrite) '(< fake term) 1 mfc state
         :forcep nil))
       ((when bound-ok)
        (cw "~x0: relieve-hyp~%" x)
        (mv t (substitute-into-term bound.rhs subst)))
       ;; (- (cw "hyp was not relieved: ~x0~%" x))
       ;; (res (mfc-rw+ hyp subst 't nil mfc state :forcep nil))
       ;; (- (cw "result of rewriting: ~x0~%" res))
       (new-x (substitute-into-term bound.rhs subst))
       (bound-ok (mfc-ap
                  ;; term to contradict:
                  (if direction
                      ;; new-x is upper bound
                      `(< ,new-x ,x)
                    ;; new-x is lower bound
                    `(< ,x ,new-x))
                  mfc state
                  :forcep nil))
       ((when bound-ok)
        (cw "~x0: ap~%" x)
        (mv t new-x))
       (- (cw "linear failed to solve: ~x0~%" x)))
    (boundrw-apply-bound x direction (cdr bound-list) mfc state))
  ///
  (defret boundrw-apply-bound-correct
    (implies (and (boundrw-ev-meta-extract-contextual-facts a)
                  (pseudo-termp x)
                  (boundrw-substlist-p bound-list))
             (and (implies direction
                           (<= (boundrw-ev x a) (boundrw-ev new-x a)))
                  (implies (not direction)
                           (<= (boundrw-ev new-x a) (boundrw-ev x a)))))))
  

(define boundrw-rewrite ((x pseudo-termp)
                         (direction booleanp)
                         (bound-alist boundrw-substlist-p)
                         (negative-bound-alist boundrw-substlist-p)
                         &key (mfc 'mfc) (state 'state))
  :irrelevant-formals-ok t
  :verify-guards nil
  :returns (new-x pseudo-termp
                  :hyp (and (pseudo-termp x)
                            (boundrw-substlist-p bound-alist)
                            (boundrw-substlist-p negative-bound-alist)))
  (b* (((mv changed new-x) (boundrw-apply-bound x direction bound-alist mfc state))
       ((when changed) new-x))
    (cond ((atom x) x)
          ((quotep x) x)
          (t
           (case-match x
             (('binary-+ a b) (list 'binary-+
                                    (boundrw-rewrite a direction bound-alist negative-bound-alist)
                                    (boundrw-rewrite b direction bound-alist negative-bound-alist)))

             (('unary-- a) (list 'unary--
                                 (boundrw-rewrite a (not direction) negative-bound-alist bound-alist)))
             (('unary-/ a)
              (b* ((a-sign (ts-check-sign-strict a mfc state))
                   ((unless a-sign) x)
                   (b (boundrw-rewrite a (not direction) negative-bound-alist bound-alist))
                   ((when (or (and (eq a-sign :positive) (not direction))
                              (and (eq a-sign :negative) direction)))
                    ;; a is positive and b is greater or equal, or a is negative
                    ;; and b is less or equal, just by correctness of this
                    ;; function.
                    (if (ts-check-rational b mfc state)
                        `(unary-/ ,b)
                      x))
                   (b-sign (ts-check-sign-strict b mfc state)))
                (if (eq a-sign b-sign)
                    `(unary-/ ,b)
                  x)))

             (('binary-* a b)
              ;; First rewrite a based on b's type, then rewrite b based on a's
              ;; type, then if necessary, go back and look at a again.
              (b* (((unless (and (ts-check-rational a mfc state)
                                 (ts-check-rational b mfc state)))
                    x)
                   (b-type (ts-check-sign b mfc state))
                   (new-a (if b-type
                              (b* (((mv a-dir a-bound-alist a-negative-bound-alist)
                                    (if (eq b-type :nonnegative)
                                        (mv direction bound-alist negative-bound-alist)
                                      (mv (not direction) negative-bound-alist bound-alist)))
                                   (res
                                    (boundrw-rewrite a a-dir a-bound-alist a-negative-bound-alist)))
                                (if (ts-check-rational res mfc state)
                                    res
                                  a))
                            a))
                   (a-type (ts-check-sign new-a mfc state))
                   (new-b (if a-type
                              (b* (((mv b-dir b-bound-alist b-negative-bound-alist)
                                    (if (eq a-type :nonnegative)
                                        (mv direction bound-alist negative-bound-alist)
                                      (mv (not direction) negative-bound-alist bound-alist)))
                                   (res (boundrw-rewrite b b-dir b-bound-alist b-negative-bound-alist)))
                                (if (ts-check-rational res mfc state)
                                    res
                                  b))
                            b))
                   ((when (or b-type (not a-type)))
                    `(binary-* ,new-a ,new-b))
                   (b-type (ts-check-sign new-b mfc state))
                   (new-a (if b-type
                              (b* (((mv a-dir a-bound-alist a-negative-bound-alist)
                                    (if (eq b-type :nonnegative)
                                        (mv direction bound-alist negative-bound-alist)
                                      (mv (not direction) negative-bound-alist bound-alist)))
                                   (res
                                    (boundrw-rewrite a a-dir a-bound-alist a-negative-bound-alist)))
                                (if (ts-check-rational res mfc state)
                                    res
                                  a))
                            a)))
                `(binary-* ,new-a ,new-b)))

             (& x)))))
  ///
  (verify-guards+ boundrw-rewrite)

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


  (local (defthm mult-monotonic-pos
         (implies (and (rationalp a)
                       (<= 0 a)
                       (<= b c))
                  (<= (* a b) (* a c)))
         :hints (("goal" :nonlinearp t))))

  (local (defthm mult-monotonic-neg
           (implies (and (rationalp a)
                         (<= a 0)
                         (<= b c))
                    (<= (* a c) (* a b)))
           :hints (("goal" :nonlinearp t))))

  ;; Each of these covers a case where we replace a with c, then b with d.
  (local (defthm mult-monotonic-pos-pos-upper
           (implies (and (<= 0 b)
                         (<= a c)
                         (<= 0 c)
                         (<= b d)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* a b) (* c d)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

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

  (local (defthm mult-monotonic-pos-neg-lower
           (implies (and (<= 0 b)
                         (<= c a)
                         (<= c 0)
                         (<= b d)
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

  (local (defthm mult-monotonic-neg-pos-lower
           (implies (and (<= b 0)
                         (<= a c)
                         (<= 0 c)
                         (<= d b)
                         (rationalp a)
                         (rationalp b)
                         (rationalp c)
                         (rationalp d))
                    (<= (* c d) (* a b)))
           :hints ((and stable-under-simplificationp
                        '(:nonlinearp t)))))

  (local (defthm mult-monotonic-neg-neg-upper
           (implies (and (<= b 0)
                         (<= c a)
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

  (defret boundrw-rewrite-correct
    (b* ((old (boundrw-ev x a))
         (new (boundrw-ev new-x a)))
      (implies (and (pseudo-termp x)
                    (boundrw-substlist-p bound-alist)
                    (boundrw-substlist-p negative-bound-alist)
                    (boundrw-ev-meta-extract-contextual-facts a))
               (and (implies direction
                             (<= old new))
                    (implies (not direction)
                             (<= new old)))))
    :hints (("goal" :induct t
             :in-theory (disable COMMUTATIVITY-OF-*)))
    :rule-classes (:rewrite :linear)))


(local (defthm boundrw-ev-of-hide
         (equal (boundrw-ev `(hide ,x) a)
                (boundrw-ev x a))
         :hints (("goal" :expand ((:free (x) (hide x)))))))

(std::defaggrify-defrec rewrite-constant)
(std::defaggrify-defrec metafunction-context)

(local (in-theory (disable metafunction-context->ancestors
                           metafunction-context->rcnst
                           rewrite-constant->current-literal
                           weak-metafunction-context-p
                           weak-rewrite-constant-p)))




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
       ((unless (and (consp curr-lit)
                     (equal (cdr curr-lit) x)))
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
       ((unless (or (consp upper-bounds) (consp lower-bounds)))
        (cw "Bound-rewrite: Bounds lists are empty~%")
        x)
       ((unless (and (boundrw-substlist-p upper-bounds)
                     (boundrw-substlist-p lower-bounds)))
        (cw "Bound-rewrite: Bounds lists are not both boundrw-substlist-ps.~%")
        x)
       
       ((list a b) (cdr x))
       (new-a (if hyp-p
                  ;; (not (< a b)) case -- replace a by lower bound
                  (boundrw-rewrite a nil lower-bounds upper-bounds)
                ;; (< a b) case -- replace a by upper bound
                (boundrw-rewrite a t upper-bounds lower-bounds)))
       (new-b (if hyp-p
                  ;; (not (< a b)) case -- replace b by upper bound
                  (boundrw-rewrite b t upper-bounds lower-bounds)
                ;; (< a b) case -- replace b by lower bound
                (boundrw-rewrite b nil lower-bounds upper-bounds)))

       ((when (and (equal new-a a) (equal new-b b)))
        ;; failed to do any replacement, stick with current term
        x)
       (new-a (sublis-var nil new-a))
       (new-b (sublis-var nil new-b))
       ((when (and (quotep new-a)
                   (quotep new-b)
                   (let ((b (unquote new-b))
                         (a (unquote new-a)))
                     (and (rationalp b)
                          (rationalp a)
                          ;; If it's going to reduce to just the HIDE term below, then skip it.
                          (if hyp-p
                              (< a b)
                            (<= b a))))))
        ;; Reduced it to NIL -- skip instead.
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
                  (boundrw-ev-meta-extract-contextual-facts a))
             (equal (boundrw-ev x a)
                    (boundrw-ev (bound-rewrite-metafn x mfc state) a)))
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
       

       
(define rewrite-bounds-fn (substs
                         in-theory
                         wait-til-stablep
                         stablep
                         state)
  :mode :program
  (b* (((unless (or (not wait-til-stablep) stablep))
        (value nil))
       ((mv upper-bounds lower-bounds) (boundrw-translate-substs substs state))
       (state (f-put-global 'boundrw-upper-bounds upper-bounds state))
       (state (f-put-global 'boundrw-lower-bounds lower-bounds state)))
    (value `(:in-theory (cons 'bound-rewrite ,in-theory)))))

(defmacro rewrite-bounds (substs
                        &key
                        (in-theory '(enable))
                        (wait-til-stablep 't)
                        (stablep 'stable-under-simplificationp)
                        (state 'state))
  `(rewrite-bounds-fn ',substs ',in-theory ,wait-til-stablep ,stablep ,state))





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
                            (<= c 30))))))

(defxdoc rewrite-bounds
  :short "Substitute upper bounds and lower bounds for subterms in comparisons."
  :long " <p>Replace expressions by upper and lower bounds for them inside
inequalities.  Usage, as a computed hint:</p>

@({
 (rewrite-bounds ((<= a 10)
                  ;; replace the variable a by 10 in upper-boundable contexts

                  (:free (b) (> (foo b c) (bar b)))
                  ;; replace (foo b c), for any b, by (bar b) in
                  ;; lower-boundable contexts (note: C is not a free variable)

                  ...)

                  ;; optional keywords:

                  ;; theory to use in addition to the bound-rewrite meta rule
                  ;; -- default is (enable), i.e., the ambient theory for the
                  ;; event
                  :in-theory (enable foo bar)

                  ;; wait until stable under simplification (default t)
                  :wait-til-stablep nil)
  })

<p>Here, lower-boundable contexts are locations where decreasing the
subexpression makes the goal stronger, and upper boundable contexts are
locations where increasing the value of the subexpression makes the goal
stronger (the new goal implies the original goal).  More on this below.</p>

<p>Note that performing such replacements may change a theorem to a
non-theorem.  Actually, this procedure leaves the original literals behind
inside @('hide') forms, but it still is best to be careful to apply this
strategy in the right places.</p>

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

<h3>Boundable Contexts</h3>

<p>The rules used for determining which contexts are upper or lower boundable
are as follows.</p>

<table>
<tr><th>Preconditions</th>
    <th>Results</th>
</tr>
<tr><td>@('(< a b)') or @('(<= a b)') in hypothesis/negated literal</td>
    <td>@('a') lower boundable, @('b') upper boundable</td>
</tr>
<tr><td>@('(< a b)') or @('(<= a b)') in conclusion/non-negated literal</td>
    <td>@('a') upper boundable, @('b') lower boundable</td>
</tr>
<tr><td>@('(+ a b)') in upper/lower boundable context</td>
    <td>@('a'), @('b') upper/lower boundable</td>
</tr>
<tr><td>@('(- a)') in upper/lower boundable context</td>
    <td>@('a') lower/upper boundable</td>
</tr>
<tr><td>@('(* a b)') in upper/lower boundable context, @('b') nonnegative</td>
    <td>@('a') upper/lower boundable</td>
</tr>
<tr><td>@('(* a b)') in upper/lower boundable context, @('b') nonpositive</td>
    <td>@('a') lower/upper boundable</td>
</tr>
<tr><td>@('(/ a)') in upper/lower boundable context, @('a') positive/negative</td>
    <td>@('a') lower/upper boundable if bound is also positive/negative</td>
</tr>
</table>

<h3>Future work</h3>

<ul>
<li>Add better control over replacements</li>
<li>Add more boundable contexts</li>
<li>Add more smarts to prevent bad replacements.</li>
</ul>")


(local
 (progn
   (defstub a () nil)
   (defstub b () nil)
   (defstub c () nil)
   (defstub d () nil)

   (in-theory (disable <-*-left-cancel
                       <-*-right-cancel
                       commutativity-of-*
                       (tau-system)))

   (defthm mult-monotonic-neg-pos-lower-foo
     (implies (and (<= (b) 0)
                   (<= (a) (c))
                   (<= 0   (c))
                   (<= (d) (b))
                   (rationalp (a))
                   (rationalp (b))
                   (rationalp (c))
                   (rationalp (d)))
              (<= (* (c) (d)) (* (a) (b))))
     :hints ((rewrite-bounds ((<= (a) (c))
                            (<= (d) (b))))))

   (defthm mult-monotonic-neg-pos-lower-foo2
     (implies (and (<= b 0)
                   (<= a c)
                   (<= 0   c)
                   (<= d b)
                   (rationalp a)
                   (rationalp b)
                   (rationalp c)
                   (rationalp d))
              (<= (* c d) (* a b)))
     :hints ((rewrite-bounds ((<= a c)
                            (<= d b)))))))




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
