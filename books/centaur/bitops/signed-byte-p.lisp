; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

; signed-byte-p.lisp
; Original author: Jared Davis <jared@centtech.com>
;
; BOZO properly integrate this with ihsext-basics.lisp.

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (in-theory (disable signed-byte-p)))
(local (do-not generalize fertilize))

(local (defthm signed-byte-p-forward
         (implies (signed-byte-p width x)
                  (and (posp width)
                       (integerp x)))
         :rule-classes :forward-chaining
         :hints(("Goal" :in-theory (enable signed-byte-p)))))

(local (defthm unsigned-byte-p-forward
         (implies (unsigned-byte-p width x)
                  (and (natp width)
                       (natp x)))
         :rule-classes :forward-chaining
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(defsection bitops/signed-byte-p
  :parents (bitops signed-byte-p unsigned-byte-p)
  :short "Lemmas about @(see signed-byte-p) and @(see unsigned-byte-p) that are
often useful when optimizing definitions with @(see acl2::type-spec)
declarations."
  :long "<p>BOZO document me.</p>")

(defthm basic-unsigned-byte-p-of-+
  ;; ACL2's fancy unification stuff means this works fine in the common case
  ;; that you're dealing with quoted constants.
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b))
           (unsigned-byte-p (+ 1 n) (+ a b)))
  :hints(("Goal" :in-theory (enable unsigned-byte-p))))

(defthm basic-signed-byte-p-of-+
  ;; ACL2's fancy unification stuff means this works fine in the common case
  ;; that you're dealing with quoted constants.
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p (+ 1 n) (+ a b)))
  :hints(("Goal" :in-theory (enable signed-byte-p))))

(defthm basic-signed-byte-p-of-unary-minus
  ;; ACL2's fancy unification stuff means this works fine in the common case
  ;; that you're dealing with quoted constants.
  (implies (signed-byte-p n x)
           (signed-byte-p (+ 1 n) (- x)))
  :hints(("Goal" :in-theory (enable signed-byte-p))))

(defthm basic-signed-byte-p-of-unary-minus-2
  ;; ACL2's fancy unification stuff means this works fine in the common case
  ;; that you're dealing with quoted constants.
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (- x)))
  :hints(("Goal" :in-theory (enable signed-byte-p unsigned-byte-p))))

(defthm basic-signed-byte-p-of-binary-minus
  ;; ACL2's fancy unification stuff means this works fine in the common case
  ;; that you're dealing with quoted constants.
  ;;
  ;; You might ask, why have this rule when we have the rule about PLUS, since
  ;; (- A B) is just the same as (+ a (unary-- b)).  The answer is: the rule
  ;; about (signed-byte-p (unary-- x)) isn't very nice, and doesn't really give
  ;; us an indirect way to get here.
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p (+ 1 n) (- a b)))
  :hints(("Goal" :in-theory (enable signed-byte-p))))



(defsection basic-unsigned-byte-p-of-*

  (local (defthmd lem-multiply-bound
           (implies (and (natp a1)
                         (natp a2)
                         (natp b1)
                         (natp b2)
                         (< a1 b1)
                         (< a2 b2))
                    (< (* a1 a2)
                       (* b1 b2)))
           :hints(("Goal" :nonlinearp t))))

  (local (defthmd step1
           (implies (and (natp a)
                         (natp b)
                         (posp n1)
                         (posp n2)
                         (< a (expt 2 n1))
                         (< b (expt 2 n2)))
                    (< (* a b)
                       (* (expt 2 n1)
                          (expt 2 n2))))
           :hints(("Goal" :use ((:instance lem-multiply-bound
                                           (a1 a)
                                           (a2 b)
                                           (b1 (expt 2 n1))
                                           (b2 (expt 2 n2))))))))

  (local (defthmd upper-bound
           (implies (and (natp a)
                         (natp b)
                         (posp n1)
                         (posp n2)
                         (< a (expt 2 n1))
                         (< b (expt 2 n2)))
                    (< (* a b) (expt 2 (+ n1 n2))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal" :use ((:instance step1))))))

  (defthm lousy-unsigned-byte-p-of-*-mixed
    ;; Probably won't ever unify with anything.
    (implies (and (unsigned-byte-p n1 a)
                  (unsigned-byte-p n2 b))
             (unsigned-byte-p (+ n1 n2) (* a b)))
    :hints(("Goal" :use ((:instance upper-bound)))))

  (defthm lousy-unsigned-byte-p-of-*
    ;; Probably won't ever unify with anything.
    (implies (and (unsigned-byte-p n a)
                  (unsigned-byte-p n b))
             (unsigned-byte-p (+ n n) (* a b))))

  (local (defthm crock
           (equal (+ (/ n 2) (/ n 2))
                  (fix n))))

  (defthm basic-unsigned-byte-p-of-*
    ;; This use of division looks awful, but note the syntaxp hyp:
    ;; This'll get us things like
    ;;
    ;;   (unsigned-byte-p 32 (* a b))
    ;;
    ;; When we can prove (unsigned-byte-p 16 a) and (unsigned-byte-p 16 b).
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  (unsigned-byte-p (/ n 2) a)
                  (unsigned-byte-p (/ n 2) b))
             (unsigned-byte-p n (* a b)))
    :hints(("Goal" :use ((:instance lousy-unsigned-byte-p-of-*
                                    (n (/ n 2))))))))


(defsection basic-signed-byte-p-of-*

; Blah, this proof is horribly long and ugly.
;
; We want to show:
;
; -2^{n-1} <= a < 2^{n-1}
; -2^{n-1} <= b < 2^{n-1}
;   ===>
; -2^{ n+n-1 } <= ab < 2^{ n+n-1 }
;
; To start with, consider only the upper bound and positive a, b.
;
; From a < 2^{n-1} and b < 2^{n-1} we trivially have:
;
;              ab < 2^{n-1}*2^{n-1}                      (*1)
;
; By trivial simplification on the rhs, we have:
;
;              ab < 2^{n-1 + n-1}
;                 < 2^{n+n-2}
;
; Now clearly 2^{n+n-2} < 2^{n+n-1}, so the bound is satisfied.

  (local (in-theory (enable signed-byte-p)))

  (local (defthmd lem-multiply-bound
           (implies (and (natp a1)
                         (natp a2)
                         (natp b1)
                         (natp b2)
                         (< a1 b1)
                         (< a2 b2))
                    (< (* a1 a2)
                       (* b1 b2)))
           :hints(("Goal" :nonlinearp t))))

  (local (defthmd step1
           (implies (and (natp a)
                         (natp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (< b (expt 2 (+ -1 n))))
                    (< (* a b)
                       (* (expt 2 (+ -1 n))
                          (expt 2 (+ -1 n)))))
           :hints(("Goal" :use ((:instance lem-multiply-bound
                                           (a1 a)
                                           (a2 b)
                                           (b1 (expt 2 (+ -1 n)))
                                           (b2 (expt 2 (+ -1 n)))))))))

  (local (defthmd step2
           (implies (natp n)
                    (equal (* (expt 2 (+ -1 n))
                              (expt 2 (+ -1 n)))
                           (expt 2 (+ -2 n n))))))

  (local (defthmd step3
           (implies (natp n)
                    (< (expt 2 (+ -2 n n))
                       (expt 2 (+ -1 n n))))))

  (local (defthmd pos-case-upper-bound
           (implies (and (natp a)
                         (natp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (< b (expt 2 (+ -1 n))))
                    (< (* a b)
                       (expt 2 (+ -1 n n))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :use ((:instance step1)
                         (:instance step2)
                         (:instance step3))))))

  (local (defthmd pos-case-lower-bound
           (implies (and (natp a)
                         (natp b))
                    (natp (* a b)))
           :rule-classes ((:type-prescription)
                          (:linear :corollary (implies (and (natp a)
                                                            (natp b))
                                                       (<= 0 (* a b)))))))

  (local (defthmd pos-case
           (implies (and (natp a)
                         (natp b)
                         (signed-byte-p n a)
                         (signed-byte-p n b))
                    (signed-byte-p (+ n n) (* a b)))
           :hints(("Goal" :in-theory (enable pos-case-upper-bound)))))


; That concludes the positive/positive case.
; Recall that we want to show:
;
; -2^{n-1} <= a < 2^{n-1}
; -2^{n-1} <= b < 2^{n-1}
;   ===>
; -2^{ n+n-1 } <= ab < 2^{ n+n-1 }
;
; Now let's do the positive * negative case.  WLOG suppose A is positive and B
; is negative.  Now obviously AB is negative so we'll focus on the lower bound
; only.  That is, we want to show:
;
;   -2^{n-1} <= ab
;
; Let V be the -B.  Then obviously AB = -AV and we are trying to show:
;
;   -2^{n-1} <= -av
;
; Multiplying each side by negative 1 flips the inequality, so our goal is:
;
;   av <= 2^{n-1}
;
; Here is what we know:
;
;   0 <= a < 2^{n-1}
;   0 <  v <= 2^{n-1}
;
; This is now exactly the same as the positive case, except that the bound on v
; is only "<=" instead of "<".  The same argument as above still applies, but we
; have to modify it to accommodate the weaker bound.

  (local (defthmd step1b
           (implies (and (natp a)
                         (posp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (<= b (expt 2 (+ -1 n))))
                    (< (* a b)
                       (* (expt 2 (+ -1 n))
                          (expt 2 (+ -1 n)))))
           :hints(("Goal" :use ((:instance lem-multiply-bound
                                           (a1 a)
                                           (a2 b)
                                           (b1 (expt 2 (+ -1 n)))
                                           (b2 (expt 2 (+ -1 n)))))))))

  (local (defthmd mix-case-crux
           (implies (and (natp a)
                         (posp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (<= b (expt 2 (+ -1 n))))
                    (< (* a b)
                       (expt 2 (+ -1 n n))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :in-theory (disable acl2::exponents-add)
                   :nonlinearp t
                   :use ((:instance step1b)
                         (:instance step2)
                         (:instance step3))))))

  (local (defthmd mix-case-unwinding
           (implies (and (natp a)
                         (integerp b)
                         (< b 0)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (<= (- (expt 2 (+ -1 n))) b))
                    (< (- (expt 2 (+ -1 n n)))
                       (* a b)))
           :hints(("Goal" :use ((:instance mix-case-crux (b (- b))))))))

  (local (defthmd mix-case
           (implies (and (natp a)
                         (integerp b)
                         (< b 0)
                         (signed-byte-p n a)
                         (signed-byte-p n b))
                    (signed-byte-p (+ n n) (* a b)))
           :hints(("Goal" :use ((:instance mix-case-unwinding))))))


; The negative negative case is slightly different.
; Recall that we want to show:
;
; -2^{n-1} <= a < 2^{n-1}
; -2^{n-1} <= b < 2^{n-1}
;   ===>
; -2^{ n+n-1 } <= ab < 2^{ n+n-1 }
;
; Suppose A and B are negative.  We know AB will be positive.  We just need to
; show it is less than 2^{n-1}.  Let X and Y be the negations of A,B respectively.
; Then we have:
;
;    0 < x <= 2^{n-1}
;    0 < y <= 2^{n-1}
;
; And we want to show: xy < 2^{n+n-1}.  Trivially:
;
;     xy <= 2^{n-1} * 2^{n-1}
;        <= 2^{n+n-2}
;
; This follows since 2^{n+n-2} < 2^{n+n-1}.

  (local (defthmd step1c
           (implies (and (posp a)
                         (posp b)
                         (posp n)
                         (<= a (expt 2 (+ -1 n)))
                         (<= b (expt 2 (+ -1 n))))
                    (<= (* a b)
                        (* (expt 2 (+ -1 n))
                           (expt 2 (+ -1 n)))))))

  (local (defthmd neg-case-crux
           (implies (and (posp a)
                         (posp b)
                         (posp n)
                         (<= a (expt 2 (+ -1 n)))
                         (<= b (expt 2 (+ -1 n))))
                    (<= (* a b)
                        (expt 2 (+ -2 n n))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :in-theory (disable acl2::exponents-add)
                   :nonlinearp t
                   :use ((:instance step1c)
                         (:instance step2)
                         (:instance step3))))))

  (local (defthmd neg-case-finish
           (implies (natp n)
                    (< (expt 2 (+ -2 n n))
                       (expt 2 (+ -1 n n))))))

  (local (defthmd neg-case-unwinding
           (implies (and (integerp a)
                         (< a 0)
                         (integerp b)
                         (< b 0)
                         (posp n)
                         (<= (- (expt 2 (+ -1 n))) a)
                         (<= (- (expt 2 (+ -1 n))) b))
                    (< (* a b)
                       (expt 2 (+ -1 n n))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal" :use ((:instance neg-case-crux
                                           (a (- a))
                                           (b (- b)))
                                (:instance neg-case-finish))))))

  (local (defthmd neg-case-lower-bound
           (implies (and (integerp a)
                         (< a 0)
                         (integerp b)
                         (< b 0))
                    (natp (* a b)))
           :rule-classes ((:type-prescription)
                          (:linear :corollary (implies (and (< a 0)
                                                            (< b 0)
                                                            (integerp a)
                                                            (integerp b))
                                                       (<= 0 (* a b)))))
           :hints(("Goal" :nonlinearp t))))

  (local (defthmd neg-case
           (implies (and (integerp a)
                         (< a 0)
                         (integerp b)
                         (< b 0)
                         (signed-byte-p n a)
                         (signed-byte-p n b))
                    (signed-byte-p (+ n n) (* a b)))
           :hints(("Goal" :use ((:instance neg-case-unwinding))))))

  (defthm lousy-signed-byte-p-of-*
    (implies (and (signed-byte-p n a)
                  (signed-byte-p n b))
             (signed-byte-p (+ n n) (* a b)))
    :hints(("Goal"
            :in-theory (disable signed-byte-p)
            :use ((:instance pos-case)
                  (:instance mix-case)
                  (:instance mix-case (a b) (b a))
                  (:instance neg-case)))))

  (local (defthm crock
           (equal (+ (/ n 2) (/ n 2))
                  (fix n))))

  (defthm basic-signed-byte-p-of-*
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  (signed-byte-p (/ n 2) a)
                  (signed-byte-p (/ n 2) b))
             (signed-byte-p n (* a b)))
    :hints(("Goal" :use ((:instance lousy-signed-byte-p-of-*
                                    (n (/ n 2)))))))


; A*B is also a signed 2N-bit number when A is signed N-bit and B is an
; unsigned N-bit number.  So, let's prove that now.  WLOG assume A is signed
; and B is unsigned.  If A is positive, then we have:
;
;   0 <= a < 2^n-1
;   0 <= b < 2^n
;
; So ab <= 2^{n+n-1}

  (local (defthmd su-pos-step1
           (implies (and (natp a)
                         (natp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (< b (expt 2 n)))
                    (< (* a b)
                       (* (expt 2 (+ -1 n))
                          (expt 2 n))))
           :hints(("Goal"
                   :use ((:instance lem-multiply-bound
                                    (a1 a)
                                    (a2 b)
                                    (b1 (expt 2 (+ -1 n)))
                                    (b2 (expt 2 n))))))))

  (local (defthmd gather-exponents
           (implies (and (integerp a)
                         (natp n)
                         (natp m))
                    (equal (* (expt a n)
                              (expt a m))
                           (expt a (+ n m))))))

  (local (defthmd su-step2
           (implies (posp n)
                    (equal (* (expt 2 (+ -1 n))
                              (expt 2 n))
                           (expt 2 (+ -1 n n))))
           :hints(("Goal"
                   :use ((:instance gather-exponents
                                    (a 2)
                                    (n (+ -1 n))
                                    (m n)))))))

  (local (defthmd su-pos-upper-bound
           (implies (and (natp a)
                         (natp b)
                         (posp n)
                         (< a (expt 2 (+ -1 n)))
                         (< b (expt 2 n)))
                    (< (* a b)
                       (expt 2 (+ -1 n n))))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :use ((:instance su-pos-step1)
                         (:instance su-step2))))))

  (local (defthmd su-pos-case
           (implies (and (natp a)
                         (signed-byte-p n a)
                         (unsigned-byte-p n b))
                    (signed-byte-p (+ n n) (* a b)))
           :hints(("Goal" :in-theory (enable su-pos-upper-bound)))))

; If A is negative then let V be -A, so we have:
;
;  0 <= V <= 2^{n-1}
;  0 <= B < 2^n
;
; AB = -VB which is obviously negative, but we need to show that:
;
;   -2^{n+n-1} <= -VB
;
; i.e., we need to show
;
;   VB <= 2^{n+n-1}.
;
; This is trivial just by doing the multiplication.

  (local (defthmd lem-multiply-bound-2
           (implies (and (posp a1)
                         (natp a2)
                         (natp b1)
                         (natp b2)
                         (<= a1 b1)
                         (< a2 b2))
                    (< (* a1 a2)
                       (* b1 b2)))
           :hints(("Goal" :nonlinearp t))))

  (local (defthmd su-neg-step1
           (implies (and (posp a)
                         (natp b)
                         (posp n)
                         (<= a (expt 2 (+ -1 n)))
                         (< b (expt 2 n)))
                    (< (* a b)
                       (* (expt 2 (+ -1 n))
                          (expt 2 n))))
           :hints(("Goal"
                   :use ((:instance lem-multiply-bound-2
                                    (a1 a)
                                    (a2 b)
                                    (b1 (expt 2 (+ -1 n)))
                                    (b2 (expt 2 n))))))))

  (local (defthmd su-neg-crux
           (implies (and (integerp a)
                         (< a 0)
                         (natp b)
                         (posp n)
                         (<= (- (expt 2 (+ -1 n))) a)
                         (< b (expt 2 n)))
                    (<= (- (expt 2 (+ -1 n n)))
                        (* a b)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :use ((:instance su-neg-step1 (a (- a)))
                         (:instance su-step2))))))

  (local (defthmd su-neg-case
           (implies (and (integerp a)
                         (< a 0)
                         (signed-byte-p n a)
                         (unsigned-byte-p n b))
                    (signed-byte-p (+ n n) (* a b)))
           :hints(("Goal" :use ((:instance su-neg-crux))))))


  (defthm lousy-signed-byte-p-of-mixed-*
    (implies (and (signed-byte-p n a)
                  (unsigned-byte-p n b))
             (signed-byte-p (+ n n) (* a b)))
    :hints(("Goal"
            :in-theory (disable unsigned-byte-p signed-byte-p)
            :use ((:instance su-neg-case)
                  (:instance su-pos-case)))))

  (defthm basic-signed-byte-p-of-mixed-*
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  (or (and (signed-byte-p (/ n 2) a)
                           (unsigned-byte-p (/ n 2) b))
                      (and (unsigned-byte-p (/ n 2) a)
                           (signed-byte-p (/ n 2) b))))
             (signed-byte-p n (* a b)))
    :hints(("Goal"
            :in-theory (disable signed-byte-p
                                unsigned-byte-p
                                lousy-signed-byte-p-of-mixed-*)
            :use ((:instance lousy-signed-byte-p-of-mixed-*
                             (n (/ n 2)))
                  (:instance lousy-signed-byte-p-of-mixed-*
                             (n (/ n 2))
                             (a b)
                             (b a)))))))



(local (include-book "ihsext-basics"))

(local (defthm logcdr-when-non-integer
         (implies (not (integerp x))
                  (equal (logcdr x) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))

(local (defthm logtail-when-non-integer
         (implies (not (integerp x))
                  (equal (logtail n x) 0))
         :hints(("Goal" :in-theory (enable logtail**)))))

(local (defthm signed-byte-p-monotonicity
         (implies (and (signed-byte-p a x)
                       (<= a b)
                       (integerp b))
                  (signed-byte-p b x))
         :hints(("Goal" :in-theory (enable signed-byte-p**)))))



(defsection signed-byte-p-of-logcdr

  (local (defthm l0
           (implies (signed-byte-p width x)
                    (equal (signed-byte-p (- width 1) (logcdr x))
                           (< 1 width)))
           :hints(("Goal" :in-theory (enable signed-byte-p**)))))

  (local (defthm l1
           (implies (signed-byte-p (+ 1 width) x)
                    (equal (signed-byte-p width (logcdr x))
                           (posp width)))
           :hints(("Goal"
                   :in-theory (disable l0)
                   :use ((:instance l0 (width (+ 1 width))))))))

  (local (defthm crux
           (implies (and (integerp x))
                    (equal (signed-byte-p width (logcdr x))
                           (and (posp width)
                                (signed-byte-p (+ 1 width) x))))
           :hints(("Goal" :in-theory (enable signed-byte-p**)))))

  (defthm signed-byte-p-of-logcdr
    (equal (signed-byte-p width (logcdr x))
           (and (posp width)
                (or (not (integerp x))
                    (signed-byte-p (+ 1 width) x))))))



(defsection signed-byte-p-of-logtail

  (local (defun my-induct (width x n)
           (if (zp n)
               (list width x n)
             (if (zp width)
                 (list width x n)
               (my-induct (- width 1) (logcdr x) (- n 1))))))

  (local (defthmd fwd-crux
           (implies (and (signed-byte-p width x)
                         (natp n)
                         (< n (- width 1)))
                    (signed-byte-p (- width n) (logtail n x)))
           :hints(("Goal"
                   :induct (my-induct width x n)
                   :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthm fwd-corner
           ;; Right shifting by more than width leaves us with either 0 or -1.
           ;; I.e., a signed-byte-p 1.
           (implies (and (signed-byte-p (+ 1 n) x)
                         (natp n) ;; blah, silly/redundant
                         )
                    (signed-byte-p 1 (logtail n x)))
           :hints(("Goal"
                   :induct (logtail n x)
                   :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions)))))

  (local (defthmd fwd-recast
           (implies (and (signed-byte-p (+ width n) x)
                         (posp width)
                         (natp n))
                    (signed-byte-p width (logtail n x)))
           :hints(("Goal" :use ((:instance fwd-crux (width (+ width n))))))))

  (local (defthm rev-corner
           (implies (and (signed-byte-p 1 (logtail n x))
                         (natp n)
                         (integerp x))
                    (signed-byte-p (+ 1 n) x))
           :hints(("Goal"
                   :induct (logtail n x)
                   :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions)))))

  (local (defthmd rev-crux
           (implies (and (signed-byte-p (- width n) (logtail n x))
                         (natp n)
                         (integerp x))
                    (signed-byte-p width x))
           :hints(("Goal"
                   :do-not '(generalize fertilize)
                   :induct (my-induct width x n)
                   :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthmd rev-recast
           (implies (and (signed-byte-p width (logtail n x))
                         (natp n)
                         (integerp x))
                    (signed-byte-p (+ width n) x))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize)
                   :use ((:instance rev-crux (width (+ width n))))))))

  (local (defthmd main
           (implies (and (natp n)
                         (posp width)
                         (integerp x))
                    (equal (signed-byte-p width (logtail n x))
                           (signed-byte-p (+ width n) x)))
           :hints(("Goal"
                   :do-not-induct t
                   :use ((:instance fwd-recast)
                         (:instance rev-recast))))))

  ;; Now we just get rid of the hyps...

  (defthm signed-byte-p-of-logtail
    (equal (signed-byte-p width (logtail n x))
           (and (posp width)
                (or (not (integerp x))
                    (signed-byte-p (+ width (nfix n)) x))))
    :hints(("Goal"
            :do-not-induct t
            :use ((:instance main (n (nfix n))))))))



(defsection unsigned-byte-p-of-minus-when-signed-byte-p

  (local (defthmd l1
           (implies (and (< x 0)
                         (<= (- (expt 2 (+ -1 n))) x)
                         (integerp x)
                         (natp n))
                    (<= (- x) (expt 2 (+ -1 n))))))

  (local (defthmd l2
           (implies (natp n)
                    (< (expt 2 (+ -1 n))
                       (expt 2 n)))))

  (local (defthmd l3
           (implies (and (< x 0)
                         (<= (- (expt 2 (+ -1 n))) x)
                         (integerp x)
                         (natp n))
                    (< (- x) (expt 2 n)))
           :hints(("Goal"
                   :in-theory (disable acl2::expt-is-increasing-for-base>1)
                   :use ((:instance l1)
                         (:instance l2))))))

  (local (in-theory (enable signed-byte-p unsigned-byte-p)))

  (local (defthmd l4
           (implies (and (signed-byte-p n x)
                         (< x 0))
                    (unsigned-byte-p n (- x)))
           :hints(("Goal" :in-theory (enable l3)))))

  (defthm unsigned-byte-p-of-minus-when-signed-byte-p
    (implies (signed-byte-p n x)
             (equal (unsigned-byte-p n (- x))
                    (<= x 0)))
    :hints(("Goal" :in-theory (enable l4)
            :cases ((< x 0) (= x 0))))))



(defsection unsigned-byte-p-of-abs-when-signed-byte-p

  (local (defthmd l0
           (implies (and (signed-byte-p n x)
                         (< x 0))
                    (unsigned-byte-p n (abs x)))))

  (local (defthmd l1
           (implies (natp n)
                    (< (expt 2 (+ -1 n))
                       (expt 2 n)))
           :rule-classes ((:rewrite) (:linear))))

  (local (defthmd l2
           (implies (and (signed-byte-p n x)
                         (<= 0 x))
                    (unsigned-byte-p n (abs x)))
           :hints(("Goal"
                   :in-theory (enable unsigned-byte-p
                                      signed-byte-p
                                      l1)))))

  (defthm unsigned-byte-p-of-abs-when-signed-byte-p
    (implies (signed-byte-p n x)
             (unsigned-byte-p n (abs x)))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l2))))))


(defthm basic-signed-byte-p-of-lognot
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (lognot x)))
  :hints(("Goal" :in-theory (enable lognot
                                    unsigned-byte-p
                                    signed-byte-p))))

(defthm basic-signed-byte-p-of-1+lognot
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (+ 1 (lognot x))))
  :hints(("Goal" :in-theory (enable lognot
                                    unsigned-byte-p
                                    signed-byte-p))))

(defthm signed-byte-p-of-decrement-when-natural-signed-byte-p
  (implies (and (signed-byte-p n x)
                (<= 0 x))
           (signed-byte-p n (1- x)))
  :hints(("Goal" :in-theory (enable signed-byte-p))))

(defthm signed-byte-p-when-signed-byte-p-smaller
  (implies (and (signed-byte-p size1 x)
                (<= size1 (nfix size2)))
           (signed-byte-p size2 x))
   :hints(("Goal" :in-theory (enable signed-byte-p))))


(encapsulate
  ()
  (local (defun my-induct (size1 size2 x)
           (if (or (zp size1)
                   (zp size2))
               (list size1 size2 x)
             (my-induct (- size1 1)
                        (- size2 1)
                        (logcdr x)))))

  (defthm signed-byte-p-when-unsigned-byte-p-smaller
    (implies (and (unsigned-byte-p size1 x)
                  (< size1 (nfix size2)))
             (signed-byte-p size2 x))
    :hints(("Goal"
            :induct (my-induct size1 size2 x)
            :in-theory (enable* ihsext-recursive-redefs
                                ihsext-inductions)))))


(defsection signed-byte-p-of-ash-split

  (local (in-theory (enable* arith-equiv-forwarding)))

  (local (defun dec-induct (n)
           (if (zp n)
               nil
             (dec-induct (- n 1)))))

  (local (defthm k0
           (implies (and (signed-byte-p width x)
                         (natp n))
                    (signed-byte-p (+ width n) (ash x n)))
           :hints(("Goal"
                   :induct (dec-induct n)
                   :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthm k0-better
           (implies (and (signed-byte-p (- width n) x)
                         (natp n))
                    (signed-byte-p width (ash x n)))
           :hints(("Goal"
                   :in-theory (disable k0)
                   :use ((:instance k0
                                    (x x)
                                    (n n)
                                    (width (- width n))))))))

  (local (defthm k1
           (implies (and (signed-byte-p (+ width n) (ash x n))
                         (natp n))
                    (equal (signed-byte-p width x)
                           (and (posp width)
                                (integerp x))))
           :hints(("Goal"
                   :induct (dec-induct n)
                   :in-theory (enable* ihsext-recursive-redefs)))))

  (local (defthm k1-better
           (implies (and (signed-byte-p width (ash x n))
                         (natp n))
                    (equal (signed-byte-p (- width n) x)
                           (and (integerp x)
                                (< n width))))
           :hints(("Goal"
                   :use ((:instance k1 (width (- width n))))))))

  (local (defthm m1
           (implies (not (integerp x))
                    (equal (signed-byte-p width (ash x n))
                           (posp width)))))

  (local (defthm m2
           (implies (not (integerp n))
                    (equal (signed-byte-p width (ash x n))
                           (signed-byte-p width (ifix x))))))

  (local (defthm m3a
           (implies (and (integerp x)
                         (natp n)
                         (< n width))
                    (equal (signed-byte-p width (ash x n))
                           (signed-byte-p (- width n) x)))
           :hints(("Goal"
                   :use ((:instance k0-better)
                         (:instance k1-better))
                   :do-not-induct t))))

  (local (defthm m3b
           (implies (and (integerp x)
                         (integerp n)
                         (< n 0)
                         (posp width))
                    (equal (signed-byte-p width (ash x n))
                           (signed-byte-p (- width n) x)))
           :hints(("Goal"
                   :do-not-induct t
                   :in-theory (disable signed-byte-p-of-logtail
                                       right-shift-to-logtail)
                   :use ((:instance signed-byte-p-of-logtail
                                    (n (- n)))
                         (:instance right-shift-to-logtail
                                    (count n)
                                    (i x)))))))

  (local (defthm m3
           (implies (and (integerp x)
                         (integerp n)
                         (< n width))
                    (equal (signed-byte-p width (ash x n))
                           (and (posp width)
                                (signed-byte-p (- width n) x))))
           :hints(("Goal" :use ((:instance m3a)
                                (:instance m3b))))))

  (local (defun m4-induction-hint (n width)
           ;; Added by Matt K. to accommodate tau soundness bug fix 7/23/2014.
           (declare (xargs :measure (nfix n)))
           (cond ((zp n) width)
                 (t (m4-induction-hint (1- n) (1- width))))))

  (local (defthm equal-0-ash-reduction
           ;; Added by Matt K. to accommodate tau soundness bug fix 7/23/2014.
           (implies (and (<= 0 n)
                         (integerp x))
                    (equal (equal 0 (ash x n))
                           (equal 0 x)))
           :hints (("Goal"
                    :induct (ash x n)
                    :in-theory (enable* ihsext-recursive-redefs
                                        ihsext-inductions)))))

  (local (defthm m4
           (implies (and (integerp x)
                         (natp n)
                         (>= n width))
                    (equal (signed-byte-p width (ash x n))
                           (and (posp width)
                                (equal x 0))))
           :hints(("Goal"
                   :induct
                   ;; Modified by Matt K. to accommodate tau soundness bug fix 7/23/2014.
                   (m4-induction-hint n width)
                   :in-theory (enable* ihsext-recursive-redefs
                                       ihsext-inductions)))))

  (defthm signed-byte-p-of-ash-split
    (equal (signed-byte-p width (ash x n))
           (and (posp width)
                (or (zip x)
                    (if (zip n)
                        (signed-byte-p width (ifix x))
                      (signed-byte-p (- width n) x)))))
    :hints(("Goal"
            :do-not-induct t
            :cases ((< n 0)
                    (< n width))))))



(defsection signed-byte-p-of-loghead

  (local (defthm l0
           (implies (and (natp n)
                         (natp size)
                         (< size n))
                    (signed-byte-p n (loghead size x)))
           :hints(("Goal"
                   :do-not-induct t
                   :in-theory (disable unsigned-byte-p-of-loghead
                                       signed-byte-p-when-unsigned-byte-p-smaller)
                   :use ((:instance unsigned-byte-p-of-loghead
                                    (i x)
                                    (size size)
                                    (size1 size))
                         (:instance signed-byte-p-when-unsigned-byte-p-smaller
                                    (x (loghead size x))
                                    (size1 size)
                                    (size2 n)))))))

  (defthm signed-byte-p-of-loghead
    (implies (and (integerp m)
                  (< (nfix size) m))
             (signed-byte-p m (loghead size x)))))
