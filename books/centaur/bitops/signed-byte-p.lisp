; Centaur Bitops Library
; Copyright (C) 2010-2016 Centaur Technology
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

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/defrule" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (in-theory (disable signed-byte-p floor truncate mod rem)))
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
declarations.")

(local (xdoc::set-default-parents bitops/signed-byte-p))

(defrule basic-unsigned-byte-p-of-+
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b))
           (unsigned-byte-p (+ 1 n) (+ a b)))
  :enable unsigned-byte-p
  :short "Adding N-bit unsigneds creates an N+1 bit unsigned."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-unsigned-byte-p-of-+-with-cin).</p>")

(defrule basic-unsigned-byte-p-of-+-with-cin
  (implies (and (bitp cin)
                (unsigned-byte-p n a)
                (unsigned-byte-p n b))
           (unsigned-byte-p (+ 1 n) (+ cin a b)))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                  (implies (and (bitp cin)
                                (unsigned-byte-p n a)
                                (unsigned-byte-p n b))
                           (unsigned-byte-p (+ 1 n) (+ a b cin)))))
  :enable unsigned-byte-p
  :short "Adding N-bit unsigneds with a carry bit creates an N+1 bit unsigned."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-unsigned-byte-p-of-+).</p>")

(defrule basic-signed-byte-p-of-+
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p (+ 1 n) (+ a b)))
  :enable signed-byte-p
  :short "Adding N-bit signeds creates an N+1 bit signed."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-signed-byte-p-of-+-with-cin).</p>")

(defrule basic-signed-byte-p-of-+-with-cin
  (implies (and (bitp cin)
                (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p (+ 1 n) (+ cin a b)))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                  (implies (and (bitp cin)
                                (signed-byte-p n a)
                                (signed-byte-p n b))
                           (signed-byte-p (+ 1 n) (+ cin a b)))))
  :enable signed-byte-p
  :short "Adding N+1 bit signeds with a carry bit creates an N+1 bit signed."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-signed-byte-p-of-+).</p>")

(defrule basic-signed-byte-p-of-unary-minus
  (implies (signed-byte-p n x)
           (signed-byte-p (+ 1 n) (- x)))
  :enable signed-byte-p
  :short "Negative N-bit signed is an N+1 bit signed."
  :long "<p>The N+1 is needed in case of the minimum integer.</p>

  <p>ACL2's fancy unification stuff means this works fine in the common case
  that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-signed-byte-p-of-unary-minus-2) and @(see
  basic-signed-byte-p-of-binary-minus).</p>")

(defrule basic-signed-byte-p-of-unary-minus-2
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (- x)))
  :enable (signed-byte-p unsigned-byte-p)
  :short "Negative N-bit unsigned is an N+1 bit signed."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants for N and N+1.  See also @(see
  basic-signed-byte-p-of-unary-minus) and @(see
  basic-signed-byte-p-of-binary-minus).</p>")

(defrule basic-signed-byte-p-of-binary-minus
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p (+ 1 n) (- a b)))
  :enable signed-byte-p
  :short "Subtracting N-bit signeds creates an N+1 bit signed."
  :long "<p>ACL2's fancy unification stuff means this works fine in the common
  case that you're dealing with quoted constants.</p>

  <p>You might ask, why have this rule when we have rules like @(see
  basic-signed-byte-p-of-+)?  After all, @('(- a b)') is just the same as @('(+
  a (unary-- b))').  The answer is: the rule about @('(signed-byte-p (unary--
  x))'), @(see basic-signed-byte-p-of-unary-minus), isn't very nice because of
  , and doesn't give us doesn't really give us an indirect way to get here.</p>

  <p>See also @(see basic-signed-byte-p-of-unary-minus) and @(see
  basic-signed-byte-p-of-unary-minus-2).</p>")

(defsection unsigned-byte-p-of-minus-when-signed-byte-p
  :short "Negating an N-bit signed creates an N-bit unsigned exactly when it
          was negative."
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
  :short "Absolute value of an N-bit signed is an N-bit unsigned."

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

(defrule signed-byte-p-of-decrement-when-natural-signed-byte-p
  (implies (and (signed-byte-p n x)
                (<= 0 x))
           (signed-byte-p n (1- x)))
  :enable (signed-byte-p)
  :short "Decrementing a positive N-bit signed creates an N-bit signed.")




(defsection basic-unsigned-byte-p-of-*
  :autodoc nil

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

  (defrule lousy-unsigned-byte-p-of-*-mixed
    (implies (and (unsigned-byte-p n1 a)
                  (unsigned-byte-p n2 b))
             (unsigned-byte-p (+ n1 n2) (* a b)))
    :use ((:instance upper-bound))
    :short "Multiplying N1 * N2 bit unsigneds creates an N1+N2 bit unsigned."
    :long "<p>This is a powerful theorem with a nice statement, but it rarely
           unifies with anything.  See also @(see lousy-unsigned-byte-p-of-*)
           and also @(see basic-unsigned-byte-p-of-*).</p>")

  (defrule lousy-unsigned-byte-p-of-*
    (implies (and (unsigned-byte-p n a)
                  (unsigned-byte-p n b))
             (unsigned-byte-p (+ n n) (* a b)))
    :short "Multiplying N * N bit unsigneds creates an N+N bit unsigned."
    :long "<p>This is a common case of @(see lousy-unsigned-byte-p-of-*-mixed),
           but it also rarely unifies with anything.  See also @(see
           basic-unsigned-byte-p-of-*).</p>")

  (local (defthm crock
           (equal (+ (/ n 2) (/ n 2))
                  (fix n))))

  (defrule basic-unsigned-byte-p-of-*
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  ;; BOZO shouldn't we be using floor instead?
                  (unsigned-byte-p (/ n 2) a)
                  (unsigned-byte-p (/ n 2) b))
             (unsigned-byte-p n (* a b)))
    :use ((:instance lousy-unsigned-byte-p-of-* (n (/ n 2))))
    :short "Multiplying constant N * N bit unsigneds creates an N+N bit unsigned."
    :long "<p>This is a less general but more automatic @(see
            lousy-unsigned-byte-p-of-*) for reasoning about constant widths.
            The use of division here looks awful, but note the @(see syntaxp)
            hyp.  This will let us get us things like:</p>

            @({ (unsigned-byte-p 32 (* a b)) })

            <p>When we know that @('(unsigned-byte-p 16 a)') and
            @('(unsigned-byte-p 16 b)').</p>"))


(defsection basic-signed-byte-p-of-*
  :autodoc nil

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

  (defrule lousy-signed-byte-p-of-*
    (implies (and (signed-byte-p n a)
                  (signed-byte-p n b))
             (signed-byte-p (+ n n) (* a b)))
    :in-theory (disable signed-byte-p)
    :use ((:instance pos-case)
          (:instance mix-case)
          (:instance mix-case (a b) (b a))
          (:instance neg-case))
    :short "Multiplying N * N bit signeds creates an N+N bit signed."
    :long "<p>This is a powerful rule with a nice statement, but it rarely
            unifies with anything automatically.  See also @(see
            basic-signed-byte-p-of-*) and also see @(see
            lousy-signed-byte-p-of-mixed-*).</p>")

  (local (defthm crock
           (equal (+ (/ n 2) (/ n 2))
                  (fix n))))

  (defrule basic-signed-byte-p-of-*
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  ;; BOZO shouldn't we be using floor instead?
                  (signed-byte-p (/ n 2) a)
                  (signed-byte-p (/ n 2) b))
             (signed-byte-p n (* a b)))
    :use ((:instance lousy-signed-byte-p-of-* (n (/ n 2))))
    :short "Multiplying constant N * N bit signeds creates an N+N bit signed."
    :long "<p>This is a less general but more automatic version of @(see
           lousy-signed-byte-p-of-*).  It's good for constant widths.</p>

           <p>The use of division here looks awful, but note the @(see syntaxp)
           hyp: we'll only do these divisions when we know @('n') is a
           constant, e.g., this will let us know that 16-bit multiplication
           gives us a 32-bit result.</p>

           <p>See also @(see basic-signed-byte-p-of-mixed-*).</p>")


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


  (defrule lousy-signed-byte-p-of-mixed-*
    (implies (and (signed-byte-p n a)
                  (unsigned-byte-p n b))
             (signed-byte-p (+ n n) (* a b)))
    :in-theory (disable unsigned-byte-p signed-byte-p)
    :use ((:instance su-neg-case)
          (:instance su-pos-case))
    :short "Multiplying N-bit signed * N-bit unsigned creates an N+N bit signed."
    :long "<p>This is a nice and general theorem but it rarely unifies
           automatically.  See also @(see basic-signed-byte-p-of-mixed-*).
           Also see @(see lousy-signed-byte-p-of-*).</p>")

  (defrule basic-signed-byte-p-of-mixed-*
    (implies (and (syntaxp (quotep n))
                  (natp n)
                  (or (and (signed-byte-p (/ n 2) a)
                           (unsigned-byte-p (/ n 2) b))
                      (and (unsigned-byte-p (/ n 2) a)
                           (signed-byte-p (/ n 2) b))))
             (signed-byte-p n (* a b)))
    :in-theory (disable signed-byte-p
                        unsigned-byte-p
                        lousy-signed-byte-p-of-mixed-*)
    :use ((:instance lousy-signed-byte-p-of-mixed-*
           (n (/ n 2)))
          (:instance lousy-signed-byte-p-of-mixed-*
           (n (/ n 2))
           (a b)
           (b a)))
    :short "Multiplying constant N-bit signed * N-bit unsigned creates an N+N bit signed."
    :long "<p>This is a more automatic @(see lousy-signed-byte-p-of-mixed-*)
           for reasoning about constant widths.  The use of division here looks
           awful, but note the @(see syntaxp) hyp.</p>"))


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

;; (defsection signed-byte-p-of-logcdr
;;   :short "Case-splitting, unconditional."

;;   (local (defthm l0
;;            (implies (signed-byte-p width x)
;;                     (equal (signed-byte-p (- width 1) (logcdr x))
;;                            (< 1 width)))
;;            :hints(("Goal" :in-theory (enable signed-byte-p**)))))

;;   (local (defthm l1
;;            (implies (signed-byte-p (+ 1 width) x)
;;                     (equal (signed-byte-p width (logcdr x))
;;                            (posp width)))
;;            :hints(("Goal"
;;                    :in-theory (disable l0)
;;                    :use ((:instance l0 (width (+ 1 width))))))))

;;   (local (defthm crux
;;            (implies (and (integerp x))
;;                     (equal (signed-byte-p width (logcdr x))
;;                            (and (posp width)
;;                                 (signed-byte-p (+ 1 width) x))))
;;            :hints(("Goal" :in-theory (enable signed-byte-p**)))))

;;   (defrule signed-byte-p-of-logcdr
;;     (equal (signed-byte-p width (logcdr x))
;;            (and (posp width)
;;                 (or (not (integerp x))
;;                     (signed-byte-p (+ 1 width) x))))))


;; (defsection signed-byte-p-of-logtail
;;   :short "Case-splitting, unconditional."

;;   (local (defun my-induct (width x n)
;;            (if (zp n)
;;                (list width x n)
;;              (if (zp width)
;;                  (list width x n)
;;                (my-induct (- width 1) (logcdr x) (- n 1))))))

;;   (local (defthmd fwd-crux
;;            (implies (and (signed-byte-p width x)
;;                          (natp n)
;;                          (< n (- width 1)))
;;                     (signed-byte-p (- width n) (logtail n x)))
;;            :hints(("Goal"
;;                    :induct (my-induct width x n)
;;                    :in-theory (enable* ihsext-recursive-redefs)))))

;;   (local (defthm fwd-corner
;;            ;; Right shifting by more than width leaves us with either 0 or -1.
;;            ;; I.e., a signed-byte-p 1.
;;            (implies (and (signed-byte-p (+ 1 n) x)
;;                          (natp n) ;; blah, silly/redundant
;;                          )
;;                     (signed-byte-p 1 (logtail n x)))
;;            :hints(("Goal"
;;                    :induct (logtail n x)
;;                    :in-theory (enable* ihsext-recursive-redefs
;;                                        ihsext-inductions)))))

;;   (local (defthmd fwd-recast
;;            (implies (and (signed-byte-p (+ width n) x)
;;                          (posp width)
;;                          (natp n))
;;                     (signed-byte-p width (logtail n x)))
;;            :hints(("Goal" :use ((:instance fwd-crux (width (+ width n))))))))

;;   (local (defthm rev-corner
;;            (implies (and (signed-byte-p 1 (logtail n x))
;;                          (natp n)
;;                          (integerp x))
;;                     (signed-byte-p (+ 1 n) x))
;;            :hints(("Goal"
;;                    :induct (logtail n x)
;;                    :in-theory (enable* ihsext-recursive-redefs
;;                                        ihsext-inductions)))))

;;   (local (defthmd rev-crux
;;            (implies (and (signed-byte-p (- width n) (logtail n x))
;;                          (natp n)
;;                          (integerp x))
;;                     (signed-byte-p width x))
;;            :hints(("Goal"
;;                    :do-not '(generalize fertilize)
;;                    :induct (my-induct width x n)
;;                    :in-theory (enable* ihsext-recursive-redefs)))))

;;   (local (defthmd rev-recast
;;            (implies (and (signed-byte-p width (logtail n x))
;;                          (natp n)
;;                          (integerp x))
;;                     (signed-byte-p (+ width n) x))
;;            :hints(("Goal"
;;                    :do-not-induct t
;;                    :do-not '(generalize fertilize)
;;                    :use ((:instance rev-crux (width (+ width n))))))))

;;   (local (defthmd main
;;            (implies (and (natp n)
;;                          (posp width)
;;                          (integerp x))
;;                     (equal (signed-byte-p width (logtail n x))
;;                            (signed-byte-p (+ width n) x)))
;;            :hints(("Goal"
;;                    :do-not-induct t
;;                    :use ((:instance fwd-recast)
;;                          (:instance rev-recast))))))

;;   ;; Now we just get rid of the hyps...

;;   (defthm signed-byte-p-of-logtail
;;     (equal (signed-byte-p width (logtail n x))
;;            (and (posp width)
;;                 (or (not (integerp x))
;;                     (signed-byte-p (+ width (nfix n)) x))))
;;     :hints(("Goal"
;;             :do-not-induct t
;;             :use ((:instance main (n (nfix n))))))))


(defrule basic-signed-byte-p-of-lognot
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (lognot x)))
  :enable (lognot unsigned-byte-p signed-byte-p)
  :short "Lognot of an N-bit unsigned is an N+1 bit signed.")

(defrule basic-signed-byte-p-of-1+lognot
  (implies (unsigned-byte-p n x)
           (signed-byte-p (+ 1 n) (+ 1 (lognot x))))
  :enable (lognot unsigned-byte-p signed-byte-p)
  :short "Lognot+1 (two's complement) of an N-bit unsigned is an N+1 bit signed.")

(defrule signed-byte-p-when-signed-byte-p-smaller
  (implies (and (signed-byte-p size1 x)
                (<= size1 (nfix size2)))
           (signed-byte-p size2 x))
  :enable signed-byte-p
  :short "An N-bit signed is an M-bit signed for any @('M >= N').")

(encapsulate
  ()
  (local (defun my-induct (size1 size2 x)
           (if (or (zp size1)
                   (zp size2))
               (list size1 size2 x)
             (my-induct (- size1 1)
                        (- size2 1)
                        (logcdr x)))))

  (defrule signed-byte-p-when-unsigned-byte-p-smaller
    (implies (and (unsigned-byte-p size1 x)
                  (< size1 (nfix size2)))
             (signed-byte-p size2 x))
    :induct (my-induct size1 size2 x)
    :enable (ihsext-recursive-redefs ihsext-inductions)
    :short "An N-bit unsigned is an M-big signed for any @('M < N')."))


(defsection signed-byte-p-of-loghead
  :short "An N-bit loghead is an M-bit signed for any @('M > N')."

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


(local
 (encapsulate
   ()

   (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (local (in-theory (disable (force))))

   (defthmd truncate-is-floor-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (truncate a b)
                     (floor a b)))
     :hints(("Goal" :in-theory (enable truncate floor))))

   (defthmd rem-is-mod-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (rem a b)
                     (mod a b)))
     :hints(("Goal" :in-theory (enable rem mod truncate-is-floor-when-naturals))))

   (defthm floor-of-zero
     (equal (floor a 0)
            0)
     :hints(("Goal" :in-theory (enable floor))))

   (defthm truncate-of-zero
     (equal (truncate a 0)
            0)
     :hints(("Goal" :in-theory (enable truncate))))

   (defthm mod-of-zero
     (equal (mod a 0)
            (fix a))
     :hints(("Goal" :in-theory (enable mod))))

   (defthm rem-of-zero
     (equal (rem a 0)
            (fix a))
     :hints(("Goal" :in-theory (enable rem))))

   (defthm integerp-of-rem
     (implies (and (integerp a)
                   (integerp b))
              (integerp (rem a b)))
     :hints(("Goal" :in-theory (enable rem))))

   (defthm floor-lower-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= 0 (floor a b)))
     :rule-classes ((:rewrite)
                    (:linear)
                    (:type-prescription :corollary (implies (and (natp a)
                                                                 (natp b))
                                                            (natp (floor a b)))))
     :hints(("Goal" :in-theory (enable floor))))

   (defthm truncate-lower-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= 0 (truncate a b)))
     :rule-classes ((:rewrite)
                    (:linear)
                    (:type-prescription :corollary (implies (and (natp a)
                                                                 (natp b))
                                                            (natp (truncate a b)))))
     :hints(("Goal" :in-theory (enable truncate-is-floor-when-naturals))))

   (defthm mod-lower-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= 0 (mod a b)))
     :rule-classes ((:rewrite)
                    (:linear)
                    (:type-prescription :corollary (implies (and (natp a)
                                                                 (natp b))
                                                            (natp (mod a b))))))

   (defthm rem-lower-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= 0 (rem a b)))
     :rule-classes ((:rewrite)
                    (:linear)
                    (:type-prescription :corollary (implies (and (natp a)
                                                                 (natp b))
                                                            (natp (rem a b)))))
     :hints(("Goal" :in-theory (enable rem-is-mod-when-naturals))))

   (defthm floor-of-1-when-integerp
     (implies (integerp a)
              (equal (floor a 1)
                     a))
     :hints(("Goal" :in-theory (enable floor))))

   (defthm truncate-of-negative-1
     (implies (integerp a)
              (equal (truncate a -1)
                     (- a)))
     :hints(("Goal" :in-theory (enable truncate))))


   (defthmd floor-strong-self-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (< (floor a b) a)
                     (if (posp a)
                         (not (equal b 1))
                       nil)))
     :hints(("Goal" :nonlinearp t)))

   (defthmd truncate-strong-self-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (< (truncate a b) a)
                     (if (posp a)
                         (not (equal b 1))
                       nil)))
     :hints(("Goal" :in-theory (enable truncate-is-floor-when-naturals
                                       floor-strong-self-upper-bound-when-naturals))))

   (defthm floor-weak-self-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= (floor a b) a))
     :hints(("Goal" :cases ((< (floor a b) a))
             :in-theory (e/d (floor-strong-self-upper-bound-when-naturals)
                             (floor)))))

   (defthm truncate-weak-self-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= (truncate a b) a))
     :rule-classes ((:rewrite) (:linear))
     :hints(("Goal" :in-theory (enable truncate-is-floor-when-naturals))))


   (defthm mod-weak-left-upper-bound-when-naturals
     (implies (and (natp a)
                   (posp b))
              (<= (mod a b) a))
     :rule-classes :linear)

   (defthm rem-weak-left-upper-bound-when-naturals
     (implies (and (natp a)
                   (posp b))
              (<= (rem a b) a))
     :rule-classes :linear
     :hints(("Goal" :in-theory (enable rem-is-mod-when-naturals))))

   (defthm mod-strong-right-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (< (mod a b) b)
                     (not (zp b))))
     :rule-classes
     ((:rewrite)
      (:linear :corollary (implies (and (natp a)
                                        (posp b))
                                   (< (mod a b) b)))))

   (defthm rem-strong-right-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (equal (< (rem a b) b)
                     (not (zp b))))
     :rule-classes
     ((:rewrite)
      (:linear :corollary (implies (and (natp a)
                                        (posp b))
                                   (< (rem a b) b))))
     :hints(("Goal" :in-theory (enable rem-is-mod-when-naturals))))

   (defthm mod-weak-global-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= (mod a b) (max a b)))
     :rule-classes :linear
     :hints(("Goal"
             :use ((:instance mod-weak-left-upper-bound-when-naturals)
                   (:instance mod-strong-right-upper-bound-when-naturals)))))

   (defthm rem-weak-global-upper-bound-when-naturals
     (implies (and (natp a)
                   (natp b))
              (<= (rem a b) (max a b)))
     :rule-classes :linear
     :hints(("Goal" :in-theory (enable rem-is-mod-when-naturals))))))


(defrule basic-unsigned-byte-p-of-floor
  (implies (and (unsigned-byte-p n a)
                (natp b))
           (unsigned-byte-p n (floor a b)))
  :enable (unsigned-byte-p)
  :disable (floor-weak-self-upper-bound-when-naturals)
  :use ((:instance floor-weak-self-upper-bound-when-naturals))
  :short "Floor an N-bit unsigned by a natural creates an N-bit unsigned.")

(defrule basic-unsigned-byte-p-of-truncate
  (implies (and (unsigned-byte-p n a)
                (natp b))
           (unsigned-byte-p n (truncate a b)))
  :enable (truncate-is-floor-when-naturals)
  :disable (floor truncate unsigned-byte-p)
  :short "Truncate an N-bit unsigned by a natural creates an N-bit unsigned.")

(defrule basic-unsigned-byte-p-of-mod
  (implies (and (unsigned-byte-p n a)
                (natp b))
           (unsigned-byte-p n (mod a b)))
  :do-not-induct t
  :use ((:instance mod-weak-left-upper-bound-when-naturals))
  :enable (unsigned-byte-p)
  :disable (mod-weak-left-upper-bound-when-naturals
            mod-weak-global-upper-bound-when-naturals)
  :short "Mod an N-bit unsigned by a natural creates an N-bit unsigned.")

(defrule basic-unsigned-byte-p-of-rem
  (implies (and (unsigned-byte-p n a)
                (natp b))
           (unsigned-byte-p n (rem a b)))
  :enable (rem-is-mod-when-naturals)
  :disable (rem mod unsigned-byte-p)
  :short "Remainder of an N-bit unsigned by a natural creates an N-bit unsigned.")



(defsection basic-signed-byte-p-of-truncate
  :autodoc nil

; Unfortunately the asymmetry of signed-byte-p makes the signed-byte-p
; lemmas for truncate and floor ugly.
;
; You might normally think of division as decreasing the magnitude of the
; numerator.  But there is a bad case.  If we divide the minimum n-bit signed
; integer by -1, the asymmetry of 2's complement arithmetic means we get a
; result that is too large to represent.  For example, for N=32:
;
;   (defconst *int-min* (- (expt 2 31)))
;   (signed-byte-p 32 *int-min*)               ;; T
;   (signed-byte-p 32 (truncate *int-min* -1)) ;; NIL(!) -- it's 2^31
;   (signed-byte-p 32 (floor *int-min* -1))    ;; NIL -- 2^31
;
; As a result, our final theorems have to rule out this one special case.  The
; proof is a bit long/involved, but is essentially very simple and just boils
; down to cases about whether the numerator/denominator are positive/negative.

  (local (in-theory (enable signed-byte-p)))

  (local (defthm |(< (- a) (- b))|
           (implies (and (rationalp a)
                         (rationalp b))
                    (equal (< (- a) (- b))
                           (< b a)))
           :hints(("Goal" :use ((:instance acl2::<-*-right-cancel
                                 (x a) (y b) (z -1)))))))

  ;; Case 1 (positive/positive):

  (local (defthm basic-signed-byte-p-of-floor-when-naturals
           (implies (and (signed-byte-p n a)
                         (case-split (natp a))
                         (case-split (natp b)))
                    (signed-byte-p n (floor a b)))
           :hints(("Goal"
                   :in-theory (disable basic-unsigned-byte-p-of-floor)
                   :use ((:instance basic-unsigned-byte-p-of-floor
                          (n (- n 1))))))))

  (local (defthm basic-signed-byte-p-of-truncate-when-naturals
           (implies (and (signed-byte-p n a)
                         (case-split (natp a))
                         (case-split (natp b)))
                    (signed-byte-p n (truncate a b)))
           :hints(("Goal"
                   :use ((:instance truncate-is-floor-when-naturals)
                         (:instance basic-signed-byte-p-of-floor-when-naturals))))))

  ;; Case 2 (positive/negative):

  (local
   (encapsulate ()

     (local (defthm truncate-when-positive-over-negative
              (implies (and (natp a)
                            (negp b))
                       (equal (truncate a b)
                              (- (truncate a (- b)))))
              :hints(("Goal" :in-theory (enable truncate)))))

     (defthm basic-signed-byte-p-of-truncate-when-positive-over-negative
       (implies (and (signed-byte-p n a)
                     (case-split (natp a))
                     (case-split (negp b)))
                (signed-byte-p n (truncate a b))))

     (local (defthm floor-when-positive-over-negative
              (implies (and (natp a)
                            (negp b))
                       (equal (floor a b)
                              (if (integerp (/ a b))
                                  (- (floor a (- b)))
                                (+ -1 (- (floor a (- b)))))))
              :hints(("Goal" :in-theory (enable floor)))))

     (defthm basic-signed-byte-p-of-floor-when-positive-over-negative
       (implies (and (signed-byte-p n a)
                     (case-split (natp a))
                     (case-split (negp b)))
                (signed-byte-p n (floor a b)))
       :hints(("Goal"
               :do-not-induct t
               :use ((:instance basic-signed-byte-p-of-floor-when-naturals
                      (a a) (b (- b)) (n n)))
               :in-theory (disable basic-signed-byte-p-of-floor-when-naturals))))))

  ;; Case 3 (negative/positive):

  (local
   (encapsulate ()

     (local (defthm truncate-when-negative-over-positive
              (implies (and (negp a)
                            (natp b))
                       (equal (truncate a b)
                              (- (truncate (- a) b))))
              :hints(("Goal" :in-theory (enable truncate)))))

     (defthm basic-signed-byte-p-of-truncate-when-negative-over-positive
       (implies (and (signed-byte-p n a)
                     (case-split (negp a))
                     (case-split (posp b)))
                (signed-byte-p n (truncate a b))))

     (local (defthm floor-when-negative-over-positive
              (implies (and (negp a)
                            (natp b))
                       (equal (floor a b)
                              (if (integerp (/ a b))
                                  (- (floor (- a) b))
                                (+ -1 (- (floor (- a) b))))))
              :hints(("Goal" :in-theory (enable floor)))))

     ;; This is harder than the positive/negative case, because in the special
     ;; case that A is the minimum signed-byte-p, the theorem about floor for
     ;; positive arguments doesn't help us, because -a becomes too large.  For
     ;; this case, we need to also appeal to our strong self-bound theorem.

     (defthm basic-signed-byte-p-of-floor-when-negative-over-positive
       (implies (and (signed-byte-p n a)
                     (case-split (negp a))
                     (case-split (posp b)))
                (signed-byte-p n (floor a b)))
       :hints(("Goal"
               :use ((:instance basic-signed-byte-p-of-floor-when-naturals
                      (a (- a)) (b b) (n n))
                     (:instance floor-strong-self-upper-bound-when-naturals
                      (a (expt 2 (+ -1 n))) (b b)))
               :in-theory (disable basic-signed-byte-p-of-floor-when-naturals
                                   floor-strong-self-upper-bound-when-naturals))))))




  ;; Case 4 (negative/negative -- the tricky case):

  (local
   (encapsulate ()

     (local (defthm truncate-when-both-negative
              (implies (and (negp a)
                            (negp b))
                       (equal (truncate a b)
                              (truncate (- a) (- b))))
              :hints(("Goal" :in-theory (enable truncate)))))

     (local (defthmd basic-signed-byte-p-of-truncate-when-negatives-except-for-int-min
              (implies (and (signed-byte-p n a)
                            (negp a)
                            (negp b)
                            (not (equal a (- (expt 2 (- n 1))))))
                       (signed-byte-p n (truncate a b)))))

     (local (defthmd basic-signed-byte-p-of-truncate-int-min
              (implies (and (signed-byte-p n a)
                            (equal a (- (expt 2 (- n 1))))
                            (negp b)
                            (not (equal b -1)))
                       (signed-byte-p n (truncate a b)))
              :hints(("Goal" :in-theory (enable truncate-strong-self-upper-bound-when-naturals)))))

     (defthm basic-signed-byte-p-of-truncate-when-negatives
       (implies (and (signed-byte-p n a)
                     (case-split (negp a))
                     (case-split (negp b)))
                (equal (signed-byte-p n (truncate a b))
                       (not (and (equal a (- (expt 2 (- n 1))))
                                 (equal b -1)))))
       :hints(("Goal"
               :do-not-induct t
               :use ((:instance basic-signed-byte-p-of-truncate-when-negatives-except-for-int-min)
                     (:instance basic-signed-byte-p-of-truncate-int-min))
               :in-theory (enable truncate-strong-self-upper-bound-when-naturals))))

     (local (defthm floor-when-both-negative
              (implies (and (negp a)
                            (negp b))
                       (equal (floor a b)
                              (floor (- a) (- b))))
              :hints(("Goal" :in-theory (enable floor)))))

     (local (defthmd basic-signed-byte-p-of-floor-when-negatives-except-for-int-min
              (implies (and (signed-byte-p n a)
                            (negp a)
                            (negp b)
                            (not (equal a (- (expt 2 (- n 1))))))
                       (signed-byte-p n (floor a b)))
              :hints(("Goal"
                      :use ((:instance basic-signed-byte-p-of-floor-when-naturals
                             (a (- a)) (b (- b))))))))

     (local (defthmd basic-signed-byte-p-of-floor-int-min
              (implies (and (signed-byte-p n a)
                            (equal a (- (expt 2 (- n 1))))
                            (negp b)
                            (not (equal b -1)))
                       (signed-byte-p n (floor a b)))
              :hints(("Goal" :in-theory (enable floor-strong-self-upper-bound-when-naturals)))))

     (defthm basic-signed-byte-p-of-floor-when-negatives
       (implies (and (signed-byte-p n a)
                     (case-split (negp a))
                     (case-split (negp b)))
                (equal (signed-byte-p n (floor a b))
                       (not (and (equal a (- (expt 2 (- n 1))))
                                 (equal b -1)))))
       :hints(("Goal"
               :do-not-induct t
               :use ((:instance basic-signed-byte-p-of-floor-when-negatives-except-for-int-min)
                     (:instance basic-signed-byte-p-of-floor-int-min))
               :in-theory (enable floor-strong-self-upper-bound-when-naturals))))))


  ;; Wrapping it all up into a coherent top-level theorem:

  (defruled basic-signed-byte-p-of-truncate-split
    (implies (and (signed-byte-p n a)
                  (integerp b))
             (equal (signed-byte-p n (truncate a b))
                    (not (and (equal a (- (expt 2 (- n 1))))
                              (equal b -1)))))
    :hints(("Goal"
            :in-theory (disable signed-byte-p)
            :do-not '(generalize fertilize eliminate-destructors)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable signed-byte-p))))
    :short "Truncate of an N-bit signed by an integer is <b>usually</b> an
            N-bit signed.  (Strong form, case splitting, disabled by default)."
    :long "<p>See also @(see basic-signed-byte-p-of-truncate), which we leave
           enabled.</p>")

  (defrule basic-signed-byte-p-of-truncate
    (implies (and (signed-byte-p n a)
                  (integerp b)
                  (not (and (equal a (- (expt 2 (- n 1))))
                            (equal b -1))))
             (signed-byte-p n (truncate a b)))
    :enable basic-signed-byte-p-of-truncate-split
    :short "Truncating an N-bit signed by an integer is <b>usually</b> an N-bit
            signed.  (Weak form, enabled by default)."
    :long "<p>See also @(see basic-signed-byte-p-of-truncate-split).</p>")

  (defrule basic-signed-byte-p-of-floor-split
    (implies (and (signed-byte-p n a)
                  (integerp b))
             (equal (signed-byte-p n (floor a b))
                    (not (and (equal a (- (expt 2 (- n 1))))
                              (equal b -1)))))
    :hints(("Goal"
            :in-theory (disable signed-byte-p)
            :do-not '(generalize fertilize eliminate-destructors)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable signed-byte-p))))
    :short "Floor of an N-bit signed by an integer is <b>usually</b> an N-bit
            signed.  (Strong form, case splitting, disabled by default)."
    :long "<p>See also @(see basic-signed-byte-p-of-floor).</p>")

  (defrule basic-signed-byte-p-of-floor
    (implies (and (signed-byte-p n a)
                  (integerp b)
                  (not (and (equal a (- (expt 2 (- n 1))))
                            (equal b -1))))
             (signed-byte-p n (floor a b)))
    :enable basic-signed-byte-p-of-floor-split
    :short "Floor of an N-bit signed by an integer is <b>usually</b> an N-bit
            signed.  (Weak form, enabled by default)."
    :long "<p>See also @(see basic-signed-byte-p-of-floor-split).</p>"))

(defsection basic-signed-byte-p-of-mod
  :autodoc nil

  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (local (in-theory (enable signed-byte-p)))

  (local (defthm basic-signed-byte-p-of-mod-when-negp-b
           ;; When B is negative, MOD-BOUNDED-BY-MODULUS tells us that the mod
           ;; is greater than B, so signed-byte-p of B suffices.
           (implies (and (integerp a)
                         (signed-byte-p n b)
                         (case-split (negp b)))
                    (signed-byte-p n (mod a b)))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize eliminate-destructors)
                   :in-theory (e/d ()
                                   (mod floor))
                   ))))

  (local (defthm basic-signed-byte-p-of-mod-when-posp-b
           ;; When B is positive, MOD-BOUNDED-BY-MODULUS tells us that the mod
           ;; is less than B, so signed-byte-p of B suffices.
           (implies (and (integerp a)
                         (signed-byte-p n b)
                         (case-split (posp b)))
                    (signed-byte-p n (mod a b)))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize eliminate-destructors)
                   :in-theory (e/d ()
                                   (mod floor))
                   ))))

  ;; That leaves only the case where B is zero.  In that case MOD-OF-ZERO shows
  ;; us that the mod is A.  So in this case we need that A is a signed-byte-p.

  (defrule basic-signed-byte-p-of-mod
    (implies (and (signed-byte-p n a)
                  (signed-byte-p n b))
             (signed-byte-p n (mod a b)))
    :short "Mod of N-bit signed by N-bit signed creates an N-bit signed.")

  ;; Same argument now for REM.

  (local (defthm basic-signed-byte-p-of-rem-when-negp-b
           (implies (and (integerp a)
                         (signed-byte-p n b)
                         (case-split (negp b)))
                    (signed-byte-p n (rem a b)))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize eliminate-destructors)
                   :in-theory (e/d ()
                                   (rem truncate))
                   ))))

  (local (defthm basic-signed-byte-p-of-rem-when-posp-b
           (implies (and (integerp a)
                         (signed-byte-p n b)
                         (case-split (posp b)))
                    (signed-byte-p n (rem a b)))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize eliminate-destructors)
                   :in-theory (e/d ()
                                   (rem truncate))
                   ))))

  (defrule basic-signed-byte-p-of-rem
    (implies (and (signed-byte-p n a)
                  (signed-byte-p n b))
             (signed-byte-p n (rem a b)))
    :short "Rem of N-bit signed by N-bit signed creates an N-bit signed."))

