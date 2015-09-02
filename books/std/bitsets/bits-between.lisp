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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITSETS")
(include-book "std/util/define" :dir :system)
(include-book "std/osets/top" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (in-theory (acl2::enable* acl2::arith-equiv-forwarding)))

(local (xdoc::set-default-parents utilities))

(define add-to-each ((offset integerp)
                     (x      integer-listp))
  :short "Add an offset to each member of a list."
  :long "<p>This is used in the development of @(see bitset-members).</p>"
  (if (atom x)
      nil
    (cons (+ offset (car x))
          (add-to-each offset (cdr x))))
  ///
  (defthm add-to-each-when-atom
    (implies (atom x)
             (equal (add-to-each offset x)
                    nil)))

  (defthm add-to-each-of-cons
    (equal (add-to-each offset (cons a x))
           (cons (+ offset a) (add-to-each offset x))))

  (defthm add-to-each-of-zero
    (implies (integer-listp x)
             (equal (add-to-each 0 x)
                    x)))

  (defthm add-to-each-of-append
    (equal (add-to-each offset (append x y))
           (append (add-to-each offset x)
                   (add-to-each offset y))))

  (local (defthm rev-of-add-to-each
           (equal (rev (add-to-each offset x))
                  (add-to-each offset (rev x)))))

  (defthm add-to-each-of-add-to-each
    (equal (add-to-each a (add-to-each b x))
           (add-to-each (+ a b) x))))



(define bits-between ((n natp "lower bound, inclusive")
                      (m natp "upper bound, exclusive")
                      (x integerp "integer to extract bits from"))
  :guard (<= n m)
  :returns set-of-bits
  :short "@(call bits-between) returns a proper, ordered set of all @('i') in
@('[n, m)') such that @('(logbitp i x)')."
  :long "<p>This is a key function in the definition of @(see
bitset-members).</p>"
  :measure (nfix (- (nfix m) (nfix n)))
  (let* ((n (lnfix n))
         (m (lnfix m)))
    (cond ((mbe :logic (zp (- m n))
                :exec (= m n))
           nil)
          ((logbitp n x)
           (cons n (bits-between (+ n 1) m x)))
          (t
           (bits-between (+ n 1) m x))))
  ///
  (defthm true-listp-of-bits-between
    (true-listp (bits-between n m x))
    :rule-classes :type-prescription)

  (defthm integer-listp-of-bits-between
    (integer-listp (bits-between n m x)))

  (defthm nat-listp-of-bits-between
    (nat-listp (bits-between n m x)))

  (defthm bits-between-when-not-integer
    (implies (not (integerp x))
             (equal (bits-between n m x)
                    nil)))

  (defthm member-equal-of-bits-between
    (iff (member-equal a (bits-between n m x))
         (and (natp a)
              (<= (nfix n) a)
              (< a (nfix m))
              (logbitp a x)))
    :hints(("Goal" :induct (bits-between n m x))))

  (defthm no-duplicatesp-equal-of-bits-between
    (no-duplicatesp-equal (bits-between n m x)))

  (defthmd bits-between-of-increment-right-index
    (implies (and (force (natp n))
                  (force (natp m))
                  (force (<= n m)))
             (equal (bits-between n (+ 1 m) x)
                    (if (logbitp m x)
                        (append (bits-between n m x)
                                (list m))
                      (bits-between n m x))))
    :hints(("Goal" :induct (bits-between n m x))))

  (defthm merge-appended-bits-between
    (implies (and (natp n)
                  (natp m)
                  (natp k)
                  (<= n m)
                  (<= m k))
             (equal (append (bits-between n m x)
                            (bits-between m k x))
                    (bits-between n k x)))
    :hints(("Goal" :induct (bits-between n m x))))

  (encapsulate
    ()
    (local (defun my-induct (n m)
             (declare (xargs :measure (nfix (- (nfix m) (nfix n)))
                             :hints(("Goal" :in-theory (enable nfix)))))
             (if (zp (- (nfix m) (nfix n)))
                 nil
               (my-induct (+ (nfix n) 1) m))))

    (local (include-book "arithmetic/top-with-meta" :dir :system))

    (defthm bits-between-of-right-shift
      (implies (and (natp n)
                    (natp m)
                    (<= n m)
                    (integerp k)
                    (< k 0))
               (equal (bits-between n m (ash x k))
                      (add-to-each k (bits-between (- n k) (- m k) x))))
      :hints(("Goal"
              :expand ((bits-between n m (ash x k))
                       (bits-between (+ (- k) n) (+ (- k) m) x))
              :induct (my-induct n m)))))

  (defthm bits-between-of-mod-2^n
    (implies (and (integerp x)
                  (natp k)
                  (<= m k))
             (equal (bits-between n m (mod x (expt 2 k)))
                    (bits-between n m x)))
    :hints(("Goal"
            :induct (bits-between n m x)
            :in-theory (e/d (bits-between nfix)))))

  (make-event
   ;; Stupid copy of the above to avoid problems unifying with (expt 2 k)
   `(defthm bits-between-of-mod-2^32
      (implies (and (integerp x)
                    (<= m 32))
               (equal (bits-between n m (mod x ,(expt 2 32)))
                      (bits-between n m x)))
      :hints(("Goal"
              :use ((:instance bits-between-of-mod-2^n (k 32)))))))

  (encapsulate
    ()
    ;; (local (in-theory (disable
    ;;                    expt-is-increasing-for-base->-1
    ;;                    expt-is-weakly-increasing-for-base->-1
    ;;                    expt->-1-one
    ;;                    expt-type-prescription-positive-base
    ;;                    expt-type-prescription-integerp-base
    ;;                    expt-type-prescription-nonnegative-base
    ;;                    expt-type-prescription-rationalp-base
    ;;                    expt-type-prescription-nonpositive-base-odd-exponent)))

    (local (defthm l0
             (implies (and (natp n)
                           (natp x)
                           (<= (integer-length x) n))
                      (not (bits-between n m x)))))

    (defthm bits-between-upper
      (implies (and (syntaxp (not (equal m `(integer-length ,x))))
                    (natp n)
                    (natp m)
                    (natp x)
                    (<= (integer-length x) m))
               (equal (bits-between n m x)
                      (bits-between n (integer-length x) x)))
      :hints(("Goal" :induct (bits-between n m x)))))

  (encapsulate
    ()
    ;; (local (in-theory (disable
    ;;                    expt-is-increasing-for-base->-1
    ;;                    |(expt x (if a b c))|
    ;;                    expt-is-weakly-increasing-for-base->-1
    ;;                    expt->-1-one)))
    (local (defthm l0
             (implies (and (natp a)
                           (natp b))
                      (equal (set::<< a b)
                             (< a b)))
             :hints(("Goal" :in-theory (enable set::<< lexorder alphorder)))))

    (local (defthm l1
             (equal (natp (car (bits-between n m x)))
                    (if (bits-between n m x)
                        t
                      nil))))

    (local (defthm l2
             (implies (bits-between n m x)
                      (<= (nfix n) (car (bits-between n m x))))
             :rule-classes ((:linear))))

    (defthm setp-of-bits-between
      (set::setp (bits-between n m x))
      :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules))))))

  (encapsulate
    ()
    (local (defthmd sets-membership-hack
             (implies (and (set::setp x)
                           (syntaxp (not (quotep x))))
                      (iff (member-equal a x)
                           (set::in a x)))
             :hints(("Goal" :in-theory (enable set::in-to-member)))))

    (defthm in-of-bits-between
      (equal (set::in a (bits-between n m x))
             (and (natp a)
                  (<= (nfix n) a)
                  (< a (nfix m))
                  (logbitp a x)))
      :hints(("Goal" :use ((:instance sets-membership-hack
                                      (a a)
                                      (x (bits-between n m x)))))))))



(local (defthm rassoc-append
         (equal (append x (append y z))
                (append (append x y) z))))


(local (defthm append-of-add-to-each
         (equal (append (add-to-each a x)
                        (add-to-each a y))
                (add-to-each a (append x y)))))

(local (in-theory (disable add-to-each-of-append)))

(local (theory-invariant (incompatible (:rewrite append-of-add-to-each)
                                       (:rewrite add-to-each-of-append))))

(local (deftheory slow-rules
         '(acl2::true-listp-append
           bits-between-upper
           ; reduce-integerp-+
           ; integerp-minus-x
           append
           not
           set::double-containment
           ; normalize-terms-such-as-a/a+b-+-b/a+b
           ; normalize-addends
           acl2::default-+-1
           acl2::default-+-2
           acl2::default-car
           acl2::default-cdr
           bitops::normalize-logbitp-when-mods-equal
           (:t acl2::logcar-type)
           (:t acl2::logcar)
           (:t logbitp)
           (:t binary-append))))

(local (in-theory (disable slow-rules)))

(define bits-0-7 ((offset :type unsigned-byte)
                  (x      :type (unsigned-byte 32))
                  (acc))
  :short "Inner loop for @(see bits-0-31)."
  (b* ((acc (if (logbitp 7 x) (cons (+ 7 offset) acc) acc))
       (acc (if (logbitp 6 x) (cons (+ 6 offset) acc) acc))
       (acc (if (logbitp 5 x) (cons (+ 5 offset) acc) acc))
       (acc (if (logbitp 4 x) (cons (+ 4 offset) acc) acc))
       (acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
       (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
       (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
       (acc (if (logbitp 0 x) (cons offset acc)       acc)))
    acc)
  ///
  (with-output
   :gag-mode :goals
   (defthm bits-0-7-redef
     (implies (force (natp offset))
              (equal (bits-0-7 offset x acc)
                     (append (add-to-each offset (bits-between 0 8 x))
                             acc)))
     :hints(("Goal"
             :in-theory (enable bits-0-7
                                bits-between
                                bits-between-of-increment-right-index)
             :expand ((:free (a b c) (append (cons a b) c))
                      (:free (c) (append nil c))))))))

(define bits-0-31 ((offset :type unsigned-byte)
                   (x      :type (unsigned-byte 32))
                   (acc))
 "Partially unrolled version of @(see bits-between) that collects the
bits from a 32-bit unsigned @('x') and adds @('offset') to each."

  :long "<p>This is about 2.8x faster than @(see bits-between), according to
the following loops (on fv-1):</p>

@({
 (progn
  (gc$)
  ;; 25.759 seconds
  (time (loop for x fixnum from 1 to 50000000 do
              (bits-between 0 32 x)))
  ;; 8.935 seconds
  (gc$)
  (time (loop for x fixnum from 1 to 50000000 do
              (bits-0-31 0 x nil))))
})

<p>The inner loop is unrolled 8 times.  Unrolling 16 times was a slightly
better, but the case explosion in the equivalence proof ended up causing ACL2 a
lot of problems.  Maybe a better rewriting strategy would solve this, but just
opening the functions is fine for 8 unrolls and it still gives us most of the
benefit.</p>"

  (b* (((when (eql x 0))
        ;; Maybe an optimization when dealing with sparse data
        acc)
       (acc (bits-0-7 (+ offset 24) (the (unsigned-byte 32) (ash x -24)) acc))
       (acc (bits-0-7 (+ offset 16) (the (unsigned-byte 32) (ash x -16)) acc))
       (acc (bits-0-7 (+ offset 8)  (the (unsigned-byte 32) (ash x -8)) acc)))
    (bits-0-7 offset x acc))

  ///
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm bits-0-31-redef
    (implies (natp offset)
             (equal (bits-0-31 offset x acc)
                    (append (add-to-each offset (bits-between 0 32 x))
                            acc)))
    :hints(("Goal" :in-theory (e/d (bits-0-31 append)
                                   (acl2::right-shift-to-logtail))))))



(define 60bits-0-7 ((offset :type unsigned-byte)
                    (x      :type (unsigned-byte 60))
                    (acc))
  :short "Identical to @(see bits-0-7), but for 60-bit unsigned ints."
  (b* ((acc (if (logbitp 7 x) (cons (+ 7 offset) acc) acc))
       (acc (if (logbitp 6 x) (cons (+ 6 offset) acc) acc))
       (acc (if (logbitp 5 x) (cons (+ 5 offset) acc) acc))
       (acc (if (logbitp 4 x) (cons (+ 4 offset) acc) acc))
       (acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
       (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
       (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
       (acc (if (logbitp 0 x) (cons offset acc)       acc)))
    acc)
  ///
  (with-output
   :gag-mode :goals
   (defthm 60bits-0-7-redef
     (implies (force (natp offset))
              (equal (60bits-0-7 offset x acc)
                     (append (add-to-each offset (bits-between 0 8 x))
                             acc)))
     :hints(("Goal"
             :in-theory (enable 60bits-0-7
                                bits-between
                                bits-between-of-increment-right-index)
             :expand ((:free (a b c) (append (cons a b) c))
                      (:free (c) (append nil c))))))))

(define 60bits-0-3 ((offset :type unsigned-byte)
                    (x      :type (unsigned-byte 60))
                    acc)
  :short "Like @(see bits-0-7), but since 8 doesn't divide 60, we have
 this goofy function for the final bits."
  (b* ((acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
       (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
       (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
       (acc (if (logbitp 0 x) (cons offset acc)       acc)))
    acc)
  ///
  (with-output
   :gag-mode :goals
   (defthm 60bits-0-3-redef
     (implies (force (natp offset))
              (equal (60bits-0-3 offset x acc)
                     (append (add-to-each offset (bits-between 0 4 x))
                             acc)))
     :hints(("Goal"
             :in-theory (e/d (60bits-0-3
                              bits-between
                              bits-between-of-increment-right-index))
             :expand ((:free (a b c) (append (cons a b) c))
                      (:free (c) (append nil c))))))))

(define 60bits-0-59 ((offset :type unsigned-byte)
                     (x      :type (unsigned-byte 60))
                     acc)
  :short "Partially unrolled version of @(see bits-between) that collects the
bits from a 60-bit unsigned @('x') and adds @('offset') to each."

  :long "<p>In CCL, 60-bit unsigned numbers are fixnums and, according to the
following loops, this is about 3.6x faster than @(see bits-between).</p>

@({
 (progn
  (gc$)
  ;; 21.540 seconds
  (time (loop for x fixnum from 1 to 30000000 do
              (bits-between 0 60 x)))
  ;; 6.013 seconds
  (gc$)
  (time (loop for x fixnum from 1 to 30000000 do
              (60bits-0-59 0 x nil))))
})"

  ;; We could do a check against zero like in bits-0-31, but since this is
  ;; used in sparse bitsets where the data should never be zero, we think
  ;; that wouldn't be good.
  (b* ((acc (60bits-0-3 (+ offset 56) (the (unsigned-byte 60) (ash x -56)) acc))
       (acc (60bits-0-7 (+ offset 48) (the (unsigned-byte 60) (ash x -48)) acc))
       (acc (60bits-0-7 (+ offset 40) (the (unsigned-byte 60) (ash x -40)) acc))
       (acc (60bits-0-7 (+ offset 32) (the (unsigned-byte 60) (ash x -32)) acc))
       (acc (60bits-0-7 (+ offset 24) (the (unsigned-byte 60) (ash x -24)) acc))
       (acc (60bits-0-7 (+ offset 16) (the (unsigned-byte 60) (ash x -16)) acc))
       (acc (60bits-0-7 (+ offset 8)  (the (unsigned-byte 60) (ash x -8)) acc)))
    (60bits-0-7 offset x acc))

  ///

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm 60bits-0-59-redef
    (implies (natp offset)
             (equal (60bits-0-59 offset x acc)
                    (append (add-to-each offset (bits-between 0 60 x))
                            acc)))
    :hints(("Goal" :in-theory (e/d (60bits-0-59 append)
                                   (acl2::right-shift-to-logtail))))))

