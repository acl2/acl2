; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "cutil/defsection" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(local (include-book "ihs-extensions"))
(local (include-book "unicode/rev" :dir :system))
(local (include-book "unicode/append" :dir :system))
; (local (include-book "arithmetic-3/extra/top-ext" :dir :system))

(local (in-theory (enable* arith-equiv-forwarding)))

(defsection add-to-each
  :parents (bitops)
  :short "@(call add-to-each) adds @('offset') to each member of @('x')."

  :long "<p>This is used in the development of @(see bitset-members).</p>"

  (defund add-to-each (offset x)
    (declare (xargs :guard (and (integerp offset)
                                (integer-listp x))))
    (if (atom x)
        nil
      (cons (+ offset (car x))
            (add-to-each offset (cdr x)))))

  (defthm add-to-each-when-atom
    (implies (atom x)
             (equal (add-to-each offset x)
                    nil))
    :hints(("Goal" :in-theory (enable add-to-each))))

  (defthm add-to-each-of-cons
    (equal (add-to-each offset (cons a x))
           (cons (+ offset a) (add-to-each offset x)))
    :hints(("Goal" :in-theory (enable add-to-each))))

  (defthm add-to-each-of-zero
    (implies (integer-listp x)
             (equal (add-to-each 0 x)
                    x))
    :hints(("Goal" :induct (len x))))

  (defthm add-to-each-of-append
    (equal (add-to-each offset (append x y))
           (append (add-to-each offset x)
                   (add-to-each offset y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm rev-of-add-to-each
           (equal (rev (add-to-each offset x))
                  (add-to-each offset (rev x)))
           :hints(("Goal" :induct (len x)))))

  (defthm add-to-each-of-add-to-each
    (equal (add-to-each a (add-to-each b x))
           (add-to-each (+ a b) x))
    :hints(("goal" :induct (len x)))))



(defsection bits-between
  :parents (bitops)
  :short "@(call bits-between) returns a proper, ordered set of all @('i') in
@('[n, m)') such that @('(@(see logbitp) i x)')."

  :long "<p>This is a key function in the definition of @(see
bitset-members).</p>"

  (defund bits-between (n m x)
    (declare (xargs :guard (and (natp n)
                                (natp m)
                                (<= n m)
                                (integerp x))
                    :hints(("Goal" :in-theory (enable nfix)))
                    :measure (nfix (- (nfix m) (nfix n)))))
    (let* ((n (lnfix n))
           (m (lnfix m)))
      (cond ((mbe :logic (zp (- m n))
                  :exec (= m n))
             nil)
            ((logbitp n x)
             (cons n (bits-between (+ n 1) m x)))
            (t
             (bits-between (+ n 1) m x)))))

  (defthm true-listp-of-bits-between
    (true-listp (bits-between n m x))
    :rule-classes :type-prescription)

  (defthm integer-listp-of-bits-between
    (integer-listp (bits-between n m x))
    :hints(("Goal" :in-theory (enable bits-between))))

  (defthm bits-between-when-not-integer
    (implies (not (integerp x))
             (equal (bits-between n m x)
                    nil))
    :hints(("Goal" :in-theory (enable bits-between))))

  (defthm member-equal-of-bits-between
    (iff (member-equal a (bits-between n m x))
         (and (natp a)
              (<= (nfix n) a)
              (< a (nfix m))
              (logbitp a x)))
    :hints(("Goal"
            :in-theory (enable bits-between)
            :induct (bits-between n m x))))

  (defthm no-duplicatesp-equal-of-bits-between
    (no-duplicatesp-equal (bits-between n m x))
    :hints(("Goal" :in-theory (enable bits-between))))

  (defthmd bits-between-of-increment-right-index
    (implies (and (force (natp n))
                  (force (natp m))
                  (force (<= n m)))
             (equal (bits-between n (+ 1 m) x)
                    (if (logbitp m x)
                        (append (bits-between n m x)
                                (list m))
                      (bits-between n m x))))
    :hints(("Goal"
            :in-theory (enable bits-between)
            :induct (bits-between n m x))))

  (defthm merge-appended-bits-between
    (implies (and (natp n)
                  (natp m)
                  (natp k)
                  (<= n m)
                  (<= m k))
             (equal (append (bits-between n m x)
                            (bits-between m k x))
                    (bits-between n k x)))
    :hints(("Goal"
            :in-theory (enable bits-between)
            :induct (bits-between n m x))))

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
              :in-theory (enable bits-between)
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
                      (not (bits-between n m x)))
             :hints(("Goal" :in-theory (enable bits-between)))))

    (defthm bits-between-upper
      (implies (and (syntaxp (not (equal m `(integer-length ,x))))
                    (natp n)
                    (natp m)
                    (natp x)
                    (<= (integer-length x) m))
               (equal (bits-between n m x)
                      (bits-between n (integer-length x) x)))
      :hints(("Goal"
              :do-not '(generalize fertilize eliminate-destructors)
              :in-theory (e/d (bits-between))
              :induct (bits-between n m x)))))

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
                      (equal (sets::<< a b)
                             (< a b)))
             :hints(("Goal" :in-theory (enable sets::<< lexorder alphorder)))))

    (local (defthm l1
             (equal (natp (car (bits-between n m x)))
                    (if (bits-between n m x)
                        t
                      nil))
             :hints(("Goal" :in-theory (enable bits-between)))))

    (local (defthm l2
             (implies (bits-between n m x)
                      (<= (nfix n) (car (bits-between n m x))))
             :rule-classes ((:linear))
             :hints(("Goal" :in-theory (enable bits-between)))))

    (defthm setp-of-bits-between
      (sets::setp (bits-between n m x))
      :hints(("Goal" :in-theory (enable* bits-between
                                         (:ruleset sets::primitive-rules))))))

  (encapsulate
    ()
    (local (defthmd sets-membership-hack
             (implies (and (sets::setp x)
                           (syntaxp (not (quotep x))))
                      (iff (member-equal a x)
                           (sets::in a x)))
             :hints(("Goal"
                     :in-theory (enable sets::in-to-member)))))

    (defthm in-of-bits-between
      (equal (sets::in a (bits-between n m x))
             (and (natp a)
                  (<= (nfix n) a)
                  (< a (nfix m))
                  (logbitp a x)))
      :hints(("Goal"
              :use ((:instance sets-membership-hack
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
         '(true-listp-append
           bits-between-upper
           ; reduce-integerp-+
           ; integerp-minus-x
           append not
           sets::double-containment
           ; normalize-terms-such-as-a/a+b-+-b/a+b
           ; normalize-addends
           default-+-1 default-+-2
           default-car default-cdr
           normalize-logbitp-when-mods-equal
           (:type-prescription logcar-type)
           (:type-prescription logcar)
           (:type-prescription logbitp)
           (:type-prescription binary-append))))

(defsection bits-0-31
  :parents (bits-between)
  :short "Partially unrolled version of @(see bits-between) that collects the
bits from a 32-bit unsigned @('x') and adds @('offset') to each."

  :long "<p>This is about 2.8x faster than bits-between, according to the
following loops (on fv-1):</p>

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

  (local (in-theory (disable slow-rules)))

  (defund bits-0-7 (offset x acc)
    (declare (xargs :guard (natp offset))
             (type (unsigned-byte 32) x))
    (b* ((acc (if (logbitp 7 x) (cons (+ 7 offset) acc) acc))
         (acc (if (logbitp 6 x) (cons (+ 6 offset) acc) acc))
         (acc (if (logbitp 5 x) (cons (+ 5 offset) acc) acc))
         (acc (if (logbitp 4 x) (cons (+ 4 offset) acc) acc))
         (acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
         (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
         (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
         (acc (if (logbitp 0 x) (cons offset acc)       acc)))
      acc))

  (defund bits-0-31 (offset x acc)
    (declare (xargs :guard (natp offset)
                    :guard-hints (("goal" :in-theory
                                   (disable unsigned-byte-p))))
             (type (unsigned-byte 32) x))
    (b* (((when (= (the (unsigned-byte 32) x) 0))
          ;; Maybe an optimization when dealing with sparse data
          acc)
         (acc (bits-0-7 (+ offset 24) (the (unsigned-byte 32) (ash x -24)) acc))
         (acc (bits-0-7 (+ offset 16) (the (unsigned-byte 32) (ash x -16)) acc))
         (acc (bits-0-7 (+ offset 8)  (the (unsigned-byte 32) (ash x -8)) acc)))
      (bits-0-7 offset x acc)))

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
                       (:free (c) (append nil c)))))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm bits-0-31-redef
    (implies (natp offset)
             (equal (bits-0-31 offset x acc)
                    (append (add-to-each offset (bits-between 0 32 x))
                            acc)))
    :hints(("Goal" :in-theory (e/d (bits-0-31 append)
                                   (right-shift-to-logtail))))))



(defsection 60bits-0-59
  :parents (bits-between)
  :short "Partially unrolled version of @(see bits-between) that collects the
bits from a 60-bit unsigned @('x') and adds @('offset') to each."

  :long "<p>In CCL, 60-bit unsigned numbers are fixnums and, according to
the following loops, this is about 3.6x faster than bits-between.</p>

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

  (defund 60bits-0-7 (offset x acc)
    ;; Identical to bits-0-7, but for 60-bit unsigned ints
    (declare (xargs :guard (natp offset))
             (type (unsigned-byte 60) x))
    (b* ((acc (if (logbitp 7 x) (cons (+ 7 offset) acc) acc))
         (acc (if (logbitp 6 x) (cons (+ 6 offset) acc) acc))
         (acc (if (logbitp 5 x) (cons (+ 5 offset) acc) acc))
         (acc (if (logbitp 4 x) (cons (+ 4 offset) acc) acc))
         (acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
         (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
         (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
         (acc (if (logbitp 0 x) (cons offset acc)       acc)))
      acc))

  (defund 60bits-0-3 (offset x acc)
    ;; Since 8 doesn't divide 60, we have this goofy function for the final
    ;; bits.
    (declare (xargs :guard (natp offset))
             (type (unsigned-byte 60) x))
    (b* ((acc (if (logbitp 3 x) (cons (+ 3 offset) acc) acc))
         (acc (if (logbitp 2 x) (cons (+ 2 offset) acc) acc))
         (acc (if (logbitp 1 x) (cons (+ 1 offset) acc) acc))
         (acc (if (logbitp 0 x) (cons offset acc)       acc)))
      acc))

  (defund 60bits-0-59 (offset x acc)
    (declare (xargs :guard (natp offset))
             (type (unsigned-byte 60) x))
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
      (60bits-0-7 offset x acc)))

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
                       (:free (c) (append nil c)))))))

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
                       (:free (c) (append nil c)))))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (defthm 60bits-0-59-redef
    (implies (natp offset)
             (equal (60bits-0-59 offset x acc)
                    (append (add-to-each offset (bits-between 0 60 x))
                            acc)))
    :hints(("Goal" :in-theory (e/d (60bits-0-59 append)
                                   (right-shift-to-logtail))))))

