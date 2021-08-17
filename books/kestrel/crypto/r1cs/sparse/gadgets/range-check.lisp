; An R1CS gadget for comparing a packed value to a constant
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; STATUS: DRAFT

;; This is based on "A.3.2.2 Range check" in the Zcash Protocol Specification.

(include-book "boolean")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/bv-lists/bit-listp" :dir :system)
(include-book "kestrel/bv/bitand" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/bv-lists/bit-listp-rules" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(in-theory (disable rtl::primep)) ;todo

(in-theory (disable mv-nth)) ;todo

(local (in-theory (enable acl2::natp-of-+-of-1-alt)))

(local
 (defthm symbolp-of-if
   (equal (symbolp (if test x y))
          (if test (symbolp x) (symbolp y)))))

(defthmd <-of-integer-length-when-equal-of-getbit-and-1
  (implies (and (equal (getbit n x) 1)
                (natp x)
                (natp n))
           (< n (integer-length x)))
  :hints (("Goal" :in-theory (e/d (integer-length getbit)
                                  (acl2::bvchop-1-becomes-getbit
                                   acl2::slice-becomes-getbit)))))

(local
 (defthm member-equal-of-cdr-of-assoc-equal-when-subsetp-equal-of-strip-cdrs
   (implies (and (subsetp-equal (strip-cdrs alist) vals)
                 (assoc-equal key alist))
            (member-equal (cdr (assoc-equal key alist)) vals))))

(local
 (defthm symbolp-of-cdr-of-assoc-equal-when-symbol-listp-of-strip-cdrs
   (implies (symbol-listp (strip-cdrs alist))
            (symbolp (cdr (assoc-equal key alist))))))

;; Make a constraint asserting that a * b = c
(defund make-product-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (r1cs-constraint (list `(1 ,a))
                   (list `(1 ,b))
                   (list `(1 ,c))))

(defthm r1cs-constraintp-of-make-product-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs-constraintp (make-product-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-product-constraint))))

(defthm make-product-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (force (valuation-bindsp valuation a))
                (force (valuation-bindsp valuation b))
                (force (valuation-bindsp valuation c))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-product-constraint a b c) valuation prime)
                  (equal (mul (lookup-equal a valuation)
                              (lookup-equal b valuation)
                              prime)
                         (lookup-equal c valuation))))
  :hints (("Goal" :in-theory (enable make-product-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal))))

;; Make a constraint asserting that a AND b = c, assuming they are all bits.
(defund make-bitand-constraint (a b c)
  (declare (xargs :guard (and (symbolp a)
                              (symbolp b)
                              (symbolp c))))
  (make-product-constraint a b c))

(defthm r1cs-constraintp-of-make-bitand-constraint
  (implies (and (symbolp a)
                (symbolp b)
                (symbolp c))
           (r1cs-constraintp (make-bitand-constraint a b c)))
  :hints (("Goal" :in-theory (enable make-bitand-constraint))))

(defthm make-bitand-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (force (valuation-bindsp valuation a))
                (force (bitp (lookup-equal a valuation)))
                (force (valuation-bindsp valuation b))
                (force (bitp (lookup-equal b valuation)))
                (force (valuation-bindsp valuation c))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-bitand-constraint a b c) valuation prime)
                  (equal (acl2::bitand (lookup-equal a valuation)
                                       (lookup-equal b valuation))
                         (lookup-equal c valuation))))
  :hints (("Goal" :in-theory (enable make-bitand-constraint
                                     bitp))))

;; Make a constraint asserting that var1 = var2.
(defund make-equality-constraint (var1 var2)
  (declare (xargs :guard (and (symbolp var1)
                              (symbolp var2))))
  ;; (1*1) * (1*var1) = (1*var2):
  (r1cs-constraint (list `(1 1))
                   (list `(1 ,var1))
                   (list `(1 ,var2))))

(defthm make-equality-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var1)
                (valuation-bindsp valuation var2)
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-equality-constraint var1 var2) valuation prime)
                  (equal (lookup-equal var1 valuation)
                         (lookup-equal var2 valuation))))
  :hints (("Goal" :in-theory (enable make-equality-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal))))

(defund index-of-lowest-0-aux (i x)
  (declare (xargs :guard (and (natp x)
                              (natp i))
                  :measure (nfix (+ 1 (- (+ 1 (integer-length x)) i)))
                  :hints (("Goal" :use (:instance <-of-integer-length-when-equal-of-getbit-and-1
                                                  (n i))))))
  (if (or (not (mbt (integerp i)))
          (not (mbt (natp x)))
          (equal 0 (getbit i x)))
      i
    (index-of-lowest-0-aux (+ 1 i) x)))

;; (index-of-lowest-0-aux 0 7)

(defthm index-of-lowest-0-aux-linear
  (implies (natp i)
           (<= i (index-of-lowest-0-aux i x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable index-of-lowest-0-aux))))

(defthm <=-of-index-of-lowest-0-aux
  (implies (and (equal 0 (getbit i x))
                (<= j i)
                (Natp j)
                (natp i))
           (<= (index-of-lowest-0-aux j x) i))
  :hints (("Goal" :in-theory (enable INDEX-OF-LOWEST-0-AUX))))

(defund index-of-lowest-0 (x)
  (declare (xargs :guard (natp x)))
  (index-of-lowest-0-aux 0 x))

(defthm <=-of-index-of-lowest-0-linear
  (implies (and (equal 0 (getbit i x))
                (natp i))
           (<= (index-of-lowest-0 x) i))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable INDEX-OF-LOWEST-0))))

(defthm natp-of-index-of-lowest-0
  (natp (index-of-lowest-0 x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable index-of-lowest-0))))

(local (in-theory (disable natp)))

;; Returns (mv constraints pivar-renaming), where the constraints added to
;; CONSTRAINTS-ACC assert that all of the (bit) values of the avars, from a_i
;; down through a_tvar, are at least as big as the corresponding bits of c.
(defund make-range-check-pi-constraints-aux (i ; index of the next bit to check, counts down
                                             tvar ; lowest index to check (can't just call this "t", hence "tvar")
                                             avars ; a_0 through a_(n-1)
                                             pivars ; pi_0 through pi_(n-1)
                                             c ; the constant to which we are comparing the (packed) AVARS
                                             constraints-acc
                                             pivar-renaming ; maps pivar indices to the corresponding equivalent, higher-numbered pivars and/or to a_n-1
                                             )
  (declare (xargs :guard (and (integerp i)
                              (natp tvar)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (equal (len avars)
                                     (len pivars))
                              ;; (<= (+ -1 tvar) i)
                              (< (+ 1 i) (len pivars)) ; ensures that pi_i+1 is among the pivars
                              (natp c)
                              (true-listp constraints-acc)
                              (alistp pivar-renaming)
                              (nat-listp (strip-cars pivar-renaming))
                              (symbol-listp (strip-cdrs pivar-renaming)))
                  :verify-guards nil ;done below
                  :measure (nfix (+ 1 i))))
  (if (or (not (mbt (natp tvar)))
          (not (mbt (integerp i)))
          (< i tvar))
      (mv (acl2::reverse-list constraints-acc) pivar-renaming)
    (let* ((c_i (getbit i c))
           (pi_i (nth i pivars))
           (pi_i+1 (nth (+ 1 i) pivars))
           ;; possibly rename pi_i+1 to some higher var:
           (pi_i+1 (let ((res (assoc (+ 1 i) pivar-renaming)))
                     (if res
                         (cdr res)
                       pi_i+1))))
      (if (equal c_i 0)
          (make-range-check-pi-constraints-aux (+ -1 i) tvar avars pivars c
                                               ;; no actual constraint added:
                                               constraints-acc
                                               ;; records the fact that pi_i is just pi_i+1
                                               ;; (but pi_i+1 may have been equated to some
                                               ;; higher numbered pivar -- see above):
                                               (acons i pi_i+1 pivar-renaming))
        (let ((a_i (nth i avars)))
          (make-range-check-pi-constraints-aux (+ -1 i) tvar avars pivars c
                                               ;; Add the constraint that pi_i+1 * a_i = pi_i
                                               ;; That is, pi_i ("all the a's down through a_i
                                               ;; are >= the corresponding c's") iff both p_i+1
                                               ;; ("all the a's down through a_i+1 are >= the
                                               ;; corresponding c's") AND a_i is >= c_i (note
                                               ;; that c_i here is known to be 1, so a_i must
                                               ;; also be 1 if it is to be >= c_i).
                                               (cons (make-bitand-constraint pi_i+1 a_i pi_i) constraints-acc)
                                               pivar-renaming))))))

(verify-guards make-range-check-pi-constraints-aux)

(defthm make-range-check-pi-constraints-aux-base-case
  (implies (< i tvar)
           (equal (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
                  (mv (acl2::reverse-list constraints-acc) pivar-renaming)))
  :hints (("Goal" :expand (MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX
                           I TVAR AVARS
                           PIVARS C CONSTRAINTS-ACC PIVAR-RENAMING))))


;; (make-range-check-pi-constraints-aux 12 ; bit 13 is handled separately
;;                      4
;;                      '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
;;                      '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 pi8 pi9 pi10 pi11 pi12 pi13)
;;                      #b11100011001111
;;                      nil
;;                      nil)

(defthm r1cs-constraint-listp-of-mv-nth-0-of-make-range-check-pi-constraints-aux
  (implies (and (alistp pivar-renaming)
                (nat-listp (strip-cars pivar-renaming))
                (symbol-listp (strip-cdrs pivar-renaming))
                (symbol-listp pivars)
                (symbol-listp avars)
                (natp tvar)
                (natp i)
                (equal (len avars)
                       (len pivars))
                (< (+ 1 i) (len pivars))
                (r1cs-constraint-listp constraints-acc))
           (r1cs-constraint-listp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm alistp-of-mv-nth-1-of-make-range-check-pi-constraints-aux
  (implies (and (alistp pivar-renaming)
                ;(nat-listp (strip-cars pivar-renaming))
                (alistp pivar-renaming)
                (symbol-listp pivars))
           (alistp (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm nat-listp-of-strip-cars-of-mv-nth-1-of-make-range-check-pi-constraints-aux
  (implies (and (alistp pivar-renaming)
                (nat-listp (strip-cars pivar-renaming))
                (alistp pivar-renaming)
                (symbol-listp pivars))
           (nat-listp (strip-cars (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm symbol-listp-of-strip-cdrs-of-mv-nth-1-of-make-range-check-pi-constraints-aux
  (implies (and (alistp pivar-renaming)
                ;; (alistp pivar-renaming)
                (symbol-listp pivars)
                (symbol-listp (strip-cdrs pivar-renaming)))
           (symbol-listp (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

;; Find the avars from a_i down to a_0 that correspond to 1 bits in c
(defund avars-for-1s (avars i c)
  (declare (xargs :guard (and (integerp i)
                              (symbol-listp avars)
                              (natp c))
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      nil
    (if (equal 1 (getbit i c)) ;if c_i = 1
        (cons (nth i avars)
              (avars-for-1s avars (+ -1 i) c))
      (avars-for-1s avars (+ -1 i) c))))

(defthm subsetp-equal-of-avars-for-1s
  (implies (and (natp i)
                (< i (len avars)))
           (subsetp-equal (avars-for-1s avars i c) avars))
  :hints (("Goal" :expand ((avars-for-1s avars 0 c))
           :in-theory (enable avars-for-1s subsetp-equal))))

;; Find the pivars from pi_i down to pi_tvar that correspond to 1 bits in c
(defund pivars-for-1s (pivars i tvar c)
  (declare (xargs :guard (and (integerp i)
                              (natp tvar)
                              (symbol-listp pivars)
                              (natp c))
                  :measure (nfix (+ 1 i))))
  (if (or (not (mbt (natp tvar)))
          (not (mbt (integerp i)))
          (< i tvar))
      nil
    (if (equal 1 (getbit i c)) ;if c_i = 1
        (cons (nth i pivars)
              (pivars-for-1s pivars (+ -1 i) tvar c))
      (pivars-for-1s pivars (+ -1 i) tvar c))))

;; Find the indices from high down through low that correspond to 1 bits in c
(defund indices-for-1s (high low c)
  (declare (xargs :guard (and (integerp high)
                              (integerp low)
                              (natp c))
                  :measure (nfix (+ 1 (- high low)))))
  (if (or (not (natp high))
          (not (natp low))
          (< high low))
      nil
    (if (equal 1 (getbit high c))
        (cons high
              (indices-for-1s (+ -1 high) low c))
      (indices-for-1s (+ -1 high) low c))))

;; Find the indices from high down through low that correspond to 0 bits in c
(defund indices-for-0s (high low c)
  (declare (xargs :guard (and (integerp high)
                              (integerp low)
                              (natp c))
                  :measure (nfix (+ 1 (- high low)))))
  (if (or (not (natp high))
          (not (natp low))
          (< high low))
      nil
    (if (equal 0 (getbit high c))
        (cons high
              (indices-for-0s (+ -1 high) low c))
      (indices-for-0s (+ -1 high) low c))))

(defthm indices-for-0s-of-+-of-1
  (implies (and (equal (getbit low c) 1)
                (integerp high)
                (natp low)
                (natp c))
           (equal (indices-for-0s high (+ 1 low) c)
                  (indices-for-0s high low c)))
  :hints (("Goal" :in-theory (enable indices-for-0s))))

(defthm indices-for-0s-of-when-low-bit-is-0
  (implies (and (equal (getbit low c) 0)
                (integerp high)
                (natp low)
                (<= low high))
           (equal (indices-for-0s high low c)
                  (append (indices-for-0s high (+ 1 low) c)
                          (list low))))
  :hints (("Goal" :in-theory (enable indices-for-0s))))

(defthmd indices-for-0s-of-when-low-bit-is-1
  (implies (and (equal (getbit low c) 1)
                (integerp high)
                (natp low)
                (<= low high))
           (equal (indices-for-0s high low c)
                  (indices-for-0s high (+ 1 low) c)))
  :hints (("Goal" :in-theory (enable indices-for-0s))))


;; ;; Find the pivars from pi_high down to pi_low that correspond to 0 bits in c
;; (defund pivars-for-0s (pivars high low c)
;;   (declare (xargs :guard (and (integerp high)
;;                               (natp low)
;;                               (symbol-listp pivars)
;;                               (natp c))
;;                   :measure (nfix (+ 1 high))))
;;   (if (or (not (mbt (natp low)))
;;           (not (mbt (integerp high)))
;;           (< high low))
;;       nil
;;     (if (equal 0 (getbit high c)) ;if c_high = 1
;;         (cons (nth high pivars)
;;               (pivars-for-0s pivars (+ -1 high) low c))
;;       (pivars-for-0s pivars (+ -1 high) low c))))

;; (defthm pivars-for-0s-of-+-of-1
;;   (implies (and (equal (getbit low c) 1)
;;                 (integerp high)
;;                 (natp low)
;;                 (symbol-listp pivars)
;;                 (natp c))
;;            (equal (pivars-for-0s pivars high (+ 1 low) c)
;;                   (pivars-for-0s pivars high low c)))
;;   :hints (("Goal" :in-theory (enable pivars-for-0s))))

;; (defthm pivars-for-0s-of-when-low-bit-is-0
;;   (implies (and (equal (getbit low c) 0)
;;                 (integerp high)
;;                 (natp low)
;;                 (<= low high)
;;                 (symbol-listp pivars)
;;                 (natp c))
;;            (equal (pivars-for-0s pivars high low c)
;;                   (append (pivars-for-0s pivars high (+ 1 low) c)
;;                           (list (nth low pivars)))))
;;   :hints (("Goal" :in-theory (enable pivars-for-0s))))

(defthm pivars-for-1s-of-when-low-bit-is-1
  (implies (and (equal (getbit low c) 1)
                (integerp high)
                (natp low)
                (<= low high)
                (symbol-listp pivars)
                (natp c))
           (equal (pivars-for-1s pivars high low c)
                  (append (pivars-for-1s pivars high (+ 1 low) c)
                          (list (nth low pivars)))))
  :hints (("Goal" :in-theory (enable pivars-for-1s))))

(defthmd pivars-for-1s-of-when-low-bit-is-0
  (implies (and (equal (getbit low c) 0)
                (integerp high)
                (natp low)
                (<= low high)
                )
           (equal (pivars-for-1s pivars high low c)
                  (pivars-for-1s pivars high (+ 1 low) c)))
  :hints (("Goal" :in-theory (enable pivars-for-1s))))

;; (defun low-count-up-induct (low high)
;;   (declare (xargs :measure (nfix (+ 1 (- high low)))))
;;   (if (or (not (natp low))
;;           (not (natp high))
;;           (< high low))
;;       (list high low)
;;     (low-count-up-induct (+ 1 low) high)))

(defthmd pivars-for-1s-redef
  (implies (and ;(equal (getbit low c) 1)
                (integerp high)
                (natp low)
                (<= low high)
                (symbol-listp pivars)
                (natp c))
           (equal (pivars-for-1s pivars high low c)
                  (append (pivars-for-1s pivars high (+ 1 low) c)
                          (if (equal (getbit low c) 1)
                              (list (nth low pivars))
                            nil))))
  :hints (("Goal" :in-theory (enable pivars-for-1s))))

(defthm pivars-for-1s-of-+-of-1-when-low-bit-is-1
  (implies (and (equal (getbit low c) 0)
                (integerp high)
                (natp low)
                (<= low high)
                (symbol-listp pivars)
                (natp c)
                )
           (equal (pivars-for-1s pivars high (+ 1 low) c)
                  (pivars-for-1s pivars high low c)))
  :hints (("Goal" :in-theory (enable pivars-for-1s-redef))))

(defthm assoc-equal-when-member-equal-of-strip-cars
  (implies (and (equal (strip-cars alist) free)
                (alistp alist))
           (iff (assoc-equal key alist)
                (member-equal key free))))

(defthm assoc-equal-when-not-member-equal-of-strip-cars
  (implies (not (member-equal key (strip-cars alist)))
           (equal (assoc-equal key alist)
                  nil))
  :hints (("Goal" :in-theory (enable strip-cars assoc-equal))))

;move
(defthm equal-of-nth-and-nth-when-no-duplicatesp-equal
  (implies (and (no-duplicatesp-equal x)
                (natp n1)
                (< n1 (len x))
                (natp n2)
                (< n2 (len x)))
           (equal (equal (nth n1 x) (nth n2 x))
                  (equal n1 n2)))
  :hints (("Goal" :in-theory (enable (:i nth) no-duplicatesp-equal))))

(defthm equal-of-nth-and-car-when-no-duplicatesp-equal
  (implies (and (no-duplicatesp-equal x)
                (natp n1)
                (< n1 (len x)))
           (equal (equal (nth n1 x) (car x))
                  (equal n1 0)))
  :hints (("Goal" :in-theory (enable (:i nth) no-duplicatesp-equal))))

(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

;move
(defthm not-member-equal-of-take-when-not-member-equal-of-take
  (implies (and (NOT (MEMBER-EQUAL val (TAKE free x)))
                (<= m free)
                (natp m)
                (natp free)
                (< free (len x)))
           (NOT (MEMBER-EQUAL val (TAKE m x))))
  :hints (("Goal" :in-theory (enable member-equal take))))

(defthm member-equal-of-nth-of-take-of-cdr
  (implies (and (natp n)
                (< 0 n)
                ;(<= (+ 1 n) (len x))
                )
           (member-equal (nth n x)
                         (take n (cdr x))))
  :hints (("Goal" :in-theory (enable (:i nth) take member-equal))))

;; (defthm not-member-equal-of-pivars-for-0s-when-not-member-equal-of-take
;;   (implies (and (not (member-equal x (take (+ 1 high) pivars)))
;;                 (<= 0 high)
;; ;               (<= low high)
;;                 (integerp high)
;;                 (< high (len pivars))
;; ;(integerp low)
;; ;(<= 0 low)
;;                 (no-duplicatesp-equal pivars)
;;                 )
;;            (not (member-equal x (pivars-for-0s pivars high low c))))
;;   :hints (("Goal" :in-theory (e/d (take pivars-for-0s) (len)))))

(defthm not-member-equal-of-pivars-for-1s-when-not-member-equal-of-take
  (implies (and (not (member-equal x (take (+ 1 high) pivars)))
                (<= 0 high)
;               (<= low high)
                (integerp high)
                (< high (len pivars))
;(integerp low)
;(<= 0 low)
                (no-duplicatesp-equal pivars)
                )
           (not (member-equal x (pivars-for-1s pivars high low c))))
  :hints (("Goal" :in-theory (e/d (take pivars-for-1s) (len)))))

(defthm not-member-equal-of-nth-and-take-when-no-duplicatesp-equal
  (implies (and (no-duplicatesp-equal x)
                (natp n)
                (< n (len x)))
           (not (member-equal (nth n x) (take n x))))
  :hints (("Goal" :in-theory (enable (:i nth) take member-equal))))

;; (defthm member-equal-of-nth-and-pivars-for-0s
;;   (implies (and (natp i)
;;                 (<= low i)
;;                 (< i (len pivars))
;;                 ;;(<= low high)
;;                 (integerp high)
;;                 (< high (len pivars))
;;                 (natp low)
;;                 ;;(symbol-listp pivars)
;;                 (no-duplicatesp-equal pivars)
;;                 (natp c))
;;            (iff (member-equal (nth i pivars) (pivars-for-0s pivars high low c))
;;                 (and (<= i high)
;;                      (equal 0 (getbit i c)))))
;;   :hints (("subgoal *1/3" :cases ((equal 0 high)))
;;           ("Goal" :in-theory (e/d (pivars-for-0s)
;;                                   (acl2::zp-open
;;                                    ;;acl2::member-equal-of-cons-non-constant
;;                                    acl2::nth-of-cons-safe
;;                                    )))))

(defthm member-equal-of-indices-for-0s
  (implies (and (natp i)
                ;; (<= low i)
                ;; (<= low high)
                (integerp high)
                (natp low))
           (iff (member-equal i (indices-for-0s high low c))
                (and (<= i high)
                     (<= low i)
                     (equal 0 (getbit i c)))))
  :hints (("subgoal *1/3" :cases ((equal 0 high)))
          ("Goal" :in-theory (e/d (indices-for-0s)
                                  (acl2::zp-open
                                   ;;acl2::member-equal-of-cons-non-constant
                                   acl2::nth-of-cons-safe
                                   )))))

(defthm make-range-check-pi-constraints-aux-of-append
  (equal (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c (append acc1 acc2) pivar-renaming))
         (append (acl2::reverse-list acc2)
                 (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c acc1 pivar-renaming))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm make-range-check-pi-constraints-aux-normalize-acc
  (implies (syntaxp (not (equal acc acl2::*nil*))) ; prevent loops
           (equal (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c acc pivar-renaming))
                  (append (acl2::reverse-list acc)
                          (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c nil pivar-renaming)))))
  :hints (("Goal" :use (:instance make-range-check-pi-constraints-aux-of-append (acc2 acc) (acc1 nil))
           :in-theory (disable make-range-check-pi-constraints-aux-of-append))))

(defthm bitp-of-mul
  (implies (and (bitp x)
                (bitp y))
           (bitp (mul x y p))))

(defthmd bitp-of-mul-forced
  (implies (and (force (bitp x))
                (force (bitp y)))
           (bitp (mul x y p))))

(defthm bitp-of-lookup-equal-when-bit-listp-of-lookup-eq-lst
  (implies (and (acl2::bit-listp (acl2::lookup-eq-lst keys valuation)) ; keys is a free var
                (member-equal key keys))
           (bitp (lookup-equal key valuation)))
  :hints (("Goal" :in-theory (enable acl2::lookup-eq-lst))))

(defthm member-equal-of-nth-and-pivars-for-1s
  (implies (and (integerp i)
                (<= low i)
                (< i (len pivars))
                ;;(<= low high)
                (integerp high)
                (< high (len pivars))
                (natp low)
                ;; (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (natp c))
           (iff (member-equal (nth i pivars) (pivars-for-1s pivars high low c))
                (and (<= i high)
                     (equal 1 (getbit i c)))))
  :hints (;("subgoal *1/2" :cases ((equal 0 high)))
          ("Goal" :in-theory (e/d (pivars-for-1s natp)
                                  (acl2::zp-open
                                   ;;acl2::member-equal-of-cons-non-constant
                                   acl2::nth-of-cons-safe
                                   ;ACL2::NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL
                                   )))))

(defthm member-equal-of-nth-and-avars-for-1s
  (implies (and (natp i)
                (< i (len avars))
                (integerp high)
                (< high (len avars))
                ;;(symbol-listp avars)
                (no-duplicatesp-equal avars)
                (natp c))
           (iff (member-equal (nth i avars) (avars-for-1s avars high c))
                (and (<= i high)
                     (equal 1 (getbit i c)))))
  :hints (("subgoal *1/2" :cases ((equal 0 high)))
          ("Goal" :in-theory (e/d (avars-for-1s)
                                  (acl2::zp-open
                                   ;;acl2::member-equal-of-cons-non-constant
                                   acl2::nth-of-cons-safe
                                   )))))

(local (in-theory (disable SYMBOL-ALISTP STRIP-CDRS len STRIP-CARS NO-DUPLICATESP-EQUAL SYMBOL-LISTP
                           R1CS-CONSTRAINTS-HOLDP)))

(in-theory (disable bitp))

;;move
(defthm r1cs-constraints-holdp-when-not-consp
  (implies (not (consp constraints))
           (r1cs-constraints-holdp constraints valuation prime))
  :hints (("Goal" :in-theory (enable r1cs-constraints-holdp))))

(defthm r1cs-constraints-holdp-when-subsetp-equal
  (implies (and (r1cs-constraints-holdp constraints+ valuation prime)
                (subsetp-equal constraints constraints+))
           (r1cs-constraints-holdp constraints valuation prime))
  :hints (("Goal" :in-theory (enable r1cs-constraints-holdp
                                     subsetp-equal))))

;; (defun-sk constraints-imply-var-is-bitp (constraints var p)
;;   (forall (valuation)
;;           (implies (r1cs-constraints-holdp constraints valuation p)
;;                    (acl2::bitp (acl2::lookup-eq var valuation)))))

;; (in-theory (disable constraints-imply-var-is-bitp))

;; (defthm constraints-imply-var-is-bitp-necc-better
;;   (implies (and (r1cs-constraints-holdp constraints valuation p)
;;                 (constraints-imply-var-is-bitp constraints var p))
;;            (bitp (lookup-eq var valuation)))
;;   :hints (("Goal" :use (:instance constraints-imply-var-is-bitp-necc)
;;            :in-theory (disable constraints-imply-var-is-bitp-necc))))

;; (defthm constraints-imply-var-is-bitp-monotonic
;;   (implies (and (constraints-imply-var-is-bitp constraints var p)
;;                 (subsetp-equal constraints constraints+))
;;            (constraints-imply-var-is-bitp constraints+ var p))
;;   :hints (("Goal" :expand ((constraints-imply-var-is-bitp constraints+ var p))
;;            :in-theory (disable constraints-imply-var-is-bitp-necc-better)
;;            :use (:instance constraints-imply-var-is-bitp-necc-better
;;                            (valuation (CONSTRAINTS-IMPLY-VAR-IS-BITP-WITNESS CONSTRAINTS+ VAR P))))))

;; (defund constraints-imply-vars-are-bitps (constraints vars p)
;;   (if (endp vars)
;;       t
;;     (and (constraints-imply-var-is-bitp constraints (first vars) p)
;;          (constraints-imply-vars-are-bitps constraints (rest vars) p))))

;; (defthm constraints-imply-vars-are-bitps-of-append
;;   (equal (constraints-imply-vars-are-bitps constraints (append vars1 vars2) p)
;;          (and (constraints-imply-vars-are-bitps constraints vars1 p)
;;               (constraints-imply-vars-are-bitps constraints vars2 p)))
;;   :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

;; (defthm constraints-imply-vars-are-bitps-when-not-consp
;;   (implies (not (consp vars))
;;            (constraints-imply-vars-are-bitps constraints vars p))
;;   :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

;; (defthm constraints-imply-vars-are-bitps-of-cons
;;   (equal (constraints-imply-vars-are-bitps constraints (cons var vars) p)
;;          (and (constraints-imply-var-is-bitp constraints var p)
;;               (constraints-imply-vars-are-bitps constraints vars p)))
;;   :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

;; (defthm constraints-imply-vars-are-bitps-monotonic
;;   (implies (and (constraints-imply-vars-are-bitps constraints vars p)
;;                 (subsetp-equal constraints constraints+))
;;            (constraints-imply-vars-are-bitps constraints+ vars p))
;;   :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))


(defund constraints-imply-vars-are-bitps (constraints vars valuation p)
  (implies (r1cs-constraints-holdp constraints valuation p)
           (acl2::bit-listp (acl2::lookup-eq-lst vars valuation))))

(defthm constraints-imply-vars-are-bitps-of-append
  (equal (constraints-imply-vars-are-bitps constraints (append vars1 vars2) valuation p)
         (and (constraints-imply-vars-are-bitps constraints vars1 valuation p)
              (constraints-imply-vars-are-bitps constraints vars2 valuation p)))
  :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

(defthm constraints-imply-vars-are-bitps-when-not-consp
  (implies (not (consp vars))
           (constraints-imply-vars-are-bitps constraints vars valuation p))
  :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

(defthm constraints-imply-vars-are-bitps-monotonic
  (implies (and (constraints-imply-vars-are-bitps constraints vars valuation p)
                (subsetp-equal constraints constraints+))
           (constraints-imply-vars-are-bitps constraints+ vars valuation p))
  :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

(defthm constraints-imply-vars-are-bitps-of-cons
  (equal (constraints-imply-vars-are-bitps constraints (cons var vars) valuation p)
         (and (implies (R1CS-CONSTRAINTS-HOLDP CONSTRAINTS VALUATION P)
                       (bitp (acl2::lookup-eq var valuation)))
              (constraints-imply-vars-are-bitps constraints vars valuation p)))
  :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

(defthm helper
  (implies (and (not (equal val (cdr (assoc-equal key alist))))
                (assoc-equal key alist)
                (subsetp-equal (strip-cdrs alist) (cons val vals)))
           (member-equal (cdr (assoc-equal key alist)) vals))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

(defthm SUBSETP-EQUAL-of-strip-cdrs-of-cdr
  (Implies (SUBSETP-EQUAL (STRIP-CDRS x) y)
           (SUBSETP-EQUAL (STRIP-CDRS (cdr x)) y)))

(defthm SYMBOL-LISTP-of-strip-cdrs-of-cdr
  (implies (SYMBOL-LISTP (STRIP-CDRS x))
           (SYMBOL-LISTP (STRIP-CDRS (CDR x)))))

(in-theory (disable ASSOC-EQUAL))

(defthm bitp-of-lookup-equal-when-constraints-imply-vars-are-bitps
  (implies (and (constraints-imply-vars-are-bitps constraints vars valuation p)
                (r1cs-constraints-holdp constraints valuation p)
                (member-equal var vars)
                )
           (bitp (lookup-equal var valuation)))
  :hints (("Goal" :in-theory (enable constraints-imply-vars-are-bitps))))

(defthm valuation-binds-allp-when-not-consp
  (implies (not (consp vars))
           (valuation-binds-allp valuation vars))
  :hints (("Goal" :in-theory (enable valuation-binds-allp))))

(defthm valuation-binds-allp-when-subsetp-equal
  (implies (and (valuation-binds-allp valuation vars+)
                (subsetp-equal vars vars+))
           (valuation-binds-allp valuation vars))
  :hints (("Goal" :in-theory (enable valuation-binds-allp subsetp-equal))))

;; All of the pivars that correspond to 1s in c are constrained to be
;; boolean-valued, assuming the vvars that correspond to 1s in c are boolean
;; valued.
;;need something about the pis above i.  are they in the acc?
;;just use the 0s and 1s aux functions?
(defthm bit-listp-of-lookup-eq-lst-of-pivars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux
  (implies (and (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                ;; the constraints already in the accumulator must tell us
                ;; that the higher-numbered pivars are bits (but note that
                ;; p_n-1 is handled separately):
                (constraints-imply-vars-are-bitps constraints-acc (pivars-for-1s pivars (+ -2 n) (+ 1 i) c) valuation p)
                (integerp i)
                (natp tvar)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (<= i (+ -2 n))
                ;; (<= (+ -1 tvar) i)
     ;(< (+ 1 i) (len pivars)) ; ensures that pi_i+1 is among the pivars
                (natp c)
                (alistp pivar-renaming)
                (nat-listp (strip-cars pivar-renaming))
                (symbol-listp (strip-cdrs pivar-renaming))
                ;; the necessary avars and pivars are bound:
                (valuation-binds-allp valuation (avars-for-1s avars (+ -1 n) c))
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) tvar c))
                (valuation-binds-allp valuation (strip-cdrs pivar-renaming)) ;drop?
                ;; the renaming has entries for all the right vars so far:
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (+ 1 i) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (+ 1 i) c)))
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                ;; (acl2::bit-listp (acl2::lookup-eq-lst (strip-cdrs pivar-renaming) valuation))
                ;; (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (+ 1 i) c) valuation))
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars i tvar c) valuation)))
  :hints (("[1]subgoal 8" :cases ((equal (NTH (+ -1 (LEN AVARS)) AVARS)
                                         (CDR (ASSOC-EQUAL (+ 1 I) PIVAR-RENAMING)))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX I TVAR AVARS PIVARS C CONSTRAINTS-ACC PIVAR-RENAMING)
           :expand ((make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
     ;(MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX (+ -2 (LEN AVARS)) TVAR AVARS PIVARS C NIL PIVAR-RENAMING)
     ;(AVARS-FOR-1S AVARS (+ -2 (LEN AVARS)) C)
     ;(PIVARS-FOR-1S PIVARS (+ -2 (LEN AVARS)) TVAR C)
                    (AVARS-FOR-1S AVARS I C)
                    (PIVARS-FOR-1S PIVARS I TVAR C))
           :in-theory (e/d ((:I make-range-check-pi-constraints-aux)
                            bitp-of-mul-forced
                            natp
                            make-bitand-constraint ;why?
                            )
                           (bitp)))))

(defthm mv-nth-1-of-make-range-check-pi-constraints-aux-type-1
  (implies (and (rtl::primep p)
                (integerp i)
                (natp tvar)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (<= i (+ -2 n))
                (natp c)
                (alistp pivar-renaming)
                (symbol-listp (strip-cdrs pivar-renaming))
                ;; the renaming has entries for all the right vars so far:
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (+ 1 i) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (<= tvar i) ;todo?
                )
           (equal (strip-cars (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)))
                  (append (acl2::reverse-list (indices-for-0s (+ -2 n) tvar c))
                          (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                          )))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX I TVAR AVARS PIVARS C CONSTRAINTS-ACC PIVAR-RENAMING)

           :in-theory (e/d (make-range-check-pi-constraints-aux
                            bitp-of-mul-forced)
                           (bitp)))))

(defthm mv-nth-1-of-make-range-check-pi-constraints-aux-type-2
  (implies (and (rtl::primep p)
                (integerp i)
                (natp tvar)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (<= i (+ -2 n))
                (natp c)
                (alistp pivar-renaming)
                (symbol-listp (strip-cdrs pivar-renaming))
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (+ 1 i) c)))
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (+ 1 i) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (<= tvar i)
                )
           (subsetp-equal (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)))
                          (cons (nth (+ -1 n) avars)
                                (pivars-for-1s pivars (+ -2 n) tvar c))))
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX I TVAR AVARS PIVARS C CONSTRAINTS-ACC PIVAR-RENAMING)

           :in-theory (e/d (make-range-check-pi-constraints-aux
                            bitp-of-mul-forced)
                           (bitp)))))

;; Returns (mv constraints pivar-renaming), where the constraints assert that
;; all of the (bit) values of the avars, from a_i down through the index of the
;; least significant 0 in c, are at least as big as the corresponding bits of
;; c.
(defund make-range-check-pi-constraints (avars ; a_0 through a_(n-1)
                                         pivars ; pi_0 through pi_(n-1)
                                         c ; the constant to which we are comparing the (packed) AVARS
                                         n ; number of bits in c
                                         )
  (declare (xargs :guard (and (posp n)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (equal n (len avars))
                              (equal n (len pivars))
                              (unsigned-byte-p n c)
                              (equal 1 (getbit (+ -1 n) c)) ;leading 1
                              )))
  (let* (;;(pi_n-1 (nth (+ -1 n) pivars))
         (a_n-1 (nth (+ -1 n) avars))
         (tvar (index-of-lowest-0 c)))
    (make-range-check-pi-constraints-aux (+ -2 n)
                                         tvar
                                         avars
                                         pivars
                                         c
                                         nil
                                         ;; Let pi_n-1 = a_n-1.  Note that this is not a
                                         ;; constraint:
                                         (acons (+ -1 n) a_n-1 nil))))

(defthm mv-nth-1-of-make-range-check-pi-constraints-type-1
  (implies (and (rtl::primep p)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (natp c))
           (equal (strip-cars (mv-nth 1 (make-range-check-pi-constraints avars pivars c n)))
                  (append (acl2::reverse-list (indices-for-0s (+ -2 n) (index-of-lowest-0 c) c))
                          (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                          )))
  :hints (("Goal" :cases ((<= (INDEX-OF-LOWEST-0 C) (+ -2 n))
                          (= (INDEX-OF-LOWEST-0 C) (+ -1 n)))
           :expand ((INDICES-FOR-0S (+ -2 (LEN AVARS))
                                   (INDEX-OF-LOWEST-0 C) C)
                    (INDICES-FOR-0S (BINARY-+ '-2 (LEN AVARS))
                                   (BINARY-+ '-1 (LEN AVARS))
                                   C))
           :in-theory (enable make-range-check-pi-constraints))))

(defthm mv-nth-1-of-make-range-check-pi-constraints-type-2
  (implies (and (rtl::primep p)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (natp c))
           (subsetp-equal (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints avars pivars c n)))
                          (cons (nth (+ -1 n) avars)
                                (pivars-for-1s pivars (+ -2 n) (INDEX-OF-LOWEST-0 C) c))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints indices-FOR-0S)
           :cases ((<= (INDEX-OF-LOWEST-0 C) (+ -2 n))
                   (= (INDEX-OF-LOWEST-0 C) (+ -1 n))))))

(defthm bit-listp-of-lookup-eq-lst-of-pivars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints
  (implies (and (r1cs-valuationp valuation p)
                (rtl::primep p)
                (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints avars pivars c n)) valuation p)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (posp n)
                (natp c)
                ;; all avars and pivars are bound:
                (valuation-binds-allp valuation (avars-for-1s avars (+ -1 n) c))
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                ;; We only assume that the avars corresponding to 1s are bits:
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                ;; (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (+ 1 i) c) valuation))
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           ;; note that we don't make a constraint for pi_n-1:
           (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) valuation)))
  :hints (("Goal" :use (:instance bit-listp-of-lookup-eq-lst-of-pivars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux
                                  (i (+ -2 n))
                                  (n n)
                                  (tvar (index-of-lowest-0 c))
                                  (constraints-acc nil)
                                  (pivar-renaming (acons (+ -1 n)
                                                         (nth (+ -1 n) avars)
                                                         nil)))
     ;            :cases ((equal 0 (len avars)))
     ;            :expand ((AVARS-FOR-1S AVARS (+ -1 (LEN AVARS)) C))
           :expand ((INDICES-FOR-0S (+ -2 (LEN AVARS)) (+ -1 (LEN AVARS)) C)
                    (PIVARS-FOR-1S PIVARS (+ -2 (LEN AVARS)) (+ -1 (LEN AVARS)) C))
           :in-theory (e/d (make-range-check-pi-constraints
     ;indices-FOR-0S
     ;(:d PIVARS-FOR-1S)
                            ) (bit-listp-of-lookup-eq-lst-of-pivars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux)))))

;; test:
;; (make-range-check-pi-constraints '(a0 a1 a2 a3 a4 a5 a6 a7)
;;                                  '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7)
;;                                  #b10001110 ; leading 1, as required
;;                                  8)

(defthm symbol-alistp-of-mv-nth-1-of-make-range-check-pi-constraints
  (implies (symbol-listp pivars)
           (alistp (mv-nth 1 (make-range-check-pi-constraints avars pivars c n))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints))))

(defthm symbol-listp-of-strip-cdrs-of-mv-nth-1-of-make-range-check-pi-constraints
  (implies (and (symbol-listp pivars)
                (symbol-listp avars))
           (symbol-listp (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints avars pivars c n)))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints))))

;; (defthm make-pi-constraint-correct
;;   (implies (and (r1cs-valuationp valuation p)
;;                 (valuation-bindsp valuation a)
;;                 (valuation-bindsp valuation b)
;;                 (valuation-bindsp valuation c)
;;                 ;; (bitp (lookup-eq a valuation))
;;                 ;; (bitp (lookup-eq b valuation))
;;                 (rtl::primep p)
;;                 (< 2 p))
;;            (equal (r1cs-constraints-holdp (make-range-check-pi-constraints-aux i
;;                                                                avars
;;                                                                pivars
;;                                                                c
;;                                                                pivar-renaming)
;;                                           valuation p)
;;                   ..
;;                   (equal (lookup-eq c valuation)
;;                          (acl2::bitxor (lookup-eq a valuation)
;;                                        (lookup-eq b valuation)))))
;;   :hints (("Goal" :in-theory (enable make-bitxor-constraint
;;                                      r1cs-constraint-holdsp
;;                                      integerp-of-lookup-equal
;;                                      acl2-numberp-of-lookup-equal))))

;; (1 - pi_i+1 - a_i) * a_i = 0
(defund make-range-check-a-constraint (a_i pi_i+1)
  (declare (xargs :guard (and (symbolp a_i)
                              (symbolp pi_i+1))))
  (r1cs-constraint (list `(1 1)
                         `(-1 ,pi_i+1)
                         `(-1 ,a_i))
                   (list `(1 ,a_i))
                   (list) ; 0
                   ))

(defthm r1cs-constraintp-of-make-range-check-a-constraint
  (implies (and (symbolp a_i)
                (symbolp pi_i+1))
           (r1cs-constraintp (make-range-check-a-constraint a_i pi_i+1)))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraint))))

(defthm make-range-check-a-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (force (valuation-bindsp valuation a_i))
                (force (valuation-bindsp valuation pi_i+1))
                (force (bitp (lookup-equal pi_i+1 valuation)))
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-range-check-a-constraint a_i pi_i+1) valuation prime)
                  (if (equal 1 (lookup-equal pi_i+1 valuation))
                      (equal 0 (lookup-equal a_i valuation))
                    (bitp (lookup-equal a_i valuation)))
                  ;; (equal (mul (add 1
                  ;;                  (add (neg (lookup-equal pi_i+1 valuation) prime)
                  ;;                       (neg (lookup-equal a_i valuation) prime)
                  ;;                       prime)
                  ;;                  prime)
                  ;;             (lookup-equal a_i valuation)
                  ;;             prime)
                  ;;        0)
                  ))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal
                                     pfield::mul-of--1-becomes-neg
                                     bitp))))

;; Makes the constraints for a_i down through a_0.  Returns a list of constraints
(defund make-range-check-a-constraints (i
                                        avars
                                        pivars
                                        c
                                        pivar-renaming)
  (declare (xargs :guard (and (integerp i)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (natp c)
                              (alistp pivar-renaming)
                              ;; (subsetp-equal (strip-cdrs pivar-renaming) pivars)
                              (symbol-listp (strip-cdrs pivar-renaming)))
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      nil
    (let* ((c_i (getbit i c))
           (a_i (nth i avars))
           (constraint
            (if (equal c_i 0) ; can't happen for i=n-1, so calling nth on (+ 1 i) is ok
                (let* ((pi_i+1 (nth (+ 1 i) pivars))
                       ;; Check whether we simply let pi_i+1 be some other var
                       ;; when generating the pi constraints:
                       (pi_i+1 (let ((res (assoc (+ 1 i) pivar-renaming)))
                                 (if res
                                     (cdr res)
                                   pi_i+1))))
                  (make-range-check-a-constraint a_i pi_i+1))
              (make-boolean-constraint a_i))))
      (cons constraint
            (make-range-check-a-constraints (+ -1 i)
                                            avars
                                            pivars
                                            c
                                            pivar-renaming)))))

(defthm r1cs-constraint-listp-of-make-range-check-a-constraints
  (implies (and (integerp i)
                (symbol-listp avars)
                (symbol-listp pivars)
                (natp c)
                (alistp pivar-renaming)
                ;; (subsetp-equal (strip-cdrs pivar-renaming) pivars)
                (symbol-listp (strip-cdrs pivar-renaming)))
           (r1cs-constraint-listp (make-range-check-a-constraints i avars pivars c pivar-renaming)))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraints))))

;; All of the avars that correspond to 1s in c are constrained to be boolean-valued.
(defthm bit-listp-of-lookup-eq-lst-of-avars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-a-constraints
  (implies (and (r1cs-valuationp valuation p)
                (rtl::primep p)
                ;; Here we just make the "a" constraints:
                (r1cs-constraints-holdp (make-range-check-a-constraints i avars pivars c pivar-renaming) valuation p)
                (integerp i)
                (symbol-listp avars)
                (symbol-listp pivars)
                (natp c)
                (alistp pivar-renaming)
                ;; (subsetp-equal (strip-cdrs pivar-renaming) pivars)
                (symbol-listp (strip-cdrs pivar-renaming))
                (valuation-binds-allp valuation (avars-for-1s avars i c)))
           (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars i c) valuation)))
  :hints (("Goal" :in-theory (e/d (make-range-check-a-constraints avars-for-1s)
                                  (make-range-check-a-constraint-correct
                                   bitp)))))

(defthm subsetp-equal-of-PIVARS-FOR-1S-and-PIVARS-FOR-1S
  (implies (and (integerp high)
                (natp i)
                ;(< i high)
                )
           (SUBSETP-EQUAL (PIVARS-FOR-1S PIVARS high (+ 1 I) C)
                          (PIVARS-FOR-1S PIVARS high I C)))
  :hints (("Goal" :in-theory (enable PIVARS-FOR-1S subsetp-equal))))

(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(defthmd take-opener-alt
  (implies (and (<= (+ 1 i) (len x))
                (natp i))
           (equal (take (+ 1 i) x)
                  (append (take i x) (list (nth i x)))))
  :hints (("Goal" :in-theory (enable take acl2::equal-of-append))))

(defthm helper2
  (implies (and (subsetp-equal (strip-cdrs alist) (cons val vals))
                (not (equal val (cdr (assoc-equal key alist))))
                (assoc-equal key alist))
           (member-equal (cdr (assoc-equal key alist)) vals))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

(local (in-theory (disable intersection-equal)))

(defthm bit-listp-of-lookup-eq-lst-when-bit-listp-of-lookup-eq-lst
  (implies (and (acl2::bit-listp (acl2::lookup-eq-lst (take (+ -1 (len avars)) avars) valuation))
                (consp avars))
           (equal (acl2::bit-listp (acl2::lookup-eq-lst avars valuation))
                  (bitp (lookup-equal (nth (+ -1 (len avars)) avars) valuation))))
  :hints (("Goal" :in-theory (enable acl2::lookup-eq-lst))))

;; All of the avars (not just the ones corresponding to 1s in c) are constrained to be boolean-valued.
(defthm bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints
  (implies (and (r1cs-constraints-holdp (make-range-check-a-constraints i avars pivars c pivar-renaming) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                ;; this is implied by the pi constraints holding:
                (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) valuation))
                (acl2::bitp (acl2::lookup-eq (nth (+ -1 n) avars) valuation)) ; since some pis may get renamed to this
                ;; the values in the renaming only include certain pivars and a_n-1:
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c)))
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (index-of-lowest-0 c) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (integerp i)
                (< i n)
                (equal n (len avars))
                (equal n (len pivars))
                (symbol-listp avars)
                (symbol-listp pivars)
                (not (intersection-equal avars pivars))
                (no-duplicatesp-equal avars)
                (no-duplicatesp-equal pivars)
                (posp n)
                (natp c)
                (alistp pivar-renaming)
                ;; (subsetp-equal (strip-cdrs pivar-renaming) pivars)
                (symbol-listp (strip-cdrs pivar-renaming))
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                (equal 1 (getbit (+ -1 n) c)) ;; leading 1
                )
           (acl2::bit-listp (acl2::lookup-eq-lst (take (+ 1 i) avars) valuation)))
  :hints (("subgoal *1/2" :cases (;(< i (INDEX-OF-LOWEST-0 C))
                                  (equal i (+ -1 n))
                                  ;; (and (>= i (INDEX-OF-LOWEST-0-AUX 0 C))
                                  ;;      (EQUAL (NTH (BINARY-+ '-1 (LEN AVARS)) AVARS)
                                  ;;                (CDR (ASSOC-EQUAL (NTH (BINARY-+ '1 I) PIVARS)
                                  ;;                                  PIVAR-RENAMING))))
                                  )
           :in-theory (e/d (make-range-check-a-constraints
                            take-opener-alt)
                           (helper2
                            index-of-lowest-0))
           :use (:instance helper2
                           (key (+ 1 I))
                           (val (NTH (+ -1 (LEN AVARS)) AVARS))
                           (alist PIVAR-RENAMING)
                           (vals (PIVARS-FOR-1S PIVARS (+ -2 (LEN AVARS))
                                       (INDEX-OF-LOWEST-0 C)
                                       C)))
           )
          ("Goal" :induct (make-range-check-a-constraints i avars pivars c pivar-renaming)
           :expand ((AVARS-FOR-1S AVARS I C))
           :in-theory (e/d (make-range-check-a-constraints
                            take-opener-alt)
                           (index-of-lowest-0)))))

(defthm bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints-instance
  (implies (and (r1cs-constraints-holdp (make-range-check-a-constraints (+ -1 n) avars pivars c pivar-renaming) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                ;; this is implied by the pi constraints holding:
                (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) valuation))
                (acl2::bitp (acl2::lookup-eq (nth (+ -1 n) avars) valuation)) ; since some pis may get renamed to this
                ;; the values in the renaming only include certain pivars and a_n-1:
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c)))
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (index-of-lowest-0 c) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (equal n (len avars))
                (equal n (len pivars))
                (symbol-listp avars)
                (symbol-listp pivars)
                (not (intersection-equal avars pivars))
                (no-duplicatesp-equal avars)
                (no-duplicatesp-equal pivars)
                (posp n)
                (natp c)
                (alistp pivar-renaming)
                ;; (subsetp-equal (strip-cdrs pivar-renaming) pivars)
                (symbol-listp (strip-cdrs pivar-renaming))
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                (equal 1 (getbit (+ -1 n) c)) ;; leading 1
                )
           (acl2::bit-listp (acl2::lookup-eq-lst (take n avars) valuation)))
  :hints (("Goal" :use (:instance bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints
                                  (i (+ -1 n)))
           :in-theory (disable bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints))))


;; Make constraints checking that the packed AVARS are <= the N-bit constant C
;; and also checking that the AVARS are bits.  The PIVARS are used for helper
;; constraints.  We require that the most significant bit (bit # n-1) of C be
;; 1.  If that is not the case, reduce C and N and call this function on those
;; reduced values.
(defund make-range-check-constraints (avars ; a_0 through a_(n-1)
                                      pivars ; pi_0 through pi_(n-1), possibly not all used
                                      c ; the constant to which the packed AVARS will be compared
                                      n ; the number of bits in c
                                      )
  (declare (xargs :guard (and (symbol-listp avars)
                              (symbol-listp pivars)
                              (no-duplicatesp-eq (append avars pivars))
                              (equal n (len avars))
                              (equal n (len pivars))
                              (posp n)
                              (unsigned-byte-p (len avars) c)
                              (equal 1 (getbit (+ -1 n) c)) ;; leading 1
                              )))
  (b* (((mv pi-constraints pivar-renaming)
        (make-range-check-pi-constraints avars pivars c n))
       (a-constraints (make-range-check-a-constraints (+ -1 n)
                                                      avars
                                                      pivars
                                                      c
                                                      pivar-renaming)))
    (append a-constraints pi-constraints)))

(local (in-theory (disable acl2::bit-listp)))

;; The varables bound by the range-check gadget are all boolean-valued:
(defthm bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-constraints
  (implies (and (r1cs-constraints-holdp (make-range-check-constraints avars pivars c n) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                (equal n (len avars))
                (equal n (len pivars))
                (symbol-listp avars)
                (symbol-listp pivars)
                (not (intersection-equal avars pivars))
                (no-duplicatesp-equal avars)
                (no-duplicatesp-equal pivars)
                (posp n)
                (natp c)
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                (equal 1 (getbit (+ -1 n) c)) ;; leading 1
                )
           (and (acl2::bit-listp (acl2::lookup-eq-lst avars valuation))
                (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) valuation))))
  :hints (("Goal" :use (bit-listp-of-lookup-eq-lst-of-pivars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints
                        (:instance bit-listp-of-lookup-eq-lst-of-avars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-a-constraints
                                   (i (+ -1 n))
                                   (pivar-renaming (MV-NTH 1
                                                          (MAKE-RANGE-CHECK-PI-CONSTRAINTS AVARS PIVARS C (LEN AVARS)))))
                        (:instance bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints-instance
                                  (pivar-renaming (MV-NTH 1
                                                          (MAKE-RANGE-CHECK-PI-CONSTRAINTS AVARS PIVARS C (LEN AVARS))))
                                  ))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (MAKE-RANGE-CHECK-CONSTRAINTS)
                           (;MAKE-RANGE-CHECK-A-CONSTRAINTS-UNROLL
                            bit-listp-of-lookup-eq-lst-when-r1cs-constraints-holdp-of-make-range-check-a-constraints-instance
     ;ACL2::LOOKUP-EQ-LST-UNROLL
                            )))))

;; correctness proof:

(local (include-book "kestrel/arithmetic-light/types" :dir :system))

;; checks that all bits of a, from i down through m, are >= the corresponding
;; bits of c.  Returns a boolean (t or nil).
;; Checks that all bits of a, from n-1 down through m, are >= the corresponding
;; bits of c.  This is PI_m.  Returns a bit (1 or 0).
(defund pi (m c n
              avars ; from a_0 to a_n-1
              valuation prime)
  (declare (xargs :guard (and; (natp m)
                              (natp c)
                              (posp n)
                              (symbol-listp avars)
                              (equal n (len avars))
                              (integerp m)
     ;(< m n)
                              (rtl::primep prime)
                              (r1cs-valuationp valuation prime)
                              (valuation-binds-allp valuation avars))
                  :verify-guards nil ; done below
                  :measure (nfix (+ 1 (- n m)))))
  (if (or (not (natp n))
          (not (natp m))
          (< (+ -1 n) m))
      1
    (acl2::bitand (if (<= (getbit m c)
                          (lookup-eq (nth m avars) valuation))
                      1 0)
                  (pi (+ 1 m) c n avars valuation prime))))

(defthm bitp-of-pi
  (bitp (pi m c n avars valuation prime))
  :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable pi))))

(verify-guards pi :hints (("Goal" :in-theory (enable acl2::rationalp-when-integerp
                                                     INTEGERP-OF-LOOKUP-EQUAL))))


;; Checks whether the values of pi_i down through pi_0 are correct in the valuation.
(defund pivars-correctp (indices
                         valuation
                         avars
                         pivars
                         c
                         n
                         prime)
  (declare (xargs :guard (and (integerp n)
                              (nat-listp indices)
                              (acl2::all-< indices n)
                              (natp c)
                              (posp n)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (equal n (len avars))
                              (rtl::primep prime)
                              (r1cs-valuationp valuation prime)
                              (valuation-binds-allp valuation avars))))
  (if (endp indices)
      t
    (and (let ((index (first indices)))
           (equal (lookup-eq (nth index pivars) valuation)
                  (pi index c n avars valuation prime)))
         (pivars-correctp (rest indices) valuation avars pivars c n prime))))

(defthm pivars-correctp-of-append
  (equal (pivars-correctp (append indices1 indices2) valuation avars pivars c n p)
         (and (pivars-correctp indices1 valuation avars pivars c n p)
              (pivars-correctp indices2 valuation avars pivars c n p)))
  :hints (("Goal" :in-theory (enable pivars-correctp))))

(defthm pivars-correctp-of-cons
  (equal (pivars-correctp (cons index indices) valuation avars pivars c n p)
         (and (equal (lookup-eq (nth index pivars) valuation)
                     (pi index c n avars valuation p))
              (pivars-correctp indices valuation avars pivars c n p)))
  :hints (("Goal" :in-theory (enable pivars-correctp))))

(defthm pivars-correctp-when-not-consp
  (implies (not (consp indices))
           (pivars-correctp indices valuation avars pivars c n p))
  :hints (("Goal" :in-theory (enable pivars-correctp))))

(defund constraints-imply-pivars-correctp (constraints
                                           indices valuation avars
                                           pivars
                                           c
                                           n
                                           p)
  (implies (r1cs-constraints-holdp constraints valuation p)
           (pivars-correctp indices valuation avars pivars c n p)))

(defthm constraints-imply-pivars-correctp-of-append
  (equal (constraints-imply-pivars-correctp constraints
                                            (append indices1 indices2)
                                            valuation avars pivars c n p)
         (and (constraints-imply-pivars-correctp constraints
                                                 indices1
                                                 valuation avars pivars c n p)
              (constraints-imply-pivars-correctp constraints
                                                 indices2
                                                 valuation avars pivars c n p)))
  :hints (("Goal" :in-theory (enable constraints-imply-pivars-correctp))))

(defthm constraints-imply-pivars-correctp-of-cons
  (equal (constraints-imply-pivars-correctp constraints
                                            (cons index indices)
                                            valuation avars pivars c n p)
         (and (implies (r1cs-constraints-holdp constraints valuation p)
                       (equal (lookup-eq (nth index pivars) valuation)
                              (pi index c n avars valuation p)))
              (constraints-imply-pivars-correctp constraints
                                                 indices
                                                 valuation avars pivars c n p)))
  :hints (("Goal" :in-theory (enable constraints-imply-pivars-correctp
                                     pivars-correctp))))

(defthm constraints-imply-pivars-correctp-monotonic
  (implies (and (constraints-imply-pivars-correctp constraints indices valuation avars pivars c n p)
                (subsetp-equal constraints constraints+))
           (constraints-imply-pivars-correctp constraints+ indices valuation avars pivars c n p))
  :hints (("Goal" :in-theory (enable constraints-imply-pivars-correctp))))

(defthm constraints-imply-pivars-correctp-when-not-consp
  (implies (not (consp indices))
           (constraints-imply-pivars-correctp constraints indices valuation avars pivars c n p))
  :hints (("Goal" :in-theory (enable constraints-imply-pivars-correctp))))

(defthm indices-for-1s-split-bottom-index
  (implies (and (equal 1 (getbit low c))
                (integerp high)
                (integerp low)
                (<= low high)
                (natp low))
           (equal (indices-for-1s high low c)
                  (append (indices-for-1s high (+ 1 low) c)
                          (list low))))
  :hints (("Goal" :in-theory (enable indices-for-1s))))

(defthm indices-for-1s-when-low-bit-0
  (implies (and (equal 0 (getbit low c))
                (integerp high)
                (integerp low)
                (<= low high)
                (natp low))
           (equal (indices-for-1s high low c)
                  (indices-for-1s high (+ 1 low) c)))
  :hints (("Goal" :in-theory (enable indices-for-1s))))

(defthmd bitand-cases
  (equal (acl2::bitand x y)
         (if (and (equal (bvchop 1 x) 1)
                  (equal (bvchop 1 y) 1))
             1
           0)))

;; (defthm pi-opener-when-0
;;   (implies (and (equal (getbit m c) 0)
;;                 (natp c)
;;                 (posp n)
;;                 (symbol-listp avars)
;;                 (equal n (len avars))
;;                 (natp m)
;;                 (< m n)
;;                 (rtl::primep prime)
;;                 (r1cs-valuationp valuation prime)
;;                 (valuation-binds-allp valuation avars))
;;            (equal (pi m c n avars valuation p)
;;                   (pi (+ 1 m) c n avars valuation p)))
;;   :hints (("Goal" :in-theory (enable bitand-cases
;;                                      <=-of-0-and-lookup-equal)
;;            :expand (PI M C (LEN AVARS) AVARS VALUATION P)
;;            )))

;; (defthm pi-opener-when-1
;;   (implies (and (equal (getbit m c) 1)
;;                 (natp c)
;;                 (posp n)
;;                 (symbol-listp avars)
;;                 (equal n (len avars))
;;                 (natp m)
;;                 (< m n)
;;                 (rtl::primep prime)
;;                 (r1cs-valuationp valuation prime)
;;                 (valuation-binds-allp valuation avars)
;;                 (acl2::bitp (acl2::lookup-equal (nth m avars) valuation)))
;;            (equal (pi m c n avars valuation p)
;;                   (acl2::bitand (pi (+ 1 m) c n avars valuation p)
;;                                 (lookup-eq (nth m avars) valuation))))
;;   :hints (("Goal" :in-theory (enable bitand-cases
;;                                      <=-of-0-and-lookup-equal)
;;            :expand (pi m c (len avars) avars valuation p)
;;            )))

(defund renaming-correctp (pivar-renaming c n avars valuation p)
  (declare (xargs :guard (and (alistp pivar-renaming)
                              (nat-listp (strip-cars pivar-renaming))
                              (symbol-listp (strip-cdrs pivar-renaming))
                              (natp c)
                              (posp n)
                              (symbol-listp avars)
                              (equal n (len avars))
                              (rtl::primep p)
                              (r1cs-valuationp valuation p)
                              (valuation-binds-allp valuation avars))))
  (if (endp pivar-renaming)
      t
    (let* ((entry (first pivar-renaming))
           (pivar-index (car entry))
           (replacement-var (cdr entry)))
      (and (equal (pi pivar-index c n avars valuation p)
                  (lookup-eq replacement-var valuation))
           (renaming-correctp (rest pivar-renaming) c n avars valuation p)))))

(defthm renaming-correctp-when-not-consp
  (implies (not (consp pivar-renaming))
           (renaming-correctp pivar-renaming c n avars valuation p))
  :hints (("Goal" :in-theory (enable renaming-correctp))))

(defthm renaming-correctp-of-cons
  (equal (renaming-correctp (cons (cons pivar-index replacement-var) pivar-renaming) c n avars valuation p)
         (and (equal (pi pivar-index c n avars valuation p)
                     (lookup-eq replacement-var valuation))
              (renaming-correctp pivar-renaming c n avars valuation p)))
  :hints (("Goal" :in-theory (enable renaming-correctp))))

(defthm lookup-equal-of-cdr-of-assoc-equal-when-renaming-correctp
  (implies (and (renaming-correctp pivar-renaming c n avars valuation p))
           (equal (lookup-equal (cdr (assoc-equal i pivar-renaming)) valuation)
                  (if (member-equal i (strip-cars pivar-renaming))
                      (pi i c n avars valuation p)
                    ;; odd case:
                    (lookup-equal nil valuation))))
  :hints (("Goal" :in-theory (enable renaming-correctp assoc-equal))))


(local
 (defthm equal-of-bitand-and-1-forced
   (implies (and (force (bitp x))
                 (force (bitp y)))
            (equal (equal (acl2::bitand x y) 1)
                   (and (equal x 1)
                        (equal y 1))))))

(local
 (defthm <-when-bitps
   (implies (and (bitp x)
                 (bitp y))
            (equal (< x y)
                   (and (equal x 0)
                        (equal y 1))))
   :hints (("Goal" :in-theory (enable bitp)))))

(local
 (defthm <-of-getbit-when-bitp
   (implies (force (bitp x))
            (equal (< x (getbit n y))
                   (and (equal x 0)
                        (equal (getbit n y) 1))))
   :hints (("Goal" :in-theory (enable bitp)))))

(defthm member-equal-of-strip-cars-helper
  (implies (and (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s high low c))
                               (list val)))
                (natp low)
                (integerp high) ;(natp high)
                (natp i))
           (iff (member-equal i (strip-cars pivar-renaming))
                (or (equal i val)
                    (and (equal 0 (getbit i c))
                         (<= i high)
                         (<= low i))))))

(defthm bitand-helper-1-forced
  (implies (and (not (equal 0 x))
                (force (bitp x))
                (force (bitp y)))
           (equal (acl2::bitand x y)
                  y)))

(defthm pivars-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux
  (implies (and (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                (renaming-correctp pivar-renaming c n avars valuation p)
                ;; the constraints already in the accumulator must be right (but note that
                ;; p_n-1 is handled separately):
                (constraints-imply-pivars-correctp constraints-acc (indices-for-1s (+ -2 n) (+ 1 i) c) valuation avars pivars c n p)
                (integerp i) ;(natp i)
                (<= -1 i)
                (natp tvar)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (<= i (+ -2 n))
                ;; (<= (+ -1 tvar) i)
                (natp c)
                (alistp pivar-renaming)
                (symbol-listp (strip-cdrs pivar-renaming))
                ;; the necessary avars and pivars are bound:
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) tvar c))
                (valuation-binds-allp valuation (strip-cdrs pivar-renaming)) ;drop?
                ;; the renaming has entries for all the right vars so far:
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (+ 1 i) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (+ 1 i) c)))
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           (pivars-correctp (indices-for-1s i tvar c)
                            valuation
                            avars
                            pivars
                            c
                            n
                            p))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
           :expand ((make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
                    (indices-for-1s i tvar c)
                    (pi i c (len avars) avars valuation p))
           :in-theory (e/d ((:i make-range-check-pi-constraints-aux)
                            bitp-of-mul-forced
                            <=-of-0-and-lookup-equal
                            indices-for-0s-of-when-low-bit-is-1)
                           (bitp
                            indices-for-0s-of-+-of-1 ;looped
                            )))))

(defthm pivars-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints
  (implies (and (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints avars pivars c n)) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (posp n)
                (equal n (len avars))
                (equal n (len pivars))
                (natp c)
                ;; the necessary avars and pivars are bound:
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           (pivars-correctp (indices-for-1s (+ -2 n) (index-of-lowest-0 c) c)
                            valuation
                            avars
                            pivars
                            c
                            n
                            p))
  :hints (("Goal"
           :cases ((bitp (LOOKUP-EQUAL (NTH (+ -1 (LEN AVARS)) AVARS) VALUATION)))
           :use (:instance PIVARS-CORRECTP-WHEN-R1CS-CONSTRAINTS-HOLDP-OF-MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX
                           (constraints-acc nil)
                           (tvar (index-of-lowest-0 c))
                           (i (+ -2 n))
                           (pivar-renaming (acons (+ -1 n)
                                                         (nth (+ -1 n) avars)
                                                         nil)))
           :in-theory (e/d (make-range-check-pi-constraints pi INDICES-FOR-0S INDICES-FOR-1S)
                           (PIVARS-CORRECTP-WHEN-R1CS-CONSTRAINTS-HOLDP-OF-MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX)))))

(defthm helper-better
  (implies (and (subsetp-equal (strip-cdrs alist) (cons val vals))
                (not (equal val (cdr (assoc-equal key alist))))
                )
           (iff (member-equal (cdr (assoc-equal key alist)) vals)
                (if (assoc-equal key alist)
                    t
                  (member-equal nil vals))))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

(defthm renaming-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux
  (implies (and (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                (renaming-correctp pivar-renaming c n avars valuation p)
                ;; the constraints already in the accumulator must be right (but note that
                ;; p_n-1 is handled separately):
                (constraints-imply-pivars-correctp constraints-acc (indices-for-1s (+ -2 n) (+ 1 i) c) valuation avars pivars c n p)
                (integerp i) ;(natp i)
                (<= -1 i)
                (natp tvar)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (<= i (+ -2 n))
                ;; (<= (+ -1 tvar) i)
                (natp c)
                (alistp pivar-renaming)
                (symbol-listp (strip-cdrs pivar-renaming))
                ;; ;; the necessary avars and pivars are bound:
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) tvar c))
                (valuation-binds-allp valuation (strip-cdrs pivar-renaming)) ;drop?
                ;; the renaming has entries for all the right vars so far:
                (equal (strip-cars pivar-renaming)
                       (append (acl2::reverse-list (indices-for-0s (+ -2 n) (+ 1 i) c))
                               (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
                               ))
                (subsetp-equal (strip-cdrs pivar-renaming)
                               (cons (nth (+ -1 n) avars)
                                     (pivars-for-1s pivars (+ -2 n) (+ 1 i) c)))
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           (renaming-correctp (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming))
                              c n avars valuation p))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
           :expand ((make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pivar-renaming)
                    (indices-for-1s i tvar c)
                    (pi i c (len avars) avars valuation p))
           :in-theory (e/d ((:i make-range-check-pi-constraints-aux)
                            bitp-of-mul-forced
                            <=-of-0-and-lookup-equal
                            indices-for-0s-of-when-low-bit-is-1
                            natp)
                           (bitp
                            indices-for-0s-of-+-of-1 ;looped
                            pivars-for-1s-of-+-of-1-when-low-bit-is-1 ;looped
                            )))))

(defthm renaming-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints
  (implies (and (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints avars pivars c n)) valuation p)
                (r1cs-valuationp valuation p)
                (rtl::primep p)
                (symbol-listp avars)
                (symbol-listp pivars)
                (no-duplicatesp-equal pivars)
                (no-duplicatesp-equal avars)
                (equal n (len avars))
                (equal n (len pivars))
                (posp n)
                (natp c)
                ;; ;; the necessary avars and pivars are bound:
                (valuation-binds-allp valuation avars)
                (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
                (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars (+ -1 n) c) valuation)) ; proved elsewhere
                (equal 1 (getbit (+ -1 n) c)) ;leading 1
                )
           (renaming-correctp (mv-nth 1 (make-range-check-pi-constraints avars pivars c n)) c n avars valuation p))
  :hints (("Goal"
           :cases ((bitp (LOOKUP-EQUAL (NTH (+ -1 (LEN AVARS)) AVARS) VALUATION)))
           :use (:instance renaming-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux
                           (constraints-acc nil)
                           (tvar (index-of-lowest-0 c))
                           (i (+ -2 n))
                           (pivar-renaming (acons (+ -1 n)
                                                  (nth (+ -1 n) avars)
                                                  nil)))
           :in-theory (e/d (make-range-check-pi-constraints pi INDICES-FOR-0S INDICES-FOR-1S)
                           (renaming-correctp-when-r1cs-constraints-holdp-of-make-range-check-pi-constraints-aux)))))


;;maybe move these up:

(include-book "kestrel/bv-lists/packbv" :dir :system)

;; (defthm make-range-check-a-constraints-is-correct
;;   (implies (and (r1cs-constraints-holdp (make-range-check-a-constraints i avars pivars c pivar-renaming) valuation p)
;;                 (r1cs-valuationp valuation p)
;;                 (rtl::primep p)
;;                 ;; All of the pivars are correct:
;;                 (pivars-correctp (indices-for-1s (+ -2 n) (index-of-lowest-0 c) c) valuation avars pivars c n p)
;;                 ;; ;; this is implied by the pi constraints holding:
;;                 ;; (acl2::bit-listp (acl2::lookup-eq-lst (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) valuation))
;;                 ;; (acl2::bitp (acl2::lookup-eq (nth (+ -1 n) avars) valuation)) ; since some pis may get renamed to this
;;                 ;; the values in the renaming only include certain pivars and a_n-1:
;;                 (subsetp-equal (strip-cdrs pivar-renaming)
;;                                (cons (nth (+ -1 n) avars)
;;                                      (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c)))
;;                 (equal (strip-cars pivar-renaming)
;;                        (append (acl2::reverse-list (indices-for-0s (+ -2 n) (index-of-lowest-0 c) c))
;;                                (list (+ -1 n)) ;since we start by setting pi_n-1 to be a_n-1
;;                                ))
;;                 (integerp i)
;;                 (<= -i i)
;;                 (< i n)
;;                 (equal n (len avars))
;;                 (equal n (len pivars))
;;                 (symbol-listp avars)
;;                 (symbol-listp pivars)
;;                 (not (intersection-equal avars pivars))
;;                 (no-duplicatesp-equal avars)
;;                 (no-duplicatesp-equal pivars)
;;                 (posp n)
;;                 (natp c)
;;                 (alistp pivar-renaming)
;;                 (renaming-correctp pivar-renaming c n avars valuation p)
;;                 (valuation-binds-allp valuation avars)
;;                 (valuation-binds-allp valuation (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c))
;;                 (equal 1 (getbit (+ -1 n) c)) ;; leading 1
;;                 )
;;            (<= (acl2::packbv (+ 1 i) 1 (acl2::lookup-eq-lst (take (+ 1 i) avars) valuation))
;;                c))
;;   :hints (("subgoal *1/2" :cases ( ;(< i (INDEX-OF-LOWEST-0 C))
;;                                   (equal i (+ -1 n))
;;                                   ;; (and (>= i (INDEX-OF-LOWEST-0-AUX 0 C))
;;                                   ;;      (EQUAL (NTH (BINARY-+ '-1 (LEN AVARS)) AVARS)
;;                                   ;;                (CDR (ASSOC-EQUAL (NTH (BINARY-+ '1 I) PIVARS)
;;                                   ;;                                  PIVAR-RENAMING))))
;;                                   )
;;            :in-theory (e/d (make-range-check-a-constraints
;;                             take-opener-alt)
;;                            (helper2
;;                             index-of-lowest-0))
;;            :use (:instance helper2
;;                            (key (+ 1 I))
;;                            (val (NTH (+ -1 (LEN AVARS)) AVARS))
;;                            (alist PIVAR-RENAMING)
;;                            (vals (PIVARS-FOR-1S PIVARS (+ -2 (LEN AVARS))
;;                                                 (INDEX-OF-LOWEST-0 C)
;;                                                 C)))
;;            )
;;           ("Goal" :induct (make-range-check-a-constraints i avars pivars c pivar-renaming)
;;            :expand ((AVARS-FOR-1S AVARS I C))
;;            :in-theory (e/d (make-range-check-a-constraints
;;                             take-opener-alt)
;;                            (index-of-lowest-0)))))
