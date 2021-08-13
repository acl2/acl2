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
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

(in-theory (disable rtl::primep)) ;todo

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

(defthm make-product-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation a)
                (valuation-bindsp valuation b)
                (valuation-bindsp valuation c)
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

;; Returns (mv constraints pi-var-renaming), where the constraints added to
;; CONSTRAINTS-ACC assert that all of the (bit) values of the avars, from a_i
;; down through a_tvar, are at least as big as the corresponding bits of c.
(defund make-pi-constraints (i ; index of the next bit to check, counts down
                             tvar ; lowest index to check (can't just call this "t", hence "tvar")
                             avars  ; a_0 through a_(n-1)
                             pivars ; pi_0 through pi_(n-1)
                             c ; the constant to which we are comparing the (packed) AVARS
                             constraints-acc
                             pi-var-renaming ; maps pivars to equivalent, higher-numbered pivars (the keys may include any vars above pi_i)
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
                              (symbol-alistp pi-var-renaming)
                              (subsetp-equal (strip-cdrs pi-var-renaming) pivars))
                  :measure (nfix (+ 1 (- i t)))))
  (if (or (not (mbt (natp tvar)))
          (not (mbt (integerp i)))
          (< i tvar))
      (mv constraints-acc pi-var-renaming)
    (let* ((c_i (getbit i c))
           (pi_i (nth i pivars))
           (pi_i+1 (nth (+ 1 i) pivars))
           ;; possibly rename pi_i+1 to some higher var:
           (pi_i+1 (let ((res (assoc-eq pi_i+1 pi-var-renaming)))
                     (if res
                         (cdr res)
                       pi_i+1))))
      (if (equal c_i 0)
          (make-pi-constraints (+ -1 i) tvar avars pivars c
                               ;; no actual constraint added:
                               constraints-acc
                               ;; records the fact that pi_i is just pi_i+1
                               ;; (but pi_i+1 may have been equated to some
                               ;; higher numbered pi var -- see above):
                               (acons pi_i pi_i+1 pi-var-renaming)
                               )
        (let ((a_i (nth i avars)))
          (make-pi-constraints (+ -1 i) tvar avars pivars c
                               ;; Add the constraint that pi_i+1 * a_i = pi_i
                               ;; That is, pi_i ("all the a's down through a_i
                               ;; are >= the corresponding c's") iff both p_i+1
                               ;; ("all the a's down through a_i+1 are >= the
                               ;; corresponding c's") AND a_i is >= c_i (note
                               ;; that c_i here is known to be 1, so a_i must
                               ;; also be 1 if it is to be >= c_i).
                               (cons (make-product-constraint pi_i+1 a_i pi_i) constraints-acc)
                               pi-var-renaming))))))

;; (make-pi-constraints 12 ; bit 13 is handled separately
;;                      4
;;                      '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
;;                      '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 pi8 pi9 pi10 pi11 pi12 pi13)
;;                      #b11100011001111
;;                      nil
;;                      nil)

(defthm symbol-alistp-of-mv-nth-1-of-make-pi-constraints
  (implies (and (symbol-alistp pi-var-renaming)
                (symbol-listp pivars))
           (symbol-alistp (mv-nth 1 (make-pi-constraints i tvar avars pivars c constraints-acc pi-var-renaming))))
  :hints (("Goal" :in-theory (enable make-pi-constraints))))

(defthm subsetp-equal-of-strip-cdrs-of-mv-nth-1-of-make-pi-constraints
  (implies (and (symbol-alistp pi-var-renaming)
                (symbol-listp pivars)
                (subsetp-equal (strip-cdrs pi-var-renaming) pivars)
                (< i (+ -1 (len avars)))
                (equal (len avars)
                       (len pivars)))
           (subsetp-equal (strip-cdrs (mv-nth 1 (make-pi-constraints i tvar avars pivars c constraints-acc pi-var-renaming)))
                          pivars))
  :hints (("Goal" :in-theory (enable make-pi-constraints))))



;; zz
;; (defthm make-pi-constraint-correct
;;   (implies (and (r1cs-valuationp valuation p)
;;                 (valuation-bindsp valuation a)
;;                 (valuation-bindsp valuation b)
;;                 (valuation-bindsp valuation c)
;;                 ;; (bitp (lookup-eq a valuation))
;;                 ;; (bitp (lookup-eq b valuation))
;;                 (rtl::primep p)
;;                 (< 2 p))
;;            (equal (r1cs-constraints-holdp (make-pi-constraints i
;;                                                                avars
;;                                                                pivars
;;                                                                c
;;                                                                pi-var-renaming)
;;                                           valuation p)
;;                   ..
;;                   (equal (lookup-eq c valuation)
;;                          (acl2::bitxor (lookup-eq a valuation)
;;                                        (lookup-eq b valuation)))))
;;   :hints (("Goal" :in-theory (enable make-bitxor-constraint
;;                                      r1cs-constraint-holdsp
;;                                      integerp-of-lookup-equal
;;                                      acl2-numberp-of-lookup-equal))))

(defthmd <-of-integer-length-when-equal-of-getbit-and-1
  (implies (and (equal (getbit n x) 1)
                (natp x)
                (natp n))
           (< n (integer-length x)))
  :hints (("Goal" :in-theory (e/d (integer-length getbit)
                                  (acl2::bvchop-1-becomes-getbit
                                   acl2::slice-becomes-getbit)))))

(defund index-of-lowest-0 (i x)
  (declare (xargs :guard (and (natp x)
                              (natp i))
                  :measure (nfix (+ 1 (- (+ 1 (integer-length x)) i)))
                  :hints (("Goal" :use (:instance <-of-integer-length-when-equal-of-getbit-and-1
                                                  (n i))))))
  (if (or (not (mbt (integerp i)))
          (not (mbt (natp x)))
          (equal 0 (getbit i x)))
      i
    (index-of-lowest-0 (+ 1 i) x)))

;; (index-of-lowest-0 0 7)

(defthm index-of-lowest-0-linear
  (implies (natp i)
           (<= i (index-of-lowest-0 i x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable index-of-lowest-0))))

(defund make-range-check-a-constraint (a_i pi_i+1)
  (declare (xargs :guard (and (symbolp a_i)
                              (symbolp pi_i+1))))
  (r1cs-constraint (list `(1 1)
                         `(-1 ,pi_i+1)
                         `(-1 ,a_i))
                   (list `(1 ,a_i))
                   (list) ; 0
                   ))

(defthm make-range-check-a-constraint-correct
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation a_i)
                (valuation-bindsp valuation pi_i+1)
                (rtl::primep prime))
           (equal (r1cs-constraint-holdsp (make-range-check-a-constraint a_i pi_i+1) valuation prime)
                  (equal (mul (add 1
                                   (add (neg (lookup-equal pi_i+1 valuation) prime)
                                        (neg (lookup-equal a_i valuation) prime)
                                        prime)
                                   prime)
                              (lookup-equal a_i valuation)
                              prime)
                         0)))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraint
                                     r1cs-constraint-holdsp
                                     dot-product
                                     integerp-of-lookup-equal
                                     pfield::mul-of--1-becomes-neg))))

(defund make-range-check-a-constraints (i
                                        avars
                                        pivars
                                        c
                                        acc
                                        pi-var-renaming)
  (declare (xargs :guard (and (integerp i)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (natp c)
                              (symbol-alistp pi-var-renaming)
                              (subsetp-equal (strip-cdrs pi-var-renaming) pivars))
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      acc
    (let* ((c_i (getbit i c))
           (a_i (nth i avars))
           (pi_i+1 (nth (+ 1 i) pivars))
           (pi_i+1 (let ((res (assoc-eq pi_i+1 pi-var-renaming)))
                     (if res
                         (cdr res)
                       pi_i+1))))
      (make-range-check-a-constraints (+ -1 i)
                                      avars
                                      pivars
                                      c
                                      (cons
                                       (if (equal c_i 0)
                                           (make-range-check-a-constraint a_i pi_i+1)
                                         (make-boolean-constraint a_i))
                                       acc)
                                      pi-var-renaming))))

(defthm true-listp-of-make-range-check-a-constraints
  (equal (true-listp (make-range-check-a-constraints i avars pivars c acc pi-var-renaming))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraints))))


;; Make constraints checking that the packed AVARS are <= the N-bit constant C
;; and also checking that the AVARS are bits.  The PIVARS are used for helper
;; constraints.
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
                              ;; (posp c) ; if c=0 there would be no leading 1
                              )))
  (b* (;; reduce n if necessary so that c_(n-1) is the leading 1:
       ;;(n (+ 1 position-of-leading-1))
       (pi_n-1 (nth (+ -1 n) pivars))
       (a_n-1 (nth (+ -1 n) avars))
       (tvar (index-of-lowest-0 0 c))
       ((mv pi-constraints pi-var-renaming)
        (make-pi-constraints (+ -2 n)
                             tvar
                             avars
                             pivars
                             c
                             (list (make-equality-constraint pi_n-1 a_n-1) ; constraint for position n-1
                                   )
                             nil))
       (a-constraints (make-range-check-a-constraints (+ -1 n)
                                          avars
                                          pivars
                                          c
                                          nil
                                          pi-var-renaming)))
    (append a-constraints pi-constraints)))

;; (make-range-check-constraints
;;  '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
;;  '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 pi8 pi9 pi10 pi11 pi12 pi13)
;;  #b11100011001111)

(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)

(include-book "kestrel/utilities/defopeners" :dir :system)


(acl2::defopeners ACL2::REVERSE-LIST)

(acl2::defopeners MAKE-RANGE-CHECK-A-CONSTRAINTS)

(acl2::defopeners MAKE-PI-CONSTRAINTS)

(acl2::defopeners ACL2::LOOKUP-EQ-LST)

(defthm pfield::add-of-+-of-p-arg1-arg2
  (implies (integerp x)
           (equal (add (+ x p) y p)
                  (add x y p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm not-equal-of-nth-and-nth-when-no-duplicatesp-equal
  (implies (and (no-duplicatesp-equal x)
                (not (equal n1 n2))
                (natp n1)
                (< n1 (len x))
                (natp n2)
                (< n2 (len x)))
           (not (equal (nth n1 x) (nth n2 x))))
  :hints (("Goal" :in-theory (e/d (no-duplicatesp-equal
                                   nth
                                   ) (acl2::nth-of-cdr)))))

;; prove it for a special case:
(thm
 (let ((n 4)
       (c #b1010 ;must have a leading 1
          )
       )
   (implies (and (natp prime)
                 (< 1000000 prime)
                 (rtl::primep prime)
                 (r1cs-valuationp valuation prime)
                 (equal n (len avars))
                 (equal n (len pivars))
                 (valuation-binds-allp valuation (append avars pivars))
                 (no-duplicatesp-eq (append avars pivars))
                 (equal 1 (getbit (+ -1 n) c)) ; constant must have a leading 1
                 )
            ;; todo: prove other direction!
            (implies (r1cs-constraints-holdp (make-range-check-constraints
                                              avars
                                              pivars
                                              c
                                              n
                                              )
                                             valuation
                                             prime)
                     (and (ACL2::ALL-UNSIGNED-BYTE-P 1 (acl2::lookup-eq-lst avars valuation))
                          (<= (acl2::packbv n ;14
                                            1
                                            (acl2::lookup-eq-lst (acl2::reverse-list avars) valuation))
                              c)))))
 :hints (("Goal" :in-theory (e/d (ACL2::LOOKUP-EQ-LST
                                  ;; R1CS-CONSTRAINT-HOLDSP
                                  DOT-PRODUCT
                                  INTEGERP-OF-LOOKUP-EQUAL
                                  ACL2::CONSP-OF-CDR
                                  acl2::car-becomes-nth-of-0
                                  ;;MAKE-PRODUCT-CONSTRAINT
                                  MAKE-RANGE-CHECK-CONSTRAINTS
                                  )
                                 (PFIELD::MUL-OF-ADD-ARG1
                                  PFIELD::MUL-OF-ADD-ARG2)))))
