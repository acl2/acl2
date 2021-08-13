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
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/bv-lists/bit-listp-rules" :dir :system))

(in-theory (disable rtl::primep)) ;todo

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

;; Returns (mv constraints pi-var-renaming), where the constraints added to
;; CONSTRAINTS-ACC assert that all of the (bit) values of the avars, from a_i
;; down through a_tvar, are at least as big as the corresponding bits of c.
(defund make-range-check-pi-constraints-aux (i ; index of the next bit to check, counts down
                                             tvar ; lowest index to check (can't just call this "t", hence "tvar")
                                             avars ; a_0 through a_(n-1)
                                             pivars ; pi_0 through pi_(n-1)
                                             c ; the constant to which we are comparing the (packed) AVARS
                                             constraints-acc
                                             pi-var-renaming ; maps pivars to equivalent, higher-numbered pivars and/or to a_n-1 -- or this could map indices...
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
                              ;;(subsetp-equal (strip-cdrs pi-var-renaming) (cons a_n-1 pivars))
                              (symbol-listp (strip-cdrs pi-var-renaming)))
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
          (make-range-check-pi-constraints-aux (+ -1 i) tvar avars pivars c
                                               ;; no actual constraint added:
                                               constraints-acc
                                               ;; records the fact that pi_i is just pi_i+1
                                               ;; (but pi_i+1 may have been equated to some
                                               ;; higher numbered pi var -- see above):
                                               (acons pi_i pi_i+1 pi-var-renaming))
        (let ((a_i (nth i avars)))
          (make-range-check-pi-constraints-aux (+ -1 i) tvar avars pivars c
                                               ;; Add the constraint that pi_i+1 * a_i = pi_i
                                               ;; That is, pi_i ("all the a's down through a_i
                                               ;; are >= the corresponding c's") iff both p_i+1
                                               ;; ("all the a's down through a_i+1 are >= the
                                               ;; corresponding c's") AND a_i is >= c_i (note
                                               ;; that c_i here is known to be 1, so a_i must
                                               ;; also be 1 if it is to be >= c_i).
                                               (cons (make-product-constraint pi_i+1 a_i pi_i) constraints-acc)
                                               pi-var-renaming))))))

;; (make-range-check-pi-constraints-aux 12 ; bit 13 is handled separately
;;                      4
;;                      '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
;;                      '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 pi8 pi9 pi10 pi11 pi12 pi13)
;;                      #b11100011001111
;;                      nil
;;                      nil)

(defthm r1cs-constraint-listp-of-mv-nth-0-of-make-range-check-pi-constraints-aux
  (implies (and (symbol-alistp pi-var-renaming)
                (symbol-listp pivars)
                (symbol-listp avars)
                (natp tvar)
                (natp i)
                (equal (len avars)
                       (len pivars))
                (< (+ 1 i) (len pivars))
                (r1cs-constraint-listp constraints-acc)
                (symbol-listp (strip-cdrs pi-var-renaming)))
           (r1cs-constraint-listp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pi-var-renaming))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm symbol-alistp-of-mv-nth-1-of-make-range-check-pi-constraints-aux
  (implies (and (symbol-alistp pi-var-renaming)
                (symbol-listp pivars))
           (symbol-alistp (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pi-var-renaming))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

;; (defthm subsetp-equal-of-strip-cdrs-of-mv-nth-1-of-make-range-check-pi-constraints-aux
;;   (implies (and (symbol-alistp pi-var-renaming)
;;                 (symbol-listp pivars)
;;                 (subsetp-equal (strip-cdrs pi-var-renaming) pivars)
;;                 (< i (+ -1 (len avars)))
;;                 (equal (len avars)
;;                        (len pivars)))
;;            (subsetp-equal (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pi-var-renaming)))
;;                           pivars))
;;   :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

(defthm symbol-listp-of-strip-cdrs-of-mv-nth-1-of-make-range-check-pi-constraints-aux
  (implies (and (symbol-alistp pi-var-renaming)
                (symbol-listp pivars)
                (symbol-listp (strip-cdrs pi-var-renaming))
;;                (< i (+ -1 (len avars)))
                ;; (equal (len avars)
                ;;        (len pivars))
                )
           (symbol-listp (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pi-var-renaming)))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints-aux))))

;; (thm
;;  (implies (and (r1cs-valuationp valuation p)
;;                (rtl::primep p)
;;                (r1cs-constraints-holdp (mv-nth 0 (make-range-check-pi-constraints-aux i tvar avars pivars c constraints-acc pi-var-renaming))
;;                                        valuation)


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
  (let* ((pi_n-1 (nth (+ -1 n) pivars))
         (a_n-1 (nth (+ -1 n) avars))
         (tvar (index-of-lowest-0 0 c)))
    (make-range-check-pi-constraints-aux (+ -2 n)
                                         tvar
                                         avars
                                         pivars
                                         c
                                         nil
                                         ;; Let pi_n-1 = a_n-1.  Note that this is not a
                                         ;; constraint:
                                         (acons pi_n-1 a_n-1 nil))))

;; test:
;; (make-range-check-pi-constraints '(a0 a1 a2 a3 a4 a5 a6 a7)
;;                                  '(pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7)
;;                                  #b10001110 ; leading 1, as required
;;                                  8)

(defthm symbol-alistp-of-mv-nth-1-of-make-range-check-pi-constraints
  (implies (symbol-listp pivars)
           (symbol-alistp (mv-nth 1 (make-range-check-pi-constraints avars pivars c n))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints))))

(defthm symbol-listp-of-strip-cdrs-of-mv-nth-1-of-make-range-check-pi-constraints
  (implies (and (symbol-listp pivars)
                (symbol-listp avars))
           (symbol-listp (strip-cdrs (mv-nth 1 (make-range-check-pi-constraints avars pivars c n)))))
  :hints (("Goal" :in-theory (enable make-range-check-pi-constraints))))


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
;;            (equal (r1cs-constraints-holdp (make-range-check-pi-constraints-aux i
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

;; Returns a list of constraints
(defund make-range-check-a-constraints (i
                                        avars
                                        pivars
                                        c
                                        pi-var-renaming)
  (declare (xargs :guard (and (integerp i)
                              (symbol-listp avars)
                              (symbol-listp pivars)
                              (natp c)
                              (symbol-alistp pi-var-renaming)
                              ;; (subsetp-equal (strip-cdrs pi-var-renaming) pivars)
                              (symbol-listp (strip-cdrs pi-var-renaming)))
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
                       (pi_i+1 (let ((res (assoc-eq pi_i+1 pi-var-renaming)))
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
                                            pi-var-renaming)))))

(defthm r1cs-constraint-listp-of-make-range-check-a-constraints
  (implies (and (integerp i)
                (symbol-listp avars)
                (symbol-listp pivars)
                (natp c)
                (symbol-alistp pi-var-renaming)
                ;; (subsetp-equal (strip-cdrs pi-var-renaming) pivars)
                (symbol-listp (strip-cdrs pi-var-renaming)))
           (r1cs-constraint-listp (make-range-check-a-constraints i avars pivars c pi-var-renaming)))
  :hints (("Goal" :in-theory (enable make-range-check-a-constraints))))

;; Find the avars from a_i down to a_0 that correspond to 1 bits in c
(local
 (defun avars-for-1s (avars i c)
   (declare (xargs :guard (and (integerp i)
                               (symbol-listp avars)
                               (natp c))
                   :measure (nfix (+ 1 (- i t)))))
   (if (not (natp i))
       nil
     (if (equal 1 (getbit i c)) ;if c_i = 1
         (cons (nth i avars)
               (avars-for-1s avars (+ -1 i) c))
       (avars-for-1s avars (+ -1 i) c)))))

;; All of the avars that correspond to 1s in c are constrained to be boolean-valued.
(local
 (defthm bit-listp-of-lookup-eq-lst-of-avars-for-1s-when-r1cs-constraints-holdp-of-make-range-check-a-constraints
   (implies (and (r1cs-valuationp valuation p)
                 (rtl::primep p)
                 (r1cs-constraints-holdp (make-range-check-a-constraints i avars pivars c pi-var-renaming) valuation p)
                 (integerp i)
                 (symbol-listp avars)
                 (symbol-listp pivars)
                 (natp c)
                 (symbol-alistp pi-var-renaming)
                 ;; (subsetp-equal (strip-cdrs pi-var-renaming) pivars)
                 (symbol-listp (strip-cdrs pi-var-renaming))
                 (valuation-binds-allp valuation (avars-for-1s avars i c)))
            (acl2::bit-listp (acl2::lookup-eq-lst (avars-for-1s avars i c) valuation)))
   :hints (("Goal" :in-theory (e/d (make-range-check-a-constraints) (bitp))))))

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
  (b* (((mv pi-constraints pi-var-renaming)
        (make-range-check-pi-constraints avars pivars c n))
       (a-constraints (make-range-check-a-constraints (+ -1 n)
                                                      avars
                                                      pivars
                                                      c
                                                      pi-var-renaming)))
    (append a-constraints pi-constraints)))





;; Proof (for one input):

(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)

(acl2::defopeners ACL2::REVERSE-LIST)

(acl2::defopeners MAKE-RANGE-CHECK-A-CONSTRAINTS)

(acl2::defopeners MAKE-RANGE-CHECK-PI-CONSTRAINTS-AUX)

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
                                  MAKE-RANGE-CHECK-PI-CONSTRAINTS
                                  )
                                 (PFIELD::MUL-OF-ADD-ARG1
                                  PFIELD::MUL-OF-ADD-ARG2)))))
