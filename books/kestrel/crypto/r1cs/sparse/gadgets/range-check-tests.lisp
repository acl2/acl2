(in-package "R1CS")

(include-book "range-check")

;; Test/proof (for one input):

(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
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

(acl2::defopeners acl2::reverse-list)

(acl2::defopeners make-range-check-a-constraints)

(acl2::defopeners make-range-check-pi-constraints-aux)

(acl2::defopeners acl2::lookup-eq-lst)

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

;; (make-range-check-constraints '(a0 a1 a2 a3)
;;                               '(pi0 pi1 pi2 pi3)
;;                               #b1010
;;                               4)

;; The pivars that get constraints are (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c).

;; prove it for a special case:
(thm
 (let ((n 4)
       (c #b1010 ;must have a leading 1
          ))
   (implies (and (natp prime)
                 (< 1000000 prime)
                 (rtl::primep prime)
                 (r1cs-valuationp valuation prime)
                 (equal n (len avars))
                 (equal n (len pivars))
                 (valuation-binds-allp valuation (append avars
                                                         (pivars-for-1s pivars (+ -2 n) (index-of-lowest-0 c) c) pivars))
                 (no-duplicatesp-eq (append avars pivars))
                 (equal 1 (getbit (+ -1 n) c)) ; constant must have a leading 1
                 )
            ;; todo: prove other direction!
            (implies (r1cs-constraints-holdp (make-range-check-constraints avars
                                                                           pivars
                                                                           c
                                                                           n)
                                             valuation
                                             prime)
                     (and (acl2::all-unsigned-byte-p 1 (acl2::lookup-eq-lst avars valuation))
                          (<= (acl2::packbv n ;14
                                            1
                                            (acl2::lookup-eq-lst (acl2::reverse-list avars) valuation))
                              c)))))
 :otf-flg t
 :hints (("Goal" :in-theory (e/d (ACL2::LOOKUP-EQ-LST
                                  ;; R1CS-CONSTRAINT-HOLDSP
                                  DOT-PRODUCT
                                  INTEGERP-OF-LOOKUP-EQUAL
                                  ACL2::CONSP-OF-CDR
                                  acl2::car-becomes-nth-of-0
                                  ;;MAKE-PRODUCT-CONSTRAINT
                                  MAKE-RANGE-CHECK-CONSTRAINTS
                                  MAKE-RANGE-CHECK-PI-CONSTRAINTS
                                  ASSOC-EQUAL
                                  ACL2::PACKBV-OPENER
                                  bitp
                                  )
                                 (PFIELD::MUL-OF-ADD-ARG1
                                  PFIELD::MUL-OF-ADD-ARG2
                                  INTERSECTION-EQUAL)))))
