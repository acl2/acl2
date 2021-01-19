; An R1CS gadget for bit packing/unpacking
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv-lists/packbv-def" :dir :system)
(include-book "kestrel/typed-lists-light/bit-listp" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-lst" :dir :system)
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/crypto/r1cs/sparse/rules" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/bv-lists/packbv" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

;; Helper function
(defund make-packing-constraint-aux (bit-vars bit-position p)
  (declare (xargs :guard (and (symbol-listp bit-vars)
                              (natp bit-position)
                              (posp p))))
  (if (endp bit-vars)
      nil
    (let ((bit-var (first bit-vars))
          ;; When packing small values (relative to p), the mod is unnecessary:
          (coefficient (mod (expt 2 bit-position) p)))
      (cons (list coefficient bit-var)
            (make-packing-constraint-aux (rest bit-vars) (+ 1 bit-position) p)))))

(defthm sparse-vectorp-of-make-packing-constraint-aux
  (implies (and (symbol-listp bit-vars)
                (natp bit-position)
                (posp p))
           (sparse-vectorp (make-packing-constraint-aux bit-vars bit-position p)))
  :hints (("Goal" :in-theory (enable make-packing-constraint-aux))))

;; Make an R1CS constraint (in sparse form) that asserts that A is equal to the
;; packed version of the BIT-VARS (modulo the prime).  The bit-vars are given
;; least-significant bit first and should be separately constrained to be bits.
;; The constraint has the form: sum(0,n-1,bit-var_i*2_i(mod p))(1) = a.  Note
;; that if not enough BIT-VARS are supplied to hold a particular value of A,
;; the constraint will just be false. TODO: Consider making a variant that
;; doesn't take the prime P as an argument.
(defund make-packing-constraint (a bit-vars p)
  (declare (xargs :guard (and (symbolp a)
                              (symbol-listp bit-vars)
                              (posp p))))
  (r1cs-constraint (make-packing-constraint-aux bit-vars 0 p) ;; a vector
                   (list `(1 1))    ;; b vector (just 1)
                   (list `(1 ,a))   ;; c vector (just A)
                   ))

(defthm r1cs-constraintp-of-make-packing-constraint
  (implies (and (symbolp a)
                (symbol-listp bit-vars)
                (posp p))
           (r1cs::r1cs-constraintp (make-packing-constraint a bit-vars p)))
  :hints (("Goal" :in-theory (enable make-packing-constraint))))

(defthm mod-of-dot-product-of-make-packing-constraint-aux
  (implies (and (symbol-listp bit-vars)
                (r1cs-valuationp valuation p)
                (valuation-binds-allp valuation bit-vars)
                (acl2::bit-listp (acl2::lookup-eq-lst bit-vars valuation))
                (posp p)
                (natp bit-position))
           (equal (mod (dot-product (make-packing-constraint-aux bit-vars bit-position p) valuation p)
                       p)
                  (mod (* (expt 2 bit-position)
                          (acl2::packbv (len bit-vars) 1 (acl2::reverse-list (acl2::lookup-eq-lst bit-vars valuation))))
                       p)))
  :hints (("Goal" ;:expand ((acl2::packbv (len bit-vars) 1 (acl2::reverse-list bit-vars)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (make-packing-constraint-aux ;acl2::packbv
                            acl2::packbv-opener-alt
                            acl2::bvcat acl2::logapp
                            add
                            acl2::expt-of-+
                            valuation-binds-allp)
                           (pfield::add-of-0-arg1-gen)))))

(local
 (defthm lookup-eq-lst-of-reverse-list
   (equal (acl2::lookup-eq-lst (acl2::reverse-list keys) alist)
          (acl2::reverse-list (acl2::lookup-eq-lst keys alist)))
   :hints (("Goal" :in-theory (enable acl2::lookup-eq-lst acl2::reverse-list)))))

;; Prove that, if we make a packing constraint for some variable A and bit
;; variables BIT-VARS, then the constraint holds over a valuation (that binds
;; the vars) iff the value of A is equal to the result of packing the BIT-VARS
;; (modulo p). The values of the BIT-VARS in the valuation must be bits.
(defthm make-packing-constraint-correct
  (implies (and (symbolp a)
                (symbol-listp bit-vars)
                (r1cs-valuationp valuation p)
                (valuation-bindsp valuation a)
                (valuation-binds-allp valuation bit-vars)
                (acl2::bit-listp (acl2::lookup-eq-lst bit-vars valuation))
                (natp p)
                (< 1 p))
           (equal (r1cs-constraint-holdsp (make-packing-constraint a bit-vars p) valuation p)
                  (equal (lookup-eq a valuation)
                         ;; The mod here will often be droppable:
                         (mod (acl2::packbv (len bit-vars)
                                            1
                                            ;; Must reverse since packbv is big-endian:
                                            (acl2::lookup-eq-lst (acl2::reverse-list bit-vars) valuation))
                              p))))
  :hints (("Goal" :in-theory (enable make-packing-constraint
                                     r1cs-constraint-holdsp
                                     integerp-of-lookup-equal
                                     acl2-numberp-of-lookup-equal))))
