; Valuations (maps from vars to field elements)
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)

;; A true list of variables, with no duplicates
(defun var-listp (vars)
  (declare (xargs :guard t))
  (and (symbol-listp vars)
       (no-duplicatesp-eq vars)))

;; A valuation is a map (alist) from vars to values that are field elements.
(defund r1cs-valuationp (valuation prime)
  (declare (xargs :guard (rtl::primep prime)))
  (and (alistp valuation)
       (var-listp (strip-cars valuation))
       (fe-listp (strip-cdrs valuation) prime)))

(defthm r1cs-valuationp-forward-to-alistp
  (implies (r1cs-valuationp valuation prime)
           (alistp valuation))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm r1cs-valuationp-forward-to-symbol-listp-of-strip-cars
  (implies (r1cs-valuationp valuation prime)
           (symbol-listp (strip-cars valuation)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm r1cs-valuationp-forward-to-no-duplicatesp-of-strip-cars
  (implies (r1cs-valuationp valuation prime)
           (no-duplicatesp (strip-cars valuation)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm r1cs-valuationp-when-not-consp
  (implies (not (consp valuation))
           (equal (r1cs-valuationp valuation prime)
                  (not valuation)))
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm r1cs-valuationp-of-cdr
  (implies (r1cs-valuationp valuation prime)
           (r1cs-valuationp (cdr valuation) prime))
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defund valuation-bindsp (valuation var)
  (declare (xargs :guard (and (symbolp var)
                              (alistp valuation))))
  (member-equal var (strip-cars valuation)))

;; A valuation cannot bind the constant 1, because it is a variable
(defthm not-valuation-bindsp-of-1
  (implies (r1cs-valuationp valuation p)
           (not (valuation-bindsp valuation 1)))
  :hints (("Goal" :in-theory (enable r1cs-valuationp valuation-bindsp))))

(defthm fep-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (fep (lookup-equal var valuation) prime))
  :hints (("Goal" :in-theory (enable r1cs-valuationp
                                     valuation-bindsp))))

;slow?
(defthmd integerp-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (integerp (lookup-equal var valuation)))
  :hints (("Goal" :in-theory (enable r1cs-valuationp
                                     valuation-bindsp))))

(defthmd acl2-numberp-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (acl2-numberp (lookup-equal var valuation)))
  :hints (("Goal" :use (:instance integerp-of-lookup-equal))))

(defthm <-of-lookup-equal-when-r1cs-valuationp
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (< (lookup-equal var valuation) prime))
  :hints (("Goal" :use (:instance fep-of-lookup-equal)
           :in-theory (disable fep-of-lookup-equal))))

(defthm natp-of-lookup-equal-when-r1cs-valuationp-type
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (natp (lookup-equal var valuation)))
  :rule-classes :type-prescription
  :hints (("Goal" :use (:instance fep-of-lookup-equal)
           :in-theory (disable fep-of-lookup-equal))))

(defund valuation-binds-allp (valuation vars)
  (declare (xargs :guard (and (symbol-listp vars) (alistp valuation))))
  (if (endp vars)
      t
    (and (valuation-bindsp valuation (first vars))
         (valuation-binds-allp valuation (rest vars)))))

(defthm valuation-bindsp-when-valuation-binds-allp
  (implies (and (valuation-binds-allp valuation vars)
                (member-equal var vars))
           (valuation-bindsp valuation var))
  :hints (("Goal" :in-theory (enable valuation-binds-allp))))

(defthm valuation-binds-allp-of-append
  (equal (valuation-binds-allp valuation (append vars1 vars2))
         (and (valuation-binds-allp valuation vars1)
              (valuation-binds-allp valuation vars2)))
  :hints (("Goal" :in-theory (enable valuation-binds-allp))))

(defthm valuation-binds-allp-of-cons
  (equal (valuation-binds-allp valuation (cons var vars))
         (and (valuation-bindsp valuation var)
              (valuation-binds-allp valuation vars)))
  :hints (("Goal" :in-theory (enable valuation-binds-allp))))
