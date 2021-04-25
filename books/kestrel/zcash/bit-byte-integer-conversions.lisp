; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZCASH")

(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bit/byte/integer-conversions
  :parents (zcash)
  :short "Conversions between bit sequences, byte sequenes, and integers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are defined in [ZPS:5.2]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define i2lebsp ((l natp) (x (integer-range-p 0 (expt 2 l) x)))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{I2LEBSP}$) in [ZPS:5.2]."
  (acl2::nat=>lebits l x)
  ///

  (defret len-of-i2lebsp
    (equal (len bits) (nfix l)))

  (defrule i2lebsp-injectivity
    (implies (and (< (nfix x1) (expt 2 (nfix l)))
                  (< (nfix x2) (expt 2 (nfix l))))
             (equal (equal (i2lebsp l x1)
                           (i2lebsp l x2))
                    (equal (nfix x1) (nfix x2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define i2bebsp ((l natp) (x (integer-range-p 0 (expt 2 l) x)))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{I2BEBSP}$) in [ZPS:5.2]."
  (acl2::nat=>bebits l x)
  ///

  (defret len-of-i2bebsp
    (equal (len bits) (nfix l)))

  (defrule i2bebsp-injectivity
    (implies (and (< (nfix x1) (expt 2 (nfix l)))
                  (< (nfix x2) (expt 2 (nfix l))))
             (equal (equal (i2bebsp l x1)
                           (i2bebsp l x2))
                    (equal (nfix x1) (nfix x2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lebs2ip ((s bit-listp))
  :returns (x natp :rule-classes :type-prescription)
  :short "The function @($\\mathsf{LEBS2IP}$) in [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('$\\ell$') argument can be determined from the @($S$) argument:
     it is the length of @($S$).
     Thus, in our formalization we just have one argument."))
  (acl2::lebits=>nat s)
  ///

  (local (include-book "arithmetic-3/top" :dir :system))

  (defret lebs2ip-upper-bound
    (< x (expt 2 (len s)))
    :rule-classes :linear)

  (defrule lebs2ip-injectivity
    (implies (equal (len s1) (len s2))
             (equal (equal (lebs2ip s1)
                           (lebs2ip s2))
                    (equal (acl2::bit-list-fix s1)
                           (acl2::bit-list-fix s2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leos2ip ((s byte-listp))
  :returns (x natp :rule-classes :type-prescription)
  :short "The function @($\\mathsf{LEOS2IP}$) in [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('$\\ell$') argument can be determined from the @($S$) argument:
     it is the length of @($S$) times 8.
     Thus, in our formalization we just have one argument."))
  (acl2::lebytes=>nat s)
  ///

  (local (include-book "arithmetic-3/top" :dir :system))

  (defret leos2ip-upper-bound
    (< x (expt 2 (* 8 (len s))))
    :rule-classes :linear
    :hints (("Goal"
             :use (:instance acl2::lebytes=>nat-upper-bound
                   (acl2::digits s)))))

  (defrule leos2ip-injectivity
    (implies (equal (len s1) (len s2))
             (equal (equal (leos2ip s1)
                           (leos2ip s2))
                    (equal (acl2::byte-list-fix s1)
                           (acl2::byte-list-fix s2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lebs2osp ((bits bit-listp))
  :returns (bytes byte-listp)
  :short "The function @($\\mathsf{LEBS2OSP}$) in [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($\\ell$) argumnent can be determined from the other argument:
     it is the length of the other argument.
     Thus, in our formalization we just have one argument."))
  (b* ((l (len bits))
       (padlen (- (* 8 (ceiling l 8)) l))
       (padded (append bits (repeat padlen 0))))
    (acl2::bits=>lebytes padded))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  ///
  (defret len-of-lebs2osp
    (equal (len bytes)
           (ceiling (len bits) 8))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define leos2bsp ((bytes byte-listp))
  :returns (bits bit-listp)
  :short "The function @($\\mathsf{LEOS2BSP}$) in [ZPS:5.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @($\\ell$) argumnent can be determined from the other argument:
     it is the length of the other argument times 8.
     Thus, in our formalization we just have one argument."))
  (acl2::lebytes=>bits bytes)
  ///
  (defret len-of-leos2bsp
    (equal (len bits)
           (* 8 (len bytes)))))
