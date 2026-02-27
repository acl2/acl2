; AIR Library
; Model 0: Library Extensions
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "kestrel/fty/bit-list" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist all-< (x bound)
  :guard (and (nat-listp x) (natp bound))
  (< x bound))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist all-null (x)
  :guard (boolean-listp x)
  (null x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection bool-list->bit-list ((x boolean-listp))
  :returns (bits bit-listp)
  (bool->bit x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled consp-when-consp-and-same-len
  (implies (and (equal (len x) (len y))
                (consp x))
           (consp y)))

;;;;;;;;;;;;;;;;;;;;

(defruled consp-of-cdr-when-consp-of-cdr-and-same-len
  (implies (and (equal (len x) (len y))
                (consp (cdr x)))
           (consp (cdr y))))

;;;;;;;;;;;;;;;;;;;;

(defruled consp-of-cddr-when-consp-of-cddr-and-same-len
  (implies (and (equal (len x) (len y))
                (consp (cddr x)))
           (consp (cddr y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled take-of-len-minus-1-is-butlast-1
  (implies (consp x)
           (equal (take (1- (len x)) x)
                  (butlast x 1)))
  :induct t
  :enable (butlast fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nth-of-len-minus-1-is-car-last
  (implies (consp lst)
           (equal (nth (1- (len lst)) lst)
                  (car (last lst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule all-<-256-when-ubyte8-listp
  (implies (ubyte8-listp x)
           (all-< x 256))
  :induct t
  :enable (ubyte8-listp
           ubyte8p
           unsigned-byte-p
           integer-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule pfield::fe-listp-of-cdr
  (implies (pfield::fe-listp x p)
           (pfield::fe-listp (cdr x) p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::fe-listp-when-nat-listp-and-all-<-prime
  (implies (and (nat-listp x)
                (all-< x prime))
           (pfield::fe-listp x prime))
  :induct t
  :enable (pfield::fe-listp
           pfield::fep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::fe-listp-when-ubyte8-listp
  (implies (and (ubyte8-listp x)
                (> prime 255))
           (pfield::fe-listp x prime))
  :induct t
  :enable (pfield::fe-listp
           pfield::fep
           ubyte8p
           unsigned-byte-p
           integer-range-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled pfield::fe-listp-when-bit-listp
  (implies (and (bit-listp x)
                (> prime 1))
           (pfield::fe-listp x prime))
  :induct t
  :enable pfield::fe-listp)
