; Bitcoin Library -- Extensions of Other Libraries
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/digits-any-base-pow2" :dir :system)
(include-book "kestrel/utilities/lists/index-of-theorems" :dir :system)
(include-book "std/basic/inductions" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; These will be moved to the appropriate libraries.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled car-of-rev-rewrite-car-of-last
  (equal (car (rev x))
         (car (last x)))
  :enable rev)

(defruled car-of-last-rewrite-car-of-rev
  (equal (car (last x))
         (car (rev x)))
  :enable rev)

(theory-invariant (incompatible (:rewrite car-of-rev-rewrite-car-of-last)
                                (:rewrite car-of-last-rewrite-car-of-rev)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule consp-of-nat=>lendian*-iff-not-zp
  (equal (consp (nat=>lendian* base nat))
         (not (zp nat)))
  :enable nat=>lendian*)

(defrule consp-of-nat=>bendian*-iff-not-zp
  (equal (consp (nat=>bendian* base nat))
         (not (zp nat)))
  :enable nat=>bendian*)

(defrule nat=>lendian*-does-not-end-with-0
  (not (equal (car (last (nat=>lendian* base nat)))
              0))
  :enable nat=>lendian*)

(defrule nat=>bendian*-does-not-start-with-0
  (not (equal (car (nat=>bendian* base nat))
              0))
  :enable (nat=>bendian* car-of-rev-rewrite-car-of-last))

(defrule trim-bendian*-of-append-zeros
  (implies (zp-listp zeros)
           (equal (trim-bendian* (append zeros digits))
                  (trim-bendian* digits)))
  :enable trim-bendian*
  :induct (dec-induct n))

(defrule trim-lendian*-of-append-zeros
  (implies (zp-listp zeros)
           (equal (trim-lendian* (append digits zeros))
                  (trim-lendian* digits)))
  :enable trim-lendian*
  :induct (dec-induct n))

(defrule trim-bendian*-when-no-starting-0
  (implies (not (zp (car digits)))
           (equal (trim-bendian* digits)
                  (nat-list-fix digits)))
  :enable trim-bendian*)

(defrule trim-lendian*-when-no-ending-0
  (implies (not (zp (car (last digits))))
           (equal (trim-lendian* digits)
                  (nat-list-fix digits)))
  :enable (trim-lendian* car-of-last-rewrite-car-of-rev)
  :prep-books
  ((include-book "kestrel/utilities/typed-list-theorems" :dir :system)))

(defrule trim-bendian*-of-nat=>bendian*
  (equal (trim-bendian* (nat=>bendian* base nat))
         (nat=>bendian* base nat))
  :use (nat=>bendian*-does-not-start-with-0
        consp-of-nat=>bendian*-iff-not-zp
        (:instance trim-bendian*-when-no-starting-0
         (digits (nat=>bendian* base nat))))
  :disable (nat=>bendian*-does-not-start-with-0
            trim-bendian*-when-no-starting-0
            consp-of-nat=>bendian*-iff-not-zp))

(defrule trim-lendian*-of-nat=>lendian*
  (equal (trim-lendian* (nat=>lendian* base nat))
         (nat=>lendian* base nat))
  :enable trim-lendian*
  :use nat=>bendian*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ubyte8-fix-rewrite-dab-digit-fix-256
  (equal (ubyte8-fix digits)
         (dab-digit-fix 256 digits))
  :enable (ubyte8-fix dab-digit-fix dab-digitp ubyte8p))

(defruled ubyte8-list-fix-rewrite-dab-digit-list-fix-256
  (equal (ubyte8-list-fix digits)
         (dab-digit-list-fix 256 digits))
  :enable (dab-digit-list-fix
           ubyte8-list-fix
           ubyte8-fix-rewrite-dab-digit-fix-256))
