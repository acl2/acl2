; Fixing Function for Lists of Signed Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-lists/signed-byte-listp" :dir :system)
(include-book "signed-byte-fixing")

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-byte-list-fix ((bits posp) (x (signed-byte-listp bits x)))
  :returns (fixed-x (signed-byte-listp bits fixed-x)
                    :hyp (posp bits))
  :parents (kestrel-utilities signed-byte-listp signed-byte-fix)
  :short "Fixing function for @(tsee signed-byte-listp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee signed-byte-fix) to lists.
     See that function for more information,
     in particular about the fixing of @('bits') to a positive integer."))
  (mbe :logic (cond ((atom x) nil)
                    (t (cons (signed-byte-fix bits (car x))
                             (signed-byte-list-fix bits (cdr x)))))
       :exec x)
  :hooks (:fix)
  ///

  (more-returns
   (fixed-x integer-listp
            :name integer-listp-of-signed-byte-list-fix))

  (defrule signed-byte-list-fix-when-signed-byte-listp
    (implies (signed-byte-listp (pos-fix bits) x)
             (equal (signed-byte-list-fix bits x)
                    x)))

  (defrule signed-byte-list-fix-of-nil
    (equal (signed-byte-list-fix bits nil)
           nil))

  (defrule signed-byte-list-fix-of-cons
    (equal (signed-byte-list-fix bits (cons x y))
           (cons (signed-byte-fix bits x)
                 (signed-byte-list-fix bits y))))

  (defrule signed-byte-list-fix-of-append
    (equal (signed-byte-list-fix bits (append x y))
           (append (signed-byte-list-fix bits x)
                   (signed-byte-list-fix bits y))))

  (defrule len-of-signed-byte-list-fix
    (equal (len (signed-byte-list-fix bits x))
           (len x)))

  (defrule consp-of-signed-byte-list-fix
    (equal (consp (signed-byte-list-fix bits x))
           (consp x)))

  (defrule car-of-signed-byte-list-fix
    (implies (consp x)
             (equal (car (signed-byte-list-fix bits x))
                    (signed-byte-fix bits (car x)))))

  (defrule cdr-of-signed-byte-list-fix
    (implies (consp x)
             (equal (cdr (signed-byte-list-fix bits x))
                    (signed-byte-list-fix bits (cdr x)))))

  (defrule rev-of-signed-byte-list-fix
    (equal (rev (signed-byte-list-fix bits x))
           (signed-byte-list-fix bits (rev x)))
    :enable rev))
