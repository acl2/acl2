; Fixing Function for Lists of Unsigned Bytes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "unsigned-byte-fixing")

(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unsigned-byte-list-fix ((bits natp) (x (unsigned-byte-listp bits x)))
  :returns (fixed-x (unsigned-byte-listp bits fixed-x)
                    :hyp (natp bits))
  :parents (kestrel-utilities unsigned-byte-listp unsigned-byte-fix)
  :short "Fixing function for @(tsee unsigned-byte-listp)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee unsigned-byte-fix) to lists.
     See that function for more information,
     in particular about the fixing of @('bits') to a natural number."))
  (mbe :logic (cond ((atom x) nil)
                    (t (cons (unsigned-byte-fix bits (car x))
                             (unsigned-byte-list-fix bits (cdr x)))))
       :exec x)
  :hooks (:fix)
  ///

  (more-returns
   (fixed-x integer-listp
            :name integer-listp-of-unsigned-byte-list-fix))

  (defrule unsigned-byte-list-fix-when-unsigned-byte-listp
    (implies (unsigned-byte-listp (nfix bits) x)
             (equal (unsigned-byte-list-fix bits x)
                    x)))

  (defrule unsigned-byte-list-fix-of-nil
    (equal (unsigned-byte-list-fix bits nil)
           nil))

  (defrule unsigned-byte-list-fix-of-cons
    (equal (unsigned-byte-list-fix bits (cons x y))
           (cons (unsigned-byte-fix bits x)
                 (unsigned-byte-list-fix bits y))))

  (defrule unsigned-byte-list-fix-of-append
    (equal (unsigned-byte-list-fix bits (append x y))
           (append (unsigned-byte-list-fix bits x)
                   (unsigned-byte-list-fix bits y))))

  (defrule len-of-unsigned-byte-list-fix
    (equal (len (unsigned-byte-list-fix bits x))
           (len x)))

  (defrule consp-of-unsigned-byte-list-fix
    (equal (consp (unsigned-byte-list-fix bits x))
           (consp x)))

  (defrule car-of-unsigned-byte-list-fix
    (implies (consp x)
             (equal (car (unsigned-byte-list-fix bits x))
                    (unsigned-byte-fix bits (car x)))))

  (defrule cdr-of-unsigned-byte-list-fix
    (implies (consp x)
             (equal (cdr (unsigned-byte-list-fix bits x))
                    (unsigned-byte-list-fix bits (cdr x)))))

  (defrule rev-of-unsigned-byte-list-fix
    (equal (rev (unsigned-byte-list-fix bits x))
           (unsigned-byte-list-fix bits (rev x)))
    :enable rev))
