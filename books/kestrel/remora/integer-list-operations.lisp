; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "std/typed-lists/integer-listp" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ integer-list-operations
  :parents (library-extensions)
  :short "Operations on lists of integer numbers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-list-sum ((ints integer-listp))
  :returns (sum integerp)
  :short "Sum of a list of zero or more integer numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 0 if the list is empty."))
  (cond ((endp ints) 0)
        (t (+ (lifix (car ints)) (integer-list-sum (cdr ints))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-list-product ((ints integer-listp))
  :returns (product integerp)
  :short "Product of a list of zero or more integer numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 1 if the list is empty."))
  (cond ((endp ints) 1)
        (t (* (lifix (car ints)) (integer-list-product (cdr ints))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-list-subtraction ((ints integer-listp))
  :guard (consp ints)
  :returns (subtraction integerp)
  :short "Subtraction of a list of one or more integer numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is defined as in Common Lisp:
     there must not be zero operands;
     if there is one operand, it is negated;
     if there are two or more operands,
     the ones after the first are all subtracted from the first."))
  (cond ((endp ints) (prog2$ (impossible) 0))
        ((endp (cdr ints)) (- (lifix (car ints))))
        (t (- (lifix (car ints)) (integer-list-sum (cdr ints))))))
