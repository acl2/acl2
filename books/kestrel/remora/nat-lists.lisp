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
(include-book "kestrel/fty/nat-list-list" :dir :system)

(local (include-book "std/typed-lists/nat-listp" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nat-lists
  :parents (library-extensions)
  :short "Library extensions for lists of natural numbers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-list-sum ((nats nat-listp))
  :returns (sum natp)
  :short "Sum of a list of zero or more natural numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 0 if the list is empty."))
  (cond ((endp nats) 0)
        (t (+ (lnfix (car nats)) (nat-list-sum (cdr nats))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-list-product ((nats nat-listp))
  :returns (product natp)
  :short "Product of a list of zero or more natural numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 1 if the list is empty."))
  (cond ((endp nats) 1)
        (t (* (lnfix (car nats)) (nat-list-product (cdr nats)))))

  ///

  (defret zp-of-nat-list-product-iff-member-0
    (iff (zp product)
         (member-equal 0 (nat-list-fix nats)))
    :hints (("Goal" :induct t)))

  (defret nat-list-product-0-iff-member-0
    (iff (equal product 0)
         (member-equal 0 (nat-list-fix nats)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-list-subtraction ((nats nat-listp))
  :guard (consp nats)
  :returns (subtraction integerp)
  :short "Subtraction of a list of one or more natural numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is defined as in Common Lisp:
     there must not be zero operands;
     if there is one operand, it is negated;
     if there are two or more operands,
     the ones after the first are all subtracted from the first."))
  (cond ((endp nats) (prog2$ (impossible) 0))
        ((endp (cdr nats)) (- (lnfix (car nats))))
        (t (- (lnfix (car nats)) (nat-list-sum (cdr nats))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-append-all ((natss nat-list-listp))
  :returns (nats nat-listp)
  :short "Append all the lists of naturals in a list, in that order."
  (cond ((endp natss) nil)
        (t (append (nat-list-fix (car natss))
                   (nat-append-all (cdr natss))))))
