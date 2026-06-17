; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lists")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/nat-list-list" :dir :system)

(local (include-book "std/basic/nfix" :dir :system))
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

(defruled true-listp-when-nat-listp
  :short "A list of naturals is a true list."
  (implies (nat-listp x)
           (true-listp x)))

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
    :hints (("Goal" :induct t)))

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruled nat-list-product-of-cdr-to-ratio
    (implies (and (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims))
             (equal (nat-list-product (cdr dims))
                    (/ (nat-list-product dims) (car dims)))))

  (defruled nat-list-product-divided-by-car
    (implies (and (nat-listp dims)
                  (consp dims))
             (integerp (/ (nat-list-product dims) (car dims))))))

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

(defrule nat-listp-of-append-all
  :short "Type of @(tsee append-all) applied to lists of lists of naturals."
  (implies (nat-list-listp lists)
           (nat-listp (append-all lists)))
  :induct t
  :enable append-all)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nat-listp-of-mv-nth-1-of-check-list-suffix
  :short "Type of the prefix returned by @(tsee check-list-suffix)
          on a list of naturals."
  (implies (nat-listp list)
           (nat-listp (mv-nth 1 (check-list-suffix list suffix))))
  :induct (check-list-suffix list suffix)
  :enable check-list-suffix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nat-list-listp-of-mv-nth-1-of-check-list-suffixes
  :short "Type of the prefixes returned by @(tsee check-list-suffixes)
          on a list of lists of naturals."
  (implies (nat-list-listp lists)
           (nat-list-listp (mv-nth 1 (check-list-suffixes lists suffixes))))
  :induct (check-list-suffixes lists suffixes)
  :enable check-list-suffixes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule nat-listp-of-mv-nth-1-of-list-prefix-join
  :short "Type of the join returned by @(tsee list-prefix-join)
          on a list of lists of naturals."
  (implies (nat-list-listp lists)
           (nat-listp (mv-nth 1 (list-prefix-join lists))))
  :induct t
  :enable list-prefix-join)
