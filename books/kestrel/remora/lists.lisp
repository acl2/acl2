; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/utilities/true-list-listp-theorems" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lists
  :parents (library-extensions)
  :short "Library extensions for lists."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define append-all ((lists true-list-listp))
  :returns (list true-listp)
  :short "Append all the lists in a list, in that order."
  (cond ((endp lists) nil)
        (t (append (mbe :logic (true-list-fix (car lists))
                        :exec (car lists))
                   (append-all (cdr lists))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-repeatp ((x true-listp))
  :returns (yes/no booleanp)
  :short "Check if all the elements of a list are the same."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether it is a repetition of the same element,
     zero or more times."))
  (or (endp x)
      (endp (cdr x))
      (and (equal (car x) (cadr x))
           (list-repeatp (cdr x))))

  ///

  (defrule list-repeatp-of-take
    (implies (and (list-repeatp list)
                  (<= (nfix n) (len list)))
             (list-repeatp (take n list)))
    :induct t
    :enable take)

  (defrule list-repeatp-of-nthcdr
    (implies (list-repeatp list)
             (list-repeatp (nthcdr n list)))
    :induct t
    :enable nthcdr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist list-list-repeatp (x)
  :guard (true-list-listp x)
  :short "Lift @(tsee list-repeatp) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is check whether each list in the list of lists
     is a repetition of the same element.
     But different lists in the list of lists may differ,
     i.e. they may be repetitions of different elements.
     This is different from saying that
     all the element of the lists in the list of lists are the same."))
  (list-repeatp x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled car-of-repeat
  :short "Theorem about @(tsee car) applied to @(tsee repeat)."
  (equal (car (repeat n x))
         (if (zp n) nil x))
  :induct t
  :enable repeat)
