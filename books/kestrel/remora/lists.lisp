; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/basic/pos-fix" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "arithmetic"))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/true-list-listp-theorems" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lists
  :parents (library-extensions)
  :short "Library extensions for lists."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled car-of-repeat
  :short "Theorem about @(tsee car) applied to @(tsee repeat)."
  (equal (car (repeat n x))
         (if (zp n) nil x))
  :induct t
  :enable repeat)

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

  (defrule list-repeatp-of-repeat
    (list-repeatp (repeat n x))
    :induct t
    :enable (repeat car-of-repeat))

  (defrule list-repeatp-of-cdr
    (implies (list-repeatp x)
             (list-repeatp (cdr x))))

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

(std::deflist all-of-len-p (x len)
  :guard (and (true-list-listp x)
              (natp len))
  :short "Check if all the lists in a list of lists have a given length."
  (equal (len x) (nfix len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define list-split ((list true-listp) (chunk posp))
  :guard (integerp (/ (len list) chunk))
  :returns (lists true-list-listp)
  :short "Split a list into chunks (sublists) of a given length each."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be a whole number of chunks in the list."))
  (b* (((when (endp list)) nil)
       (chunk (mbe :logic (pos-fix chunk) :exec chunk))
       (sublist (take chunk list))
       (sublists (list-split (nthcdr chunk list) chunk)))
    (cons sublist sublists))
  :measure (len list)
  :hints (("Goal" :in-theory (enable nfix)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  ///

  (defrule len-of-list-split
    (implies (and (posp chunk)
                  (integerp (/ (len list) chunk)))
             (equal (len (list-split list chunk))
                    (/ (len list) chunk)))
    :induct t
    :enable (fix nfix lt-to-zero-when-divided-by-pos))

  (defrule consp-of-list-split
    (equal (consp (list-split list chunk))
           (consp list))
    :induct t)

  (defrule all-of-len-p-of-list-split
    (implies (posp chunk)
             (all-of-len-p (list-split list chunk) chunk))
    :induct t
    :enable (all-of-len-p))

  (defrule list-list-repeat-of-list-split
    (implies (and (list-repeatp list)
                  (posp n)
                  (integerp (/ (len list) n)))
             (list-list-repeatp (list-split list n)))
    :induct t
    :enable (list-list-repeatp nfix posp pos-gte-pos-divisor)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define append-list-to-lists ((list true-listp) (lists true-list-listp))
  :returns (lists1 true-list-listp)
  :short "Append a list to each list in a list of lists."
  (cond ((endp lists) nil)
        (t (cons (append list (true-list-fix (car lists)))
                 (append-list-to-lists list (cdr lists)))))

  ///

  (defret len-of-append-list-to-lists
    (equal (len lists1)
           (len lists))
    :hints (("Goal" :induct t)))

  (defret consp-of-append-list-to-lists
    (equal (consp lists1)
           (consp lists))
    :hints (("Goal" :induct t)))

  (defret append-list-to-lists-iff
    (iff lists1 (true-list-fix lists))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define car-list ((lists true-list-listp))
  :returns (cars true-listp)
  :short "Take the first element of each list in a list of lists,
          returning the list of first elements in the same order."
  (cond ((endp lists) nil)
        (t (cons (car (car lists)) (car-list (cdr lists)))))

  ///

  (defret len-of-car-list
    (equal (len cars)
           (len lists))
    :hints (("Goal" :induct t)))

  (defret consp-of-car-list
    (equal (consp cars)
           (consp lists))
    :hints (("Goal" :induct t))))
