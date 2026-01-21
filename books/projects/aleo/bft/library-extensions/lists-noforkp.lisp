; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lists-noforkp ((list1 true-listp)
                       (list2 true-listp))
  :returns (yes/no booleanp)
  :parents (library-extensions)
  :short "Check that two lists do not fork in front."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lists must be considered from right to left w.r.t. forking.
     That is, the lists start at @('nil') and are extended via @(tsee cons).
     So long we the same things are @(tsee cons)ed to both in the same order,
     the lists do not fork, i.e. stay the same.
     If elements are added to one list but not the other,
     the former is ``ahead'', but there is no forking.
     There continued to be no forking if the shorter list
     is extended with the same elements as the longer list.
     Only if at some point there are two different elements,
     the two lists have forked.")
   (xdoc::p
    "Saying that the two lists do not diverge amounts to saying that
     the longer one is an extension of the shorter one,
     or that they are equal if they have the same length.
     Saying that one is an extension of another is expressed
     by saying that the shorter one is obtained
     by removing from (the front of) the longer one
     a number of elements equal to the difference in lengths.")
   (xdoc::p
    "We prove various properties of this predicate,
     so that we do not need to open it in proofs that use it."))
  (cond
   ((< (len list1) (len list2))
    (equal (nthcdr (- (len list2)
                      (len list1))
                   list2)
           list1))
   ((> (len list1) (len list2))
    (equal (nthcdr (- (len list1)
                      (len list2))
                   list1)
           list2))
   (t ; (= (len list1) (len list2))
    (equal list1 list2)))

  ///

  (defrule lists-noforkp-of-same
    (lists-noforkp list list))

  (defrule lists-noforkp-of-nil-left
    (implies (true-listp list)
             (lists-noforkp nil list))
    :enable fix)

  (defrule lists-noforkp-of-nil-right
    (implies (true-listp list)
             (lists-noforkp list nil))
    :enable fix)

  (defrule lists-noforkp-of-append-left
    (lists-noforkp (append list1 list2)
                   list2)
    :enable (fix nfix))

  (defrule lists-noforkp-of-append-right
    (lists-noforkp list2
                   (append list1 list2))
    :enable (fix nfix))

  (defrule lists-noforkp-of-append-more-right
    (implies (and (lists-noforkp list1 list2)
                  (<= (len list1) (len list2)))
             (lists-noforkp list1 (append list list2)))
    :induct t
    :enable (append fix))

  (defrule lists-noforkp-commutative
    (equal (lists-noforkp list1 list2)
           (lists-noforkp list2 list1))
    :enable lists-noforkp))
