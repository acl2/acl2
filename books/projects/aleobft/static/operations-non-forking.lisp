; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-non-forking
  :parents (operations-additional)
  :short "Operations about non-forking sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "A fundamental property of our protocol is that blockchains do not fork.
     We prove that by first showing the anchor sequences do not fork.")
   (xdoc::p
    "So here we introduce a generic operation on lists (i.e. sequences)
     formalizing the notion of not forking."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lists-nofork-p ((list1 true-listp)
                        (list2 true-listp))
  :returns (yes/no booleanp)
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
     the two lists have forked.
     This is applicable to lists modeling blockchains,
     where each element of the lists is a block.")
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

  (defrule lists-nofork-p-of-same
    (lists-nofork-p list list))

  (defrule lists-nofork-p-of-nil-left
    (implies (true-listp list)
             (lists-nofork-p nil list))
    :enable fix)

  (defrule lists-nofork-p-of-nil-right
    (implies (true-listp list)
             (lists-nofork-p list nil))
    :enable fix)

  (defrule lists-nofork-p-of-append-left
    (lists-nofork-p (append list1 list2)
                    list2)
    :enable (fix nfix))

  (defrule lists-nofork-p-of-append-right
    (lists-nofork-p list2
                    (append list1 list2))
    :enable (fix nfix))

  (defrule lists-nofork-p-commutative
    (equal (lists-nofork-p list1 list2)
           (lists-nofork-p list2 list1))
    :enable lists-nofork-p))
