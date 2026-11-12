; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/data/treeset/set-defs" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../edge-defs")
(include-book "../edges-defs")
(include-book "step-defs")
(include-book "walk-defs")
(include-book "walk-in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/insert" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "../edge"))
(local (include-book "../edges"))
(local (include-book "step"))
(local (include-book "walk"))
(local (include-book "walk-in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-snoc ((walk walkp) to label)
  :type-prescription :none
  :returns (walk$ walkp)
  :parents (walks)
  :short "Add a step to the end of a walk."
  :long
  (xdoc::topstring
    (xdoc::p
      "The result follows @('walk'), and then the edge with the given label
       from its end to @('to').")
    (xdoc::p
      "Time complexity: @($O(k)$), where @($k$) is the number of steps, since
       the steps are copied. Building a walk by repeated calls therefore takes
       quadratic time. To build a walk from its start in linear time,
       accumulate its steps in reverse and reverse them once at the end."))
  (walk (walk->start walk)
        (append (walk->steps walk)
                (list (step to label))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-snoc-when-walk-equiv-of-arg1-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-snoc walk0 to label)
                  (walk-snoc walk1 to label)))
  :rule-classes :congruence
  :enable walk-snoc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule walk->start-of-walk-snoc
  (equal (walk->start (walk-snoc walk to label))
         (walk->start walk))
  :enable walk-snoc)

(defrule walk->steps-of-walk-snoc
  (equal (walk->steps (walk-snoc walk to label))
         (append (walk->steps walk)
                 (list (step to label))))
  :enable walk-snoc)

(defrule walk-end-of-walk-snoc
  (equal (walk-end (walk-snoc walk to label))
         to)
  :enable (walk-end
           steps-end))

(defrule walk-edges-of-walk-snoc
  (equal (walk-edges (walk-snoc walk to label))
         (treeset::insert (edge (walk-end walk) to label)
                          (walk-edges walk)))
  :enable (walk-edges
           walk-end
           steps-edges))

(defrule walk-in-of-walk-snoc
  (equal (walk-in (walk-snoc walk to label) graph)
         (and (walk-in walk graph)
              (treeset::in (edge (walk-end walk) to label)
                           (edges graph))))
  :enable walk-in)
