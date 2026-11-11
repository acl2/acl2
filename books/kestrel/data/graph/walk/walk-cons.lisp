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

(local (include-book "../edge"))
(local (include-book "../edges"))
(local (include-book "step"))
(local (include-book "walk"))
(local (include-book "walk-in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-cons (from label (walk walkp))
  :type-prescription :none
  :returns (walk$ walkp)
  :parents (walks)
  :short "Add a step to the front of a walk."
  :long
  (xdoc::topstring-p
    "The result starts at @('from'), follows the edge with the given label to
     the start of @('walk'), and then continues as @('walk'). Time
     complexity: @($O(1)$).")
  (walk from
        (cons (step (walk->start walk) label)
              (walk->steps walk)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-cons-when-walk-equiv-of-arg3-congruence
  (implies (walk-equiv walk0 walk1)
           (equal (walk-cons from label walk0)
                  (walk-cons from label walk1)))
  :rule-classes :congruence
  :enable walk-cons)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule walk->start-of-walk-cons
  (equal (walk->start (walk-cons from label walk))
         from)
  :enable walk-cons)

(defrule walk->steps-of-walk-cons
  (equal (walk->steps (walk-cons from label walk))
         (cons (step (walk->start walk) label)
               (walk->steps walk)))
  :enable walk-cons)

(defrule walk-end-of-walk-cons
  (equal (walk-end (walk-cons from label walk))
         (walk-end walk))
  :enable (walk-end
           steps-end))

(defrule walk-edges-of-walk-cons
  (equal (walk-edges (walk-cons from label walk))
         (treeset::insert (edge from (walk->start walk) label)
                          (walk-edges walk)))
  :enable (walk-edges
           steps-edges))

(defrule walk-in-of-walk-cons
  (equal (walk-in (walk-cons from label walk) graph)
         (and (treeset::in (edge from (walk->start walk) label)
                           (edges graph))
              (walk-in walk graph)))
  :enable walk-in)
