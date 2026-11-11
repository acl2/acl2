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
(include-book "kestrel/data/treeset/union-defs" :dir :system)

(include-book "../graph-defs")
(include-book "step-defs")
(include-book "walk-defs")
(include-book "walk-in-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/data/treeset/set" :dir :system))
(local (include-book "kestrel/data/treeset/in" :dir :system))
(local (include-book "kestrel/data/treeset/subset" :dir :system))
(local (include-book "kestrel/data/treeset/union" :dir :system))

(local (include-book "../edges"))
(local (include-book "step"))
(local (include-book "walk"))
(local (include-book "walk-in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define walk-append ((x walkp) (y walkp))
  :guard (equal (walk-end x) (walk->start y))
  :type-prescription :none
  :returns (walk walkp)
  :parents (walks)
  :short "Join two walks, the second starting where the first ends."
  :long
  (xdoc::topstring
    (xdoc::p
      "The result follows @('x') and then @('y'). The guard requires @('y')
       to start at the end of @('x'). Logically, if it does not, the result
       is @('x'), so that joining two walks in a graph always gives a walk in
       the graph (see @('walk-in-of-walk-append-when-walk-in-and-walk-in')).")
    (xdoc::p
      "Time complexity: @($O(k)$), where @($k$) is the number of steps of
       @('x'), since those steps are copied."))
  (mbe :logic (if (equal (walk-end x) (walk->start y))
                  (walk (walk->start x)
                        (append (walk->steps x) (walk->steps y)))
                (walk-fix x))
       :exec (walk (walk->start x)
                   (append (walk->steps x) (walk->steps y))))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(defrule walk-append-when-walk-equiv-of-arg1-congruence
  (implies (walk-equiv x0 x1)
           (equal (walk-append x0 y)
                  (walk-append x1 y)))
  :rule-classes :congruence
  :enable walk-append)

(defrule walk-append-when-walk-equiv-of-arg2-congruence
  (implies (walk-equiv y0 y1)
           (equal (walk-append x y0)
                  (walk-append x y1)))
  :rule-classes :congruence
  :enable walk-append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When the second walk does not start where the first ends, the first walk
;; is returned.

(defruled walk-append-when-not-equal-of-walk-end-and-walk->start
  (implies (not (equal (walk-end x) (walk->start y)))
           (equal (walk-append x y)
                  (walk-fix x)))
  :enable walk-append)

(defrule walk-append-when-not-equal-of-walk-end-and-walk->start-cheap
  (implies (not (equal (walk-end x) (walk->start y)))
           (equal (walk-append x y)
                  (walk-fix x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by walk-append-when-not-equal-of-walk-end-and-walk->start)

;; Otherwise the walks are joined.

(defrule walk->start-of-walk-append
  (equal (walk->start (walk-append x y))
         (walk->start x))
  :enable walk-append)

(defrule walk->steps-of-walk-append
  (implies (equal (walk-end x) (walk->start y))
           (equal (walk->steps (walk-append x y))
                  (append (walk->steps x) (walk->steps y))))
  :enable walk-append)

(defrule walk-end-of-walk-append
  (implies (equal (walk-end x) (walk->start y))
           (equal (walk-end (walk-append x y))
                  (walk-end y)))
  :enable walk-end)

(defrule walk-edges-of-walk-append
  (implies (equal (walk-end x) (walk->start y))
           (equal (walk-edges (walk-append x y))
                  (treeset::union (walk-edges x) (walk-edges y))))
  :enable (walk-end
           walk-edges))

(defrule walk-in-of-walk-append
  (implies (equal (walk-end x) (walk->start y))
           (equal (walk-in (walk-append x y) graph)
                  (and (walk-in x graph)
                       (walk-in y graph))))
  :enable walk-in)

;; Joining two walks in a graph always gives a walk in the graph.

(defrule walk-in-of-walk-append-when-walk-in-and-walk-in
  (implies (and (walk-in x graph)
                (walk-in y graph))
           (walk-in (walk-append x y) graph))
  :cases ((equal (walk-end x) (walk->start y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthy walk-append-extra-rules
  '(walk-append-when-not-equal-of-walk-end-and-walk->start))
