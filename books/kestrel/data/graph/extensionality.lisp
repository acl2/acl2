; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "edges-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "graph"))
(local (include-book "nodes"))
(local (include-book "edges"))
(local (include-book "internal/extensionality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc extensionality
  :parents (graph)
  :short "A @(see graph) is determined by its nodes and edges."
  :long
  (xdoc::topstring
    (xdoc::p
      "Two graphs are equal exactly when they have the same @(tsee nodes) and
       the same @(tsee edges). This is the logical view of a graph: most
       properties of the graph operations are stated in terms of those two
       sets, and proved by enabling the @('extensionality') rule.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled extensionality-no-backchain-limit
  (implies (and (graphp x)
                (graphp y)
                (equiv x$ (double-rewrite x))
                (equiv y$ (double-rewrite y)))
           (equal (equal x y)
                  (and (equal (nodes x$) (nodes y$))
                       (equal (edges x$) (edges y$)))))
  :enable (nodes
           edges
           adj-list-extensionality
           break-abstraction))

(defruled extensionality
  (implies (and (graphp x)
                (graphp y)
                (equiv x$ (double-rewrite x))
                (equiv y$ (double-rewrite y)))
           (equal (equal x y)
                  (and (equal (nodes x$) (nodes y$))
                       (equal (edges x$) (edges y$)))))
  :rule-classes ((:rewrite :backchain-limit-lst (1 1 nil nil)))
  :by extensionality-no-backchain-limit)
