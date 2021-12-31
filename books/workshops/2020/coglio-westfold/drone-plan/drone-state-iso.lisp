; Defines an isomorphic version of dr-state with FD components; initially just visited nodes and current pos
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dp-impl-support")

(include-book "kestrel/std/util/defiso" :dir :system)


;;; Extended Drone State

(fty::defprod dr-state-ext0
  ((drone-id drone-id)
   (dgraph dgraph-p)
   (visited-nodes node-list)
   (path-taken node-list)
   (unvisited-nodes node-list)
   (currentpos node-or-null)))

(defthm nodep-of-dr-state-ext0->currentpos
  (implies (dr-state-ext0->currentpos drn-st)
           (nodep (dr-state-ext0->currentpos drn-st)))
  :hints (("Goal" :use (:instance nodep-or-null-of-dr-state-ext0->currentpos (x drn-st))
           :in-theory (disable nodep-or-null-of-dr-state-ext0->currentpos))))

;; Backward isomorphism function
(define from-dr-state-ext ((drn-st-ext dr-state-ext0-p))
  :returns (drn-st dr-state-p)
  (dr-state (dr-state-ext0->drone-id drn-st-ext)
            (dr-state-ext0->dgraph drn-st-ext)
            (dr-state-ext0->visited-nodes drn-st-ext)
            (dr-state-ext0->path-taken drn-st-ext))
///
(defthm dr-state->drone-id-from-dr-state-ext
  (equal (dr-state->drone-id (from-dr-state-ext drn-st))
         (dr-state-ext0->drone-id (double-rewrite drn-st))))
(defthm dr-state->dgraph-from-dr-state-ext
  (equal (dr-state->dgraph (from-dr-state-ext drn-st))
         (dr-state-ext0->dgraph (double-rewrite drn-st))))
(defthm dr-state->visited-nodes-from-dr-state-ext
  (equal (dr-state->visited-nodes (from-dr-state-ext drn-st))
         (dr-state-ext0->visited-nodes (double-rewrite drn-st))))
(defthm dr-state->path-taken-from-dr-state-ext
  (equal (dr-state->path-taken (from-dr-state-ext drn-st))
         (dr-state-ext0->path-taken (double-rewrite drn-st))))
) ; from-dr-state-ext

;; Define dr-state-ext-p to be isomorphic to dr-state
(define dr-state-ext-p (drn-st)
  :returns (b booleanp)
  (and (dr-state-ext0-p drn-st)
       (equal (dr-state-ext0->unvisited-nodes drn-st)
              (set-difference-equal (dgraph->nodes (dr-state-ext0->dgraph drn-st))
                                    (dr-state-ext0->visited-nodes drn-st)))
       (equal (dr-state-ext0->currentpos drn-st)
              (drone-location (from-dr-state-ext drn-st))))
///
(defthm dr-state-ext-p-implies-non-nil
  (implies (not (double-rewrite drn-st-ext))
           (not (dr-state-ext-p drn-st-ext))))
(defthm dr-state-ext-p-dr-state-ext0-p
  (implies (dr-state-ext-p drn-st)
           (dr-state-ext0-p drn-st)))
(defthm dr-state-ext-p-unvisited-nodes
  (implies (dr-state-ext-p drn-st)
           (equal (set-difference-equal (dgraph->nodes (dr-state-ext0->dgraph drn-st))
                                        (dr-state-ext0->visited-nodes drn-st))
                  (dr-state-ext0->unvisited-nodes drn-st))))
(defthm dr-state-ext-p-currentpos
  (implies (dr-state-ext-p drn-st)
           (equal (dr-state-ext0->currentpos drn-st)
                  (drone-location (from-dr-state-ext drn-st)))))
(defthm memberp-visited-nodes
  (implies (and (dr-state-ext-p drn-st)
                (memberp n (dgraph->nodes (dr-state-ext0->dgraph drn-st))))
           (equal (not (memberp n (dr-state-ext0->visited-nodes drn-st)))
                  (memberp n (dr-state-ext0->unvisited-nodes drn-st)))))
) ; dr-state-ext-p

;; isomorphic construct to dr-state
(define dr-state-ext ((drone-id drone-id-p)
                      (dgraph dgraph-p)
                      (visited-nodes node-list-p)
                      (path-taken node-list-p))
  :returns (drn-ext dr-state-ext-p :hyp :guard
                    :hints (("Goal" :in-theory (enable dr-state-ext-p dr-state-ext0 drone-location
                                                       dr-state-ext0->unvisited-nodes
                                                       dr-state-ext0->dgraph dr-state-ext0->visited-nodes
                                                       dr-state-ext0->path-taken dr-state-ext0->currentpos
                                                       dr-state-ext0-p))))
  (dr-state-ext0 drone-id dgraph visited-nodes path-taken
                 (set-difference-equal (dgraph->nodes dgraph)
                                       visited-nodes)
                 (if (consp path-taken) (car (last path-taken)) nil))
///
(defthm dr-state-ext0->drone-id-of-dr-state-ext
  (implies (drone-id-p drone-id)
           (equal (dr-state-ext0->drone-id (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  drone-id)))
(defthm dr-state-ext0->dgraph-of-dr-state-ext
  (implies (dgraph-p dgraph)
           (equal (dr-state-ext0->dgraph (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  dgraph)))
(defthm dr-state-ext0->visited-nodes-of-dr-state-ext
  (implies (node-list-p visited-nodes)
           (equal (dr-state-ext0->visited-nodes (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  visited-nodes)))
(defthm dr-state-ext0->path-taken-of-dr-state-ext
  (implies (node-list-p path-taken)
           (equal (dr-state-ext0->path-taken (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  path-taken)))
(defthm dr-state-ext0->unvisited-nodes-of-dr-state-ext
  (implies (and (drone-id-p drone-id)
                (dgraph-p dgraph))
           (equal (dr-state-ext0->unvisited-nodes (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  (set-difference-equal (dgraph->nodes dgraph)
                                        visited-nodes))))
(defthm dr-state-ext0->currentpos-of-dr-state-ext
  (implies (node-list-p path-taken)
           (equal (dr-state-ext0->currentpos (dr-state-ext drone-id dgraph visited-nodes path-taken))
                  (if (consp path-taken) (car (last path-taken)) nil))))
(defthm dr-state-ext-p-dr-state-ext-id
  (implies (dr-state-ext-p drn-st-ext)
           (equal (dr-state-ext (dr-state-ext0->drone-id drn-st-ext)
                                (dr-state-ext0->dgraph drn-st-ext)
                                (dr-state-ext0->visited-nodes drn-st-ext)
                                (dr-state-ext0->path-taken drn-st-ext))
                  drn-st-ext))
   :hints (("Goal" :in-theory (enable drone-location))))
) ; dr-state-ext

(defthmd dr-state-~>dr-state-ext
  (equal (dr-state drn-id g visited-nodes path-taken)
         (from-dr-state-ext (dr-state-ext drn-id g visited-nodes path-taken)))
  :hints (("Goal" :in-theory (enable from-dr-state-ext dr-state-ext))))

;; Forward isomorphism function
(define to-dr-state-ext ((drn-st dr-state-p))
  :returns (drn-st-ext dr-state-ext-p :hyp :guard)
  (dr-state-ext (dr-state->drone-id drn-st)
                (dr-state->dgraph drn-st)
                (dr-state->visited-nodes drn-st)
                (dr-state->path-taken drn-st))
///
(defthm to-dr-state-ext-dr-state
  (implies (and (node-list-p visited-nodes)
                (node-list-p path-taken))
           (equal (to-dr-state-ext (dr-state drone-id dgraph visited-nodes path-taken))
                  (dr-state-ext drone-id dgraph visited-nodes path-taken)))
  :hints (("Goal" :in-theory (enable drone-location dr-state-ext))))
(defthm dr-state-ext0->drone-id-to-dr-state-ext
  (equal (dr-state-ext0->drone-id (to-dr-state-ext drn-st))
         (dr-state->drone-id drn-st)))
(defthm dr-state-ext0->dgraph-to-dr-state-ext
  (equal (dr-state-ext0->dgraph (to-dr-state-ext drn-st))
         (dr-state->dgraph drn-st)))
(defthm dr-state-ext0->visited-nodes-to-dr-state-ext
  (equal (dr-state-ext0->visited-nodes (to-dr-state-ext drn-st))
         (dr-state->visited-nodes drn-st)))
(defthm dr-state-ext0->path-taken-to-dr-state-ext
  (equal (dr-state-ext0->path-taken (to-dr-state-ext drn-st))
         (dr-state->path-taken drn-st))
  :hints (("Goal" :in-theory (enable dr-state-ext))))
(defthmd dr-state-ext-~>dr-state
  (implies (and (node-list-p visited-nodes)
                (node-list-p path-taken))
           (equal (dr-state-ext drn-id g visited-nodes path-taken)
                  (to-dr-state-ext (dr-state drn-id g visited-nodes path-taken))))
  :hints (("Goal" :in-theory (enable drone-location dr-state-ext))))
) ; to-dr-state-ext


(defiso dr-state-p-to-dr-state-ext-p
  dr-state-p dr-state-ext-p to-dr-state-ext from-dr-state-ext
  :thm-enable :all-nonguard
  :hints (:beta-of-alpha (("Goal" :in-theory (enable from-dr-state-ext to-dr-state-ext)))
          :alpha-of-beta (("Goal" :in-theory (enable from-dr-state-ext to-dr-state-ext)))))

;; Forward isomorphism theorems for destructors of dr-state
(defthmd dr-state->drone-id-~>dr-state-ext0->drone-id
  (equal (dr-state->drone-id drn-st)
         (dr-state-ext0->drone-id (to-dr-state-ext drn-st))))
(defthmd dr-state->dgraph-~>dr-state-ext0->dgraph
  (equal (dr-state->dgraph drn-st)
         (dr-state-ext0->dgraph (to-dr-state-ext drn-st))))
(defthmd dr-state->visited-nodes-~>dr-state-ext0->visited-nodes
  (equal (dr-state->visited-nodes drn-st)
         (dr-state-ext0->visited-nodes (to-dr-state-ext drn-st))))
(defthmd dr-state->path-taken-~>dr-state-ext0->path-taken
  (equal (dr-state->path-taken drn-st)
         (dr-state-ext0->path-taken (to-dr-state-ext drn-st))))

;; Backward isomorphism theorems for destructors of dr-state
(defthmd dr-state-ext0->drone-id-~>dr-state->drone-id
  (equal (dr-state-ext0->drone-id drn-st)
         (dr-state->drone-id (from-dr-state-ext drn-st))))
(defthmd dr-state-ext0->dgraph-~>dr-state->dgraph
  (equal (dr-state-ext0->dgraph drn-st)
         (dr-state->dgraph (from-dr-state-ext drn-st))))
(defthmd dr-state-ext0->visited-nodes-~>dr-state->visited-nodes
  (equal (dr-state-ext0->visited-nodes drn-st)
         (dr-state->visited-nodes (from-dr-state-ext drn-st))))
(defthmd dr-state-ext0->path-taken-~>dr-state->path-taken
  (equal (dr-state-ext0->path-taken drn-st)
         (dr-state->path-taken (from-dr-state-ext drn-st))))

(defthm dr-state-ext-p-unvisited-nodes-rev
  (implies (dr-state-ext-p drn-st)
           (equal (set-difference-equal (dgraph->nodes (dr-state-ext0->dgraph drn-st))
                                        (dr-state-ext0->visited-nodes drn-st))
                  (dr-state-ext0->unvisited-nodes drn-st))))

(defthm dr-state-ext-p-currentpos-rev
  (implies (dr-state-ext-p drn-st)
           (equal (drone-location (from-dr-state-ext drn-st))
                  (dr-state-ext0->currentpos drn-st))))

(defthm dr-state-ext-p-currentpos-rev-2
  (implies (dr-state-ext-p drn-st)
           (equal (car (last (dr-state-ext0->path-taken drn-st)))
                  (dr-state-ext0->currentpos drn-st)))
  :hints (("Goal" :use dr-state-ext-p-currentpos-rev
           :in-theory (e/d (drone-location)
                           (dr-state-ext-p-currentpos-rev)))))

(in-theory (disable dr-state-ext-p-unvisited-nodes dr-state-ext-p-currentpos))

(theory-invariant (incompatible (:rewrite dr-state-ext-p-unvisited-nodes)
                                (:rewrite dr-state-ext-p-unvisited-nodes-rev)))
(theory-invariant (incompatible (:rewrite dr-state-ext-p-currentpos)
                                (:rewrite dr-state-ext-p-currentpos-rev)))
(theory-invariant (incompatible (:rewrite dr-state-ext-p-currentpos)
                                (:rewrite dr-state-ext-p-currentpos-rev-2)))
