
; Applies isomorphic type refinement to drone planning system
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dp-impl")
(include-book "drone-state-iso")

(include-book "kestrel/apt/simplify" :dir :system)
(include-book "kestrel/apt/propagate-iso" :dir :system)

(include-book "kestrel/apt/isodata" :dir :system)

(local (apt::set-default-input-old-to-new-enable t)) ; enable generated old to new rules

;; Generate isomorphic versions of functions needed for refining extend-path-taken
;;
(apt::propagate-iso dr-state-p-to-dr-state-ext-p
  ((dr-state dr-state-ext
             dr-state-~>dr-state-ext
             dr-state-ext-~>dr-state
             (* * * *) => (dr-state-p))
   (dr-state->drone-id dr-state-ext0->drone-id
                       dr-state->drone-id-~>dr-state-ext0->drone-id
                       dr-state-ext0->drone-id-~>dr-state->drone-id
                       (dr-state-p) => *)
   (dr-state->dgraph dr-state-ext0->dgraph
                     dr-state->dgraph-~>dr-state-ext0->dgraph
                     dr-state-ext0->dgraph-~>dr-state->dgraph
                     (dr-state-p) => *)
   (dr-state->visited-nodes dr-state-ext0->visited-nodes
                            dr-state->visited-nodes-~>dr-state-ext0->visited-nodes
                            dr-state-ext0->visited-nodes-~>dr-state->visited-nodes
                            (dr-state-p) => *)
   (dr-state->path-taken dr-state-ext0->path-taken
                         dr-state->path-taken-~>dr-state-ext0->path-taken
                         dr-state-ext0->path-taken-~>dr-state->path-taken
                         (dr-state-p) => *))
  :iso-rules (dr-state->drone-id-from-dr-state-ext
              dr-state->path-taken-from-dr-state-ext
              dr-state-ext0->dgraph-~>dr-state->dgraph
              to-dr-state-ext-dr-state)
  :first-event dr-state*-p
  :last-event valid-plan-p-node-path-p)

;; Refine extend-path-taken using isodata and simplify
;;
(apt::isodata extend-path-taken (((drn-st :result) good-dr-state-p-iso-good-dr-state-ext-p)))


;; Rule necessary to get best simplification
(defthmd set-difference-equal-of-append-rev
  (equal (set-difference-equal x (append y z))
         (set-difference-equal (set-difference-equal x z) y))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

; Matt K. mod: Guard verification fails in ACL2(p) with waterfall-parallelism
; enabled for the call (simplify extend-path-taken$1 ...) below.
(set-waterfall-parallelism nil)

(simplify extend-path-taken$1
  :assumptions ((good-dr-state-ext-p drn-st))
  :enable (dr-state-ext set-difference-equal-of-append-rev)
  :simplify-guard t)

(defthm good-dr-state-ext-p-extend-path-taken$2
  (implies (good-dr-state-ext-p drn-st)
           (good-dr-state-ext-p (extend-path-taken$2 drn-st plan)))
  :hints (("Goal" :use extend-path-taken$1-new-representation)))
(defthm extend-path-taken-~>extend-path-taken$2
  (implies (good-dr-state-p drn-st)
           (equal (extend-path-taken drn-st plan)
                  (from-dr-state-ext (extend-path-taken$2 (to-dr-state-ext drn-st)
                                                          plan)))))
(defthmd extend-path-taken$2-~>extend-path-taken
  (implies (good-dr-state-ext-p drn-st)
           (equal (extend-path-taken$2 drn-st plan)
                  (to-dr-state-ext (extend-path-taken (from-dr-state-ext drn-st)
                                                      plan)))))
;; Propagate iso to all the remaining users
;;
(apt::propagate-iso dr-state-p-to-dr-state-ext-p
  ((dr-state dr-state-ext
             dr-state-~>dr-state-ext
             dr-state-ext-~>dr-state
             (* * * *) => dr-state-p)
   (dr-state->drone-id dr-state-ext0->drone-id
                       dr-state->drone-id-~>dr-state-ext0->drone-id
                       dr-state-ext0->drone-id-~>dr-state->drone-id
                       (dr-state-p) => *)
   (dr-state->dgraph dr-state-ext0->dgraph
                     dr-state->dgraph-~>dr-state-ext0->dgraph
                     dr-state-ext0->dgraph-~>dr-state->dgraph
                     (dr-state-p) => *)
   (dr-state->visited-nodes dr-state-ext0->visited-nodes
                            dr-state->visited-nodes-~>dr-state-ext0->visited-nodes
                            dr-state-ext0->visited-nodes-~>dr-state->visited-nodes
                            (dr-state-p) => *)
   (dr-state->path-taken dr-state-ext0->path-taken
                         dr-state->path-taken-~>dr-state-ext0->path-taken
                         dr-state-ext0->path-taken-~>dr-state->path-taken
                         (dr-state-p) => *)
   ;; Added  to previous call to propagate-iso
   (extend-path-taken extend-path-taken$2
                      extend-path-taken-~>extend-path-taken$2
                      extend-path-taken$2-~>extend-path-taken
                      (dr-state-p *) => dr-state-p))
  :iso-rules (dr-state->drone-id-from-dr-state-ext
              dr-state->path-taken-from-dr-state-ext
              dr-state-ext0->dgraph-~>dr-state->dgraph
              to-dr-state-ext-dr-state)
  :first-event dr-state*-p
  :last-event run-drone-system)
