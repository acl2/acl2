;; Julien Schmaltz
;; August 1st 2005
;; File: xy-routing.lisp
;; Application of GeNoC-routing to an XY-routing algorithm

(in-package "ACL2")
;; we import the generic definition
(include-book "../../../generic-modules/GeNoC-routing")
;; we import the book with node definition for a 2D-mesh
(include-book "../../nodeset/2D-mesh-nodeset")

;; we load the arithmetic books
(include-book "arithmetic-3/bind-free/top" :dir :system)

;(set-non-linearp t)
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

;;------------------------------------------------------------------------
;;
;;                Definition of the Routing Algorithm
;;
;;------------------------------------------------------------------------
;; ALGORITHM
;; from = (x_o y_o)
;; dest = (x_d y_d)
;; if x_o = x_d and y_o = y_d
;;    then we stop
;; else
;;    if x_o /= x_d then
;;       if x_d < x_o then we go one step west
;;       else we go one step east
;;       endif
;;    else
;;       if y_d < y_o then we go one step south
;;       else we go one step north
;;       endif
;;   endif
;; endif


;; 1 Measure
;; ------------
;; measure = | x_d - x_o | + | y_d - y_o |
;; The measure is just the sum of the absolute value of the difference of the
;; coordinates. We force the result to be a natural.


(defun dist (s d)
  (if (or (not (coordinatep s)) (not (coordinatep d)))
      0
    (let ((s_x (car s))
          (s_y (cadr s))
          (d_x (car d))
          (d_y (cadr d)))
      (+ (abs (- d_x s_x)) (abs (- d_y s_y))))))

(defthm O-P-dist
  ;; the measure must be an ordinal
  (O-P (dist from to)))

;; 2 Routing function
;; ---------------------
;; we define here the basic routing function
(defun xy-routing (from to)
  (declare (xargs :measure (dist from to)))
  ;; from = (x_o y_o) dest = (x_d y_d)
  (if (or (not (coordinatep from))
          (not (coordinatep to)))
      nil
    (let ((x_d (car to))
          (y_d (cadr to))
          (x_o (car from))
          (y_o (cadr from)))
      (if (and (equal x_d x_o)  ;; x_d = x_o
               (equal y_d y_o)) ;; y_d = y_o
          ;; if the destination is equal to the current node, we stop
          (cons from nil)
        (if (not (equal x_d x_o))  ;; x_d /= x_o
            (if (< x_d x_o)
                ;; the x-destination is on the descending x
                (cons from (xy-routing (list (- x_o 1) y_o) to))
              ;; x_d > x_o
              (cons from (xy-routing (list (+ x_o 1) y_o) to)))
          ;; otherwise we test the y-direction
          ;; y_d /= y_o
          ;; x_d = x_o
          (if (< y_d y_o)
              (cons from (xy-routing (list x_o (- y_o 1)) to))
            ;; y_d > y_o
            (cons from (xy-routing (list x_o (+ y_o 1)) to))))))))

;; 3 Validation of the basic routing function
;; -------------------------------------------
;; we prove first some lemmas on the basic function

;; 3.a some trivial properties
(defthm first-XY-routing
  ;; the first element is the origin
  (implies (and (coordinatep from)
                (coordinatep to))
           (equal (car (XY-routing from to))
                  from)))

(defthm last-XY-routing
  ;; the last element is the destination
  (implies (and (coordinatep from)
                (coordinatep to))
           (equal (car (last (XY-routing from to)))
                  to)))

(defthm XY-routing-len->=-2
  ;; a route has at least two elements
  (implies (and (coordinatep from) (coordinatep to)
                (not (equal from to)))
           (<= 2 (len (xy-routing from to)))))


;; 3.b A route is a subset of nodeset

;; now we prove that a route is a subsetp of the set of existing nodes
;; NodeSet

;; the tactic is the following:
;; a/ we prove that a list of valid coordinates with every x less than
;; x-dim and every y less than y-dim is a subset of coord-gen(x-dim, y-dim)
;; b/ we prove that routing satisfies the above properties

(defun all-x-<-max (L x-max)
  ;; we define a function that checks that every x-coordinate is less than x-max
  (if (endp L)
      t
    (and (< (caar L) x-max) ;; x_i < x-max
         (all-x-<-max (cdr L) x-max))))

(defun all-y-<-max (L y-max)
  ;; we define a function that checks that every y-coordinate is less than y-max
  (if (endp L)
      t
    (and (< (cadar L) y-max) ;; y_i < y-max
         (all-y-<-max (cdr L) y-max))))

(defthm member-equal-x-dim-gen
  ;; we prove that if x is a coordinate with its first part less than x-dim
  ;; and its second part equal to y-dim then x is a member of x-dim-gen.
  (implies (and (coordinatep x) (< (car x) x-dim)
                (natp x-dim)
                (natp y-dim)
                (equal (cadr x) y-dim))
           (member-equal x (x-dim-gen x-dim y-dim))))

(defthm member-coord-generator-1
  ;; we prove something similar for the function coord-generator-1
  ;; both parts of x are less than x-dim and y-dim implies that x
  ;; is a member of coord-generator-1
  (implies (and (coordinatep x) (natp y-dim)
                (natp x-dim)
                (< (car x) x-dim) (< (cadr x) y-dim))
           (member-equal x (coord-generator-1 x-dim y-dim))))

(defthm tactic1
  ;; we prove that our tactic is valid for membership
  (implies (and (2D-mesh-nodesetp L) (consp L)
                (all-x-<-max L x-dim) (natp x-dim)
                (all-y-<-max L y-dim) (natp y-dim))
           (member-equal (car L) (coord-generator-1 x-dim y-dim))))

(defthm member-equal-rev
  ;; this should go elsewhere
  (implies (member-equal x S)
           (member-equal x (rev S))))

(defthm tactic1-top
  ;; we now prove that our tactic is valid
  (implies (and (2D-mesh-nodesetp L)
                (all-x-<-max L x-dim) (natp x-dim)
                (all-y-<-max L y-dim) (natp y-dim))
           (subsetp L (coord-gen x-dim y-dim)))
  :hints (("GOAL"
           :in-theory (enable coord-gen))))

;; Then the strategy is to prove that xy-routing satisfies
;; the hypotheses of this theorem

(defthm 2D-mesh-nodesetp-xy-routing
  ;; 1st hyp is trivial
  ;; a route is a list of valid coordinates
  (2D-mesh-nodesetp (xy-routing from to)))

;; let's go to the more tricky part.
;; First, every x-coord of any nodes produced by function xy-routing
;; is strictly less than 1 + Max(from_x, to_x)
(defthm all-x-<-max-+
  ;; lemma added for compability between 3.1 and 3.2.1
  (implies (all-x-<-max x y)
	   (all-x-<-max x (+ 1 y))))

(defthm routing-all-x-less
  (all-x-<-max (xy-routing from to)
               (1+ (max (car from) (car to)))))

;; and every y-coord is strictly less than 1 + Max(from_y, to_y)
(defthm routing-all-y-less
  (all-y-<-max (xy-routing from to)
               (1+ (max (cadr from) (cadr to)))))

(defthm xy-routing-subsetp-coord-max
  (implies (and (coordinatep from) (coordinatep to))
           (subsetp (xy-routing from to)
                    (coord-gen (1+ (max (car from) (car to)))
                               (1+ (max (cadr from) (cadr to))))))
  :hints (("GOAL"
           :in-theory (disable max))))


;; then our goal is to prove that coor-gen(NX,NY) produces nodes
;; with x-coord < NX and y-coord < NY

(defthm all-x-<-max-minus-1
  ;; lemma needed to be able to enlarge the majoration
  (implies (all-x-<-max L (1- x))
           (all-x-<-max L x)))

(defthm all-x-<-max-x-dim-gen
  ;; we prove that x-dim-gen generates nodes with x-coord < x
  (all-x-<-max (x-dim-gen x y) x))

(defthm all-x-<-max-coord-gen
  ;; we propagate this property to coord-generator-1 which calls x-dim-gen
  (all-x-<-max (coord-generator-1 x y) x))

(defthm all-x-<-max-member-equal
  (implies (and (all-x-<-max L x)
                (member-equal y L))
           (< (car y) x)))

(defthm all-x-<-max-rev
  ;; all-x-<-max is preserved if we reverse its arguments
  (implies (all-x-<-max L x)
           (all-x-<-max (rev L) x)))

(defthm all-y-<-max-x-dim-gen
  (all-y-<-max (x-dim-gen x y) (+ 1 y)))

(defthm all-y-<-max-minus-1
  (implies (all-y-<-max L (+ -1 x))
           (all-y-<-max L x)))

(defthm all-y-<-max-append
  (implies (and (all-y-<-max L1 x)
                (all-y-<-max L2 x))
           (all-y-<-max (append L1 L2) x)))

(defthm all-y-<-max-coord-gen-1
  (all-y-<-max (coord-generator-1 x y) y)
  :hints (("SubGoal *1/2"
           :cases ((all-y-<-max (x-dim-gen x (+ -1 y)) y)))
          ("SubGoal *1/2.2"
           :use (:instance all-y-<-max-x-dim-gen (y (+ -1 y)))
           :in-theory (disable all-y-<-max-x-dim-gen))))

(defthm rev-append
  ;; should be put elsewhere
  (equal (rev (append x y))
         (append (rev y) (rev x))))

(defthm all-y-<-max-rev
  (implies (all-y-<-max L x)
           (all-y-<-max (rev L) x)))

(defthm all-max-coord-gen
  (and (all-x-<-max (coord-gen X Y) X)
       (all-y-<-max (coord-gen X Y) Y))
  :hints (("GOAL"
           :in-theory (enable coord-gen))))

;; now we prove that if (x1 y1) and (x2 y2) belong to (coord-gen NX NY)
;; then Max(x1, x2) < NX and Max(y1, y2) < NY

(defthm member-equal-x-dim-gen-plus
  (implies (and (<= x1 x2)  (natp x1) (< 0 x1) (natp x2))
           (member-equal (list (+ -1 x1) y)
                         (x-dim-gen x2 y))))

(defthm subsetp-x-dim-gen-plus
  (implies (and (natp x1) (natp x2) (<= x1 x2))
           (subsetp (x-dim-gen x1 y)
                    (x-dim-gen x2 y))))

(defthm subsetp-append-2
  ;; should be put elsewhere
  (implies (and (subsetp x L)
                (subsetp y L))
           (subsetp (append x y) L)))

(defthm all-y-<-max-member-equal
  (implies (and (all-y-<-max L y)
                (member-equal e L))
           (< (cadr e) y)))

(defthm all-max-member-equal
  (implies (and (member-equal x L)
                (all-x-<-max L x-max)
                (all-y-<-max L y-max)
                (member-equal y L))
           (and (< (max (car x) (car y)) x-max)
                (< (max (cadr x) (cadr y)) y-max))))

;; then we prove that if x < NX and y < NY then
;; (coord-gen x y) is a subset of (coord-gen NX NY)

(defthm subsetp-x-dim-gen-coord-gen-1
  (implies (and (natp x1) (natp x2) (natp y1) (natp y2)
                (<= x1 x2) (< y1 y2))
           (subsetp (x-dim-gen x1 y1)
                    (coord-generator-1 x2 y2))))

(defthm subsetp-coord-gen-1
  (implies (and (<= x1 x2) (<= y1 y2)
                (natp x1) (natp x2) (natp y1) (natp y2))
           (subsetp (coord-generator-1 x1 y1)
                    (coord-generator-1 x2 y2))))

(defthm subsetp-rev-2
  ;; should go elsewhere
  (implies (subsetp x y)
           (subsetp (rev x) (rev y))))

;; here comes our main lemma:
(defthm subsetp-coord-plus
  (implies (and (<= x1 x2) (<= y1 y2)
                (natp x1) (natp x2) (natp y1) (natp y2))
           (subsetp (coord-gen x1 y1)
                    (coord-gen x2 y2)))
  :hints (("GOAL"
           :in-theory (enable coord-gen))))

;; and now using the transitivity of subsetp we conclude:
(defthm trans-subsetp
  ;; should be put elsewhere
  (implies (and (subsetp x y) (subsetp y z))
           (subsetp x z)))


(defthm xy-routing-subsetp-nodeset
  ;; now we want to prove that if NodeSet = coord-gen x y, then
  ;; route is a subsetp of NodeSet.
  ;; from and to must be members of NodeSet
  ;; from and to must not be equal
  (implies (and (not (equal from to))
                (coordinatep from) (coordinatep to)
                (natp X) (natp Y)
                ;; it should be member-equal
                (member-equal from (coord-gen X Y))
                (member-equal to (coord-gen X Y)))
           (subsetp (xy-routing from to) (coord-gen X Y)))
  :otf-flg t
  :hints (("GOAL"
           :use ((:instance all-max-member-equal
                            (L (coord-gen X Y))
                            (x from) (y to)
                            (x-max X) (y-max Y))
                 (:instance xy-routing-subsetp-coord-max))
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable coord-gen coordinatep natp subsetp
                               all-max-member-equal
                               xy-routing-subsetp-coord-max)
           :do-not-induct t)
          ("Subgoal 4"
           :use (:instance subsetp-coord-plus
                           (x1 (+ 1 (car from))) (x2 x)
                           (y1 (+ 1 (cadr from))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 3"
           :use (:instance subsetp-coord-plus
                           (x1 (+ 1 (car from))) (x2 x)
                           (y1 (+ 1 (cadr to))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 2"
           :use (:instance subsetp-coord-plus
                           (x1 (+ 1 (car to))) (x2 x)
                           (y1 (+ 1 (cadr from))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 1"
           :use (:instance subsetp-coord-plus
                           (x1 (+ 1 (car to))) (x2 x)
                           (y1 (+ 1 (cadr to))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))))



;; 4 Definition compatible with GeNoC
;; -----------------------------------

;; 4.a Definition of the function
(defun xy-routing-top (Missives)
  (if (endp Missives)
      nil
    (let* ((miss (car Missives))
           (from (OrgM miss))
           (to (DestM miss))
           (id (IdM miss))
           (frm (FrmM miss)))
      (cons (list id frm (list (xy-routing from to)))
            (xy-routing-top (cdr Missives))))))

(defun XYRouting (Missives NodeSet)
  (declare (ignore NodeSet))
  (xy-routing-top Missives))

;; 4.b Proof of compliance
;; ------------------------

;(defun bind-to-itself (x)
;  (list (cons x x)))

;; need to prove CorrectRoutesp and TrLstp and ToMissives
;; 1. ToMissives seems to be simple
(defthm 2D-mesh-nodesetp-member-equal
  (implies (and ;(bind-free (bind-to-itself x))
                ;; ask matt why it does not work
                (2D-mesh-nodesetp x)
                (member-equal e x))
           (Coordinatep e)))

(defthm XYRouting-Missives
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (Missivesp Missives NodeSet)
                  (mesh-hyps Params))
           (equal (ToMissives (xy-routing-top Missives))
                  Missives)))
  :otf-flg t
  :hints (("GOAL"
           :induct (xy-routing-top Missives)
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable coordinatep)
           :do-not-induct t)
          ("Subgoal *1/2"
           :use ((:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (OrgM (car Missives))))
                 (:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (DestM (car Missives)))))
           :in-theory (disable 2D-mesh-nodesetp-member-equal
                               coordinatep))))

;; 2. TrLstp
(defthm consp-xy-routing
  ;; should be systematically added
  (implies (and (coordinatep from)
                (coordinatep to))
           (consp (xy-routing from to))))

(defthm consp-xy-routing-cdr
  ;; should be systematically added
  (implies (and (coordinatep from) (not (equal from to))
                (coordinatep to))
           (consp (cdr (xy-routing from to)))))

(defthm V-ids-xy-routing-=-M-ids
  ;; this one too ...
  (equal (V-ids (xy-routing-top Missives))
         (M-ids Missives)))

(defthm TrLstp-XYRouting
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (Missivesp Missives NodeSet)
                  (mesh-hyps Params))
;                  (equal NodeSet (mesh-nodeset-gen Params)))
             (TrLstp (xy-routing-top Missives))))
  :hints (("GOAL"
           :induct (xy-routing-top missives))
          ("Subgoal *1/2"
           :use ((:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (OrgM (car Missives))))
                 (:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (DestM (car Missives)))))
           :in-theory (disable 2D-mesh-nodesetp-member-equal
                               coordinatep))))

;; 3. CorrectRoutesp
(defthm CorrectRoutesp-XYRouting
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (mesh-hyps Params)
                  (Missivesp Missives NodeSet))
           (CorrectRoutesp (xy-routing-top Missives)
                           Missives NodeSet)))
  :hints (("GOAL"
           :induct (xy-routing-top Missives)
           :do-not-induct t)
          ("Subgoal *1/2"
           :use ((:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (OrgM (car Missives))))
                 (:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (DestM (car Missives)))))
           :in-theory (disable 2D-mesh-nodesetp-member-equal
                               coordinatep))))


;; now we can prove that the XY-routing algorithm is compliant
;; to the GeNoC-routing.
(defthm check-compliance-XY-routing
  t
  :rule-classes nil
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use (:functional-instance
                 ToMissives-Routing
                 (NodeSetGenerator mesh-nodeset-gen)
                 (NodeSetp 2D-mesh-nodesetp)
                 (ValidParamsp mesh-hyps)
                 (Routing XYRouting))
           :in-theory (disable ToMissives-Routing
                               mesh-nodeset-gen
                               trlstp mesh-hyps
                               Missivesp))
          ("Subgoal 3" ; changed after v4-3 from "Subgoal 4", for tau system
           :in-theory (enable mesh-hyps))))
