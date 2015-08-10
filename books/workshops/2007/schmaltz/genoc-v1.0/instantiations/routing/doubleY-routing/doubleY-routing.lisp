;; Julien Schmaltz
;; Sept. 19th 2005
;; File: doubleY-routing.lisp
;; modeling of an adaptive routing algorithm
;; we consider a 2D-mesh. We compute all possible minimal paths
;; between two nodes.
;; The algorithm is an interleaving of XY and YX.

(in-package "ACL2")
;;; we need the xy routing algorithm
(include-book "../xy-routing/xy-routing")

;;-------------------------------------------------------------
;;
;;            I. Definition of the YX routing algorithm
;;
;;-------------------------------------------------------------

;; the distance between two nodes is the sum of the absolute values of the difference of
;; the coordinates

(defun yx-routing (from to)
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
        (if (not (equal y_d y_o))  ;; y_d /= y_o
            (if (< y_d y_o)
                ;; the y-destination is on the descending y
                (cons from (yx-routing (list x_o (- y_o 1)) to))
              ;; y_d > x_o
              (cons from (yx-routing (list x_o (+ 1 y_o)) to)))
          ;; otherwise we test the y-direction
          ;; y_d = y_o
          ;; x_d /= x_o
          (if (< x_d x_o)
              (cons from (yx-routing (list (- x_o 1) y_o) to))
            ;; x_d > x_o
            (cons from (yx-routing (list (+ 1 x_o) y_o) to))))))))

(defthm first-YX-routing
  ;; the first element  the origin
  (implies (and (coordinatep from)
                (coordinatep to))
           (equal (car (YX-routing from to))
                  from)))

(defthm consp-yx-routing
  ;; should be systematically added
  (implies (and (coordinatep from)
                (coordinatep to))
           (consp (yx-routing from to))))


(defun CloserListp (r d)
  ;; recognizes a list r of nodes such that any higher position
  ;; of the list gives a nodes that is closer to d than lower
  ;; positions. More extactly, the distance decreases by 1
  ;; if the position increases by 1,
  (if (or (endp r) (endp (cdr r)))
      t
    (and (equal (dist (cadr r) d) (1- (dist (car r) d)))
         (closerlistp (cdr r) d))))

(defthm closertlistp-yx-routing
  (closerlistp (yx-routing from to) to))

;; we now prove that it is a valid instance of GeNoC
;; most of the lemmas are deduced from theorems proven for the xy algorithm using
;; basic facts about rev


;; I.1. Validation of the basic routing function
;; -------------------------------------------
;; we prove first some lemmas on the basic function

;; I.1.a/ some trivial properties
;; --------------------------


(defthm last-YX-routing
  ;; the last element is the destination
  (implies (and (coordinatep from)
                (coordinatep to))
           (equal (car (last (YX-routing from to)))
                  to)))

(defthm last-cdr-YX-routing
  (implies (and (coordinatep from) (not (equal from to))
		(coordinatep to))
	   (equal (car (last (cdr (YX-routing from to)))) to)))

(defthm YX-routing-len->=-2
  ;; a route has at least two elements
  (implies (and (coordinatep from) (coordinatep to)
                (not (equal from to)))
           (<= 2 (len (yx-routing from to)))))


;; 3.b A route is a subset of nodeset

;; now we prove that a route is a subsetp of the set of existing nodes
;; NodeSet

;; we reuse the strategy

(defthm 2D-mesh-nodesetp-yx-routing
  (2D-mesh-nodesetp (yx-routing from to)))

;; First, every x-coord of any nodes produced by function yx-routing2
;; is strictly less than 1 + Max(from_x, to_x)
(defthm yx-routing-all-x-less
  (all-x-<-max (yx-routing from to)
               (1+ (max (car from) (car to)))))


;; and every y-coord is strictly less than 1 + Max(from_y, to_y)
(defthm yx-routing-all-y-less
  (all-y-<-max (yx-routing from to)
               (1+ (max (cadr from) (cadr to)))))

(defthm yx-routing-subsetp-coord-max
  (implies (and (coordinatep from) (coordinatep to))
           (subsetp (yx-routing from to)
                    (coord-gen (1+ (max (car from) (car to)))
                               (1+ (max (cadr from) (cadr to))))))
  :hints (("GOAL"
           :in-theory (disable max))))

(defthm yx-routing-subsetp-nodeset
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
           (subsetp (yx-routing from to) (coord-gen X Y)))
  :otf-flg t
  :hints (("GOAL"
           :use ((:instance all-max-member-equal
                            (L (coord-gen X Y))
                            (x from) (y to)
                            (x-max X) (y-max Y))
                 (:instance yx-routing-subsetp-coord-max))
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable coord-gen coordinatep natp subsetp
                               all-max-member-equal
                               yx-routing-subsetp-coord-max)
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


;; Definition compatible with GeNoC
;; -----------------------------------

;; a Definition of the function
(defun yx-routing-top (Missives)
  (if (endp Missives)
      nil
    (let* ((miss (car Missives))
           (from (OrgM miss))
           (to (DestM miss))
           (id (IdM miss))
           (frm (FrmM miss)))
      (cons (list id frm (list (yx-routing from to)))
            (yx-routing-top (cdr Missives))))))

(defun YXRouting (Missives NodeSet)
  (declare (ignore NodeSet))
  (yx-routing-top Missives))



;; Proof of compliance
;; ------------------------

;; need to prove CorrectRoutesp and TrLstp and ToMissives
;; 1. ToMissives seems to be simple

(defthm YXRouting-Missives
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (Missivesp Missives NodeSet)
                  (mesh-hyps Params))
           (equal (ToMissives (yx-routing-top Missives))
                  Missives)))
  :otf-flg t
  :hints (("GOAL"
           :induct (yx-routing-top Missives)
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

(defthm consp-yx-routing-cdr
  ;; should be systematically added
  (implies (and (coordinatep from) (not (equal from to))
                (coordinatep to))
           (consp (cdr (yx-routing from to)))))

(defthm V-ids-yx-routing-=-M-ids
  ;; this one too ...
  (equal (V-ids (yx-routing-top Missives))
         (M-ids Missives)))

(defthm TrLstp-YXRouting
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (Missivesp Missives NodeSet)
                  (mesh-hyps Params))
             (TrLstp (yx-routing-top Missives))))
  :hints (("GOAL"
           :induct (yx-routing-top missives))
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
(defthm CorrectRoutesp-YXRouting
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (mesh-hyps Params)
                  (Missivesp Missives NodeSet))
           (CorrectRoutesp (yx-routing-top Missives)
                           Missives NodeSet)))
  :hints (("GOAL"
           :induct (yx-routing-top Missives)
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
(defthm check-compliance-YXRouting
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
                 (Routing YXRouting))
           :in-theory (disable ToMissives-Routing
                               mesh-nodeset-gen
                               trlstp mesh-hyps
                               Missivesp))
	  ("Subgoal 3" ; changed after v4-3 from "Subgoal 4", for tau system
	   :in-theory (enable mesh-hyps))))

;; this concludes the verification of the YX algorithm.
;; ----------------------------------------------------

;;-------------------------------------------------------------
;;
;;      II. Definition of the Double-Y routing algorithm
;;
;;-------------------------------------------------------------

;; in this algorithm, at each node two paths are possible, along the X or the Y axis.
;; We model it as the alternative application of the xy and the yx algorithms.
;; We compute all possible minimal paths between any pair of nodes.
;; Note that for all nodes that share one coordinate with a destination,
;; there is no choice: the shortest path is to travel along the opposite axis.
;; For a given source node s, all possible routes obtained by first
;; applying the xy algorithm are computed by (a) r = xy(s,d),
;; (b) applying yx for all nodes of r that do not share
;; a coordinate with d, (c) for all such routes, applying the xy algorithm to
;; each node that do not share a coordinate with d, ...


;; II.1. Basic definitions
;; -----------------------

;; we will need to append an element to every list of a list of lists.
(defun append-e-all (e L)
  ;; L is a list of list
  ;; we append e to every list of L
  (if (endp L)
      nil
    (cons (cons e (car L))
          (append-e-all e (cdr L)))))

;; we can easily prove that the length of L is not modified
(defthm len-append-e-all
  (equal (len (append-e-all e L))
	 (len L)))

;; we will also need to append a list l to every list of a list of lists
(defun append-l-all (l Lst)
  ;; l is a list and we append it to every list in Lst
  (if (endp Lst)
      nil
    (cons (append l (car lst))
          (append-l-all l (cdr Lst)))))

;; again, the length of L is not modified by this operation
(defthm len-append-l-all
  (equal (len (append-l-all l Lst))
         (len Lst)))


;; II.2. Prefix computation
;; ------------------------

;; A subroute of a route from s to d, consists of a route from s to some
;; intermediate node.
;; Prefixes of a route r w.r.t. a destination d, are all the subroutes
;; where each node does not share a coordinate with d.

(defun extract-prefixes (r d)
  ;; compute all the possible prefixes suggested by the route
  ;; r for the destination d
  (if (or (not (coordinatep d)) (not (2D-mesh-nodesetp r)))
      nil
    (if (endp r)
        nil
      (let* ((n1 (car r)) ;; n1 is the first node of r
             (n1_x (car n1))
             (n1_y (cadr n1))
             (d_x (car d))
             (d_y (cadr d)))
        (if (or (equal n1_x d_x) (equal n1_y d_y))
            ;; nodes with one common coordinate with the destination
            ;; do not allow any choice.
            nil
          (cons (list n1) ;; n1 is a prefix
                (append-e-all n1 ;; all other prefixes start with n1 and the recursive call
                              (extract-prefixes (cdr r) d))))))))

;(extract-prefixes (xy-routing '(0 0) '(3 3)) '(3 3))
;(((0 0))
; ((0 0) (1 0))
; ((0 0) (1 0) (2 0)))

;; II.3. Get Sources
;; --------------------
;; For a route r, the "sources" w.r.t. a destination d, are the nodes that do not
;; share a coordinate with destination d.

(defun GetSources1 (r d)
  (if (or (endp r) (not (coordinatep d))
          (not (2d-mesh-nodesetp r)))
      nil
    (let* ((n1 (car r))
           (n1_x (car n1))
           (n1_y (cadr n1))
           (d_x (car d))
           (d_y (cadr d)))
      (if (or (equal n1_x d_x) (equal n1_y d_y))
          nil ;; n1 shares a coordinate with d
        (cons n1 (GetSources1 (cdr r) d))))))

(defun GetSources (r d)
  ;; we remove the first node because it has already been computed.
  ;; (it is already in the prefix)
  (GetSources1 (cdr r) d))



;; II.4 Double Y Routing
;; ---------------------


;; We need some lemmas to prove that the main function (dy1) terminates

;; the next three defthm's are used to prove that the distance from s to d decreases
;; also from the successor of s. These lemmas consider the application
;; of the xy algorithm


(defthm cadr-xy-routing
  (implies (and (coordinatep s) (coordinatep d)
                (< (car d) (car s)))
           (equal (cadr (xy-routing s d))
                  (list (+ -1 (car s)) (cadr s)))))

(defthm dist-cadr-dx-<-sx
  (implies (and (coordinatep s) (coordinatep d)
                (< (car d) (car s)))
           (equal (dist (cadr (xy-routing s d)) d)
                  (1- (dist s d)))))

(defthm dist-cadr-xy
  ;; now we prove the main theorem for xy-routing and the distance
  (implies (and (coordinatep s) (coordinatep d)
                (or (not (equal (car s) (car d)))
                    (not (equal (cadr s) (cadr d)))))
           (equal (dist (cadr (xy-routing s d)) d)
                  (1- (dist s d))))
  :hints (("Subgoal *1/1"
           :use dist-cadr-dx-<-sx
           :in-theory (disable dist-cadr-dx-<-sx))))

;; we need to prove an equivalent theorem for the application of the yx algorithm

; lemmas for the other definition
(defthm cadr-yx-routing
  (implies (and (coordinatep s) (coordinatep d)
                (< (cadr d) (cadr s)))
           (equal (cadr (yx-routing s d))
                  (list (car s) (- (cadr s) 1)))))

(defthm dist-cadr-dx-<-sx-yx
  (implies (and (coordinatep s) (coordinatep d)
                (< (cadr d) (cadr s)))
           (equal (dist (cadr (yx-routing s d)) d)
                  (1- (dist s d)))))

(defthm dist-cadr-yx-routing
  ;; now we prove the main theorem for xy-routing and the distance
  (implies (and (coordinatep s) (coordinatep d)
                (or (not (equal (car s) (car d)))
                    (not (equal (cadr s) (cadr d)))))
           (equal (dist (cadr (yx-routing s d)) d)
                  (1- (dist s d))))
  :hints (("Subgoal *1/1"
           :use dist-cadr-dx-<-sx-yx
           :in-theory (disable dist-cadr-dx-<-sx-yx))))

;; -------------------


;; to prove termination, we need to know what is the first candidate
(defthm car-getsources1
  (let ((c (getsources1 r d)))
    (implies (consp (getsources1 r d))
             (equal (car c) (car r)))))


(defun dy1 (sources d flg prefixes)
  (declare (xargs :measure
                  (dist (car sources) d)
                  :hints (("GOAL"
                           :in-theory (disable reduce-integerp-+)
                           :do-not '(eliminate-destructors generalize))
                          ("Subgoal 3"
                           :cases
                           ((consp (getsources1
                                    (cdr (yx-routing (car sources) d))
                                    d))))
                          ("Subgoal 2"
                           :cases
                           ((consp (getsources1
                                    (cdr (xy-routing (car sources) d))
                                    d))))
                          ("[1]Subgoal 2"
                           :in-theory (disable prefer-positive-addends-equal))
                          ("[1]Subgoal 1"
                           :in-theory (disable prefer-positive-addends-equal)))))
  ;; sources = a list of nodes, on which xy and yx are applied
  ;; d = destination
  ;; flg = t means "apply xy", nil means "apply yx"
  ;; prefixes = a list of prefixes that are appended to the routes
  ;; obtained by xy or yx on the nodes of sources.
  ;; The function works as follows. First, sources contains
  ;; only one node. We apply either xy or yx to get one route.
  ;; From this route we extract a list of nodes (of "sources")
  ;; that constitutes the new sources. On each of these nodes
  ;; we apply either yx or xy, und so weiter ....
  ;; We stop when the first node in list sources shares one coordinate
  ;; with the destination.
  ;; The first test gets rid of bad inputs.
  ;; To prove that this function terminates, the nodes in
  ;; sources must be such that nodes with a higher position in
  ;; sources are closer to the destination d.
  (if (or (endp sources) (not (CloserListp sources d))
          (not (2d-mesh-nodesetp sources))
          (not (coordinatep d)))
      nil
    (let* ((prefix (car prefixes))
           (s (car sources))
           (s_x (car s))
           (s_y (cadr s))
           (d_x (car d))
           (d_y (cadr d)))
      (cond ((or (equal s_x d_x) (equal s_y d_y))
             ;; if one of the coordinate has been reached,
             ;; we stop
              nil)
            (t
             (let ((routes
                    (cond (flg ;; last was yx-routing, next is xy-routing
                           (let ((suffix (xy-routing s d)))
                             ;; the new route is made of the prefix and
                             ;; the new suffix of the route.
                             (cons
                              (append prefix suffix)
                              (dy1
                               (getSources suffix d)
                               d nil ;; next is YX
                               (append-l-all
                                prefix
                                (extract-prefixes suffix d))))))
                          (t ;; last was xy-routing, next is yx
                           (let ((suffix (yx-routing s d)))
                             (cons (append prefix suffix)
                                   (dy1
                                    (getSources suffix d)
                                    d t ;;next is XY
                                    (append-l-all
                                     prefix
                                     (extract-prefixes suffix d)))))))))
               (append routes
                       (dy1 (cdr sources)
                                          d flg prefixes))))))))



(defun dy (s d)
  ;; if s and d share a coordinate, we have a "border" case. No minimal adaptive path
  ;; is available, thus we have apply either xy or yx. But, in that case, they both
  ;; return the same path.

  ;; Note: it is not possible to add this special case in the previous function, because
  ;; this would add routes in the computation.

  (if (and (coordinatep s) (coordinatep d)
	   (or (equal (car s) (car d))
	       (equal (cadr s) (cadr d))))
	   (list (xy-routing s d))

      ;; when calling the "full" algorithm, we know that adapative behaviors are possible
      ;; note: this is required as an invariant in the proof

      (append (dy1 (list s) d t nil) ;; flag is true,we start with xy
	      (dy1 (list s) d nil nil)))) ;; flag is false, we start with yx


;; we define the last functions to match the signature of the generic routing function

(defun DoubleYRouting1 (Missives)
  (if (endp Missives)
      nil
    (let* ((miss (car Missives))
           (org (OrgM miss))
           (dest (DestM miss))
           (Id (IdM miss))
           (frm (FrmM miss)))
      (cons (list id frm (dy org dest))
            (DoubleYRouting1 (cdr Missives))))))

(defun DoubleYRouting (Missives NodeSet)
  (declare (ignore NodeSet))
  (DoubleYRouting1 Missives))

;; this concludes the definition of the doube Y algorithm
;; ---------------------------------------------------------------------------------------------


;;-------------------------------------------------------------
;;
;;      III. Validation of the Double-Y routing algorithm
;;
;;-------------------------------------------------------------

;; now, we want to prove that this algorithms is a valid instance of the
;; generic routing function.

;; The function here at the same level as xy-routing is dy.
;; The function at the same leval as xy-routing-top is doubleyRouting1.

;; the final theorem we want to prove is:
;(defthm compliance-dbleYrouting
;  t
;  :rule-classes nil
;  :otf-flg t
;  :hints (("GOAL"
;           :do-not-induct t
;           :use (:functional-instance
;                 ToMissives-Routing
;                 (NodeSetGenerator mesh-nodeset-gen)
;                 (NodeSetp 2D-mesh-nodesetp)
;                 (ValidParamsp mesh-hyps)
;                 (Routing DoubleYRouting))
;           :in-theory (disable ToMissives-Routing
;                               mesh-nodeset-gen
;                               trlstp mesh-hyps
;                               Missivesp))))
;; we can submit this theorem to see which properties have to be proven.
;; the two remaining goals are correctroutesp (routes are correct) and trlstp (travels are
;; well-formed)

;; III.1. Proving Correctroutesp of DoubleYRouting1
;; ------------------------------------------------

;; the constraint we need to relieve is the following:
;(IMPLIES (AND (MISSIVESP M (MESH-NODESET-GEN PARAMS))
;              (MESH-HYPS PARAMS))
;         (CORRECTROUTESP (DOUBLEYROUTING1 M)
;                         M (MESH-NODESET-GEN PARAMS)))



;; the strategy is to prove validroutes and subsetp


(defun all-validroutep (routes s d)
  ;; this predicate recognizes a list of routes where every route r starts in s and ends with d
  (if (endp routes) t
    (let ((r (car routes)))
      (and (equal (car r) s)
	   (equal (car (last r)) d)
	   (not (equal (car r) (car (last r))))
	   (all-validroutep (cdr routes) s d)))))

(defun all-subsetp (routes nodeset)
  ;; checks that all elements of routes is a subset of nodeset
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (subsetp r nodeset)
	   (all-subsetp (cdr routes) nodeset)))))

(defthm tactic-is-good
  (implies (and (all-subsetp routes nodeset)
		(all-validroutep routes (orgm msv) (destm msv)))
	   (checkroutes routes msv nodeset)))


;; III.1.a/ all-validroutep
;; --------------------

;; we want to prove that dy1 satisfies this property

(defthm all-validroutep-append
  ;; removing append's by conjunctions
  (equal (all-validroutep (append l1 l2) s d)
	 (and (all-validroutep l1 s d)
	      (all-validroutep l2 s d))))

(defun all-2d-mesh-nodesetp (lst)
  ;; checks that all lists in lst are lists of valid nodes
  (if (endp lst)
      t
    (let ((r (car lst)))
      (and (and (consp r) (2d-mesh-nodesetp r))
	   ;; we check that if lst is not empty, then
	   ;; its elements are not empty either
	   (all-2d-mesh-nodesetp (cdr lst))))))

(defthm all-2d-mesh-nodesetp-extract-prefixes
  (implies (2d-mesh-nodesetp lst)
	   (all-2d-mesh-nodesetp (extract-prefixes lst d))))

(defthm all-2d-mesh-nodesetp-append-l-all
  (implies (and (2d-mesh-nodesetp l)
		(all-2d-mesh-nodesetp LST))
	   (all-2d-mesh-nodesetp (append-l-all l LST))))

(defthm all-2d-mesh-append-l-all-xy-routing
  ;; this lemma might not be useful to prove validroutep-apply-DoubleY-all-nodeset
  ;; also s is free ... s is now (car sources) ...
  (implies (all-2d-mesh-nodesetp prefixes)
	   (all-2d-mesh-nodesetp (append-l-all (car prefixes)
					       (extract-prefixes
						(xy-routing (car sources) d) d)))))

(defthm all-2d-mesh-append-l-all-yx-routing2
  (implies (all-2d-mesh-nodesetp prefixes)
	   (all-2d-mesh-nodesetp (append-l-all (car prefixes)
					       (extract-prefixes
						(yx-routing (car sources) d) d)))))


(defthm car-last-append
  (implies (consp l2)
	   (equal (car (last (append l1 l2)))
		  (car (last l2)))))

(defthm not-member-equal-getSources
  (not (member-equal d (getSources1 L d))))

(defthm not-member-equal-with-car
  (implies (and (not (member-equal d sources)) (consp sources))
	   (not (equal (car sources) d)))
  :rule-classes :forward-chaining)

(defthm 2d-mesh-coordinatep-forward
  (implies (and (2d-mesh-nodesetp lst) (consp lst))
	   (coordinatep (car lst)))
  :rule-classes :forward-chaining)

(defthm 2d-mesh-nodesetp-cdr
  (implies (2d-mesh-nodesetp lst)
	   (2d-mesh-nodesetp (cdr lst)))
  :rule-classes :forward-chaining)

(defthm 2d-mesh-nodesetp-getSources1
  (implies (and (2d-mesh-nodesetp r) (coordinatep d))
	   (2d-mesh-nodesetp (getSources1 r d))))

(defthm 2D-nodesetp-cdr-yx-routing
  (2d-mesh-nodesetp (getSources1 (cdr (yx-routing from to)) to)))

(defthm true-list-getSources1
  (true-listp (getSources1 lst d))
  :rule-classes :type-prescription)

(defun no-common-coordinate (lst d)
  ;; check that nodes of lst do not share a coordinate with d
  ;; this holds in case of "adaptiveness"
  (if (endp lst)
      t
    (let ((n (car lst)))
      (and (not (equal (car n) (car d)))
	   (not (equal (cadr n) (cadr d)))
	   (no-common-coordinate (cdr lst) d)))))

(defthm no-common-coordinate-cdr-fwd
  (implies (no-common-coordinate lst d)
	   (no-common-coordinate (cdr lst) d))
  :rule-classes :forward-chaining)

(defthm all-2d-mesh-cdr
  (implies (all-2d-mesh-nodesetp lst)
	   (all-2d-mesh-nodesetp (cdr lst)))
  :rule-classes :forward-chaining)

(defthm no-common-coordinate-getSources1
  (no-common-coordinate (getSources1 lst d) d))

(defthm no-common-not-equal
  (implies (and (no-common-coordinate sources d)
		(2d-mesh-nodesetp sources)
		(consp sources))
	   (not (equal (car sources) d)))
  :rule-classes :forward-chaining)

(defthm last-cdr-xy-routing
  (implies (and (coordinatep from) (coordinatep to)
		(not (equal from to)))
	   (equal (car (last (cdr (xy-routing from to)))) to)))

(defun inv-sources (sources s)
  (if (endp sources)
      t
    (and (equal (car sources) s)
	 (inv-sources (cdr sources) s))))

(defun inv-prefixes (prefixes s)
  (if (endp prefixes)
      t
    (and (equal (caar prefixes) s)
	 (inv-prefixes (cdr prefixes) s))))

(defun inv (prefixes sources s)
  (if (endp prefixes)
      (inv-sources sources s)
    (inv-prefixes prefixes s)))

(defthm inv-cdr
  (implies (inv prefixes sources s)
	   (inv prefixes (cdr sources) s))
  :rule-classes :forward-chaining)

(defthm car-xy-routing-append-prefixes
  (implies (and (inv prefixes sources s)
		(consp sources)
		(2d-mesh-nodesetp sources)
		(all-2d-mesh-nodesetp prefixes)
		(coordinatep d)
		)
	   (equal (car (append (car prefixes)
			       (xy-routing (car sources) d)))
		  s)))

(defthm car-yx-routing-append-prefixes
  (implies (and (inv prefixes sources s) (consp sources)
		(2d-mesh-nodesetp sources)
		(all-2d-mesh-nodesetp prefixes)
		(coordinatep d))
	   (equal (car (append (car prefixes)
			       (yx-routing (car sources) d)))
		  s)))


(defthm consp-car-all-2d-mesh
  (implies (and (consp lst) (all-2d-mesh-nodesetp lst))
	   (consp (car lst)))
  :rule-classes :forward-chaining)


(defthm append-l-all-nil
  (implies (true-listp lst)
	   (equal (append-l-all nil lst)
		  lst)))

(defthm inv-append-e-all-s
  (implies (consp lst)
	   (inv (append-e-all s lst) sources s)))

(defthm inv-prefixes-append-e-all
  (implies (consp lst)
	   (inv-prefixes (append-e-all s lst) s)))

(defthm inv-prefixes-append-l-all
  (implies (and (consp lst) (inv-prefixes prefixes s) (consp prefixes)
		(all-2d-mesh-nodesetp prefixes))
	   (inv-prefixes (append-l-all (car prefixes) lst) s)))

(defthm consp-append-e-all
  (implies (consp lst)
	   (consp (append-e-all e lst))))


;; we first link car and append
(defthm car-append
  (implies (consp a)
           (equal (car (append a b))
                  (car a))))

(defthm inv-append-l-all-xy-routing
  (implies (and (inv prefixes sources s)
		(no-common-coordinate sources d)
		(coordinatep s) (coordinatep d) (consp sources)
		(all-2d-mesh-nodesetp prefixes)
		(2d-mesh-nodesetp sources))
	   (INV (APPEND-L-ALL (CAR PREFIXES)
			      (EXTRACT-PREFIXES (XY-ROUTING (CAR SOURCES) D)
						D))
		(GETSOURCES1 (CDR (XY-ROUTING (CAR SOURCES) D))
				D)
		S))
  :otf-flg t
  :hints (("GOAL"
	   :cases ((consp prefixes))
	   :do-not-induct t
	   :do-not '(eliminate-destructors generalize))
	  ("Subgoal 2.2.1"
	   :cases ((consp (extract-prefixes (cdr (xy-routing s d)) d))))
	  ("Subgoal 1.2.1"
	   :cases ((consp (extract-prefixes (cdr (xy-routing (car sources) d)) d))))))


(defthm inv-append-l-all-comprefix-getcand-yx-routing
  (implies (and (inv prefixes sources s)
		(no-common-coordinate sources d)
		(coordinatep s) (coordinatep d) (consp sources)
		(all-2d-mesh-nodesetp prefixes)
		(2d-mesh-nodesetp sources))
	   (INV (APPEND-L-ALL (CAR PREFIXES)
                              (EXTRACT-PREFIXES (YX-ROUTING (CAR SOURCES) D)
                                                D))
                (GETSOURCES1 (CDR (YX-ROUTING (CAR SOURCES) D))
                                D)
                S))
  :otf-flg t
  :hints (("GOAL"
	   :cases ((consp prefixes))
	   :do-not '(eliminate-destructors generalize)
	   :do-not-induct t)
	  ("Subgoal 2.2.1"
	   :cases ((consp (extract-prefixes (cdr (yx-routing s d)) d))))
	  ("Subgoal 1.2.1"
	   :cases ((consp (extract-prefixes (cdr (yx-routing (car sources) d)) d))))))


(defthm validroutep-apply-DoubleY-all-nodeset
  (implies (and (all-2d-mesh-nodesetp prefixes) ;; this true even if prefixes is empty
		(coordinatep d) (coordinatep s)
		(not (equal s d))
		(no-common-coordinate sources d)
		(consp sources)
		(2d-mesh-nodesetp sources)
		(inv prefixes sources s)
		)
	   (all-validroutep (dy1 sources d flg prefixes)
			    s d))
  :hints (("GOAL"
	   :in-theory (e/d ()
			   (all-2d-mesh-nodesetp member-equal 2d-mesh-nodesetp coordinatep
			    no-common-coordinate xy-routing yx-routing extract-prefixes
			    getSources1 append-e-all append-l-all closerlistp inv))
	   :do-not '(eliminate-destructors generalize))))


;; III.1.b/ all-subsetp
;; --------------------

;; we now prove that the routes produced by the double Y routing algorithm use only existing
;; nodes

;; we need to prove that the routes computed by apply-doubleY-all are
;; subsets of NodeSet = coord-gen(X,Y), i.e. the following theorem:
;;(defthm subsetp-apply-DoubleY-all-nodeset
;;  (implies (and (2d-mesh-nodesetp sources) (coordinatep d)
;;                (member-equal d (coord-gen X Y))
;;                (not (member-equal d sources))
;;                (natp X) (natp Y)
;;                (subsetp sources (coord-gen X Y))
;;                (all-subsetp prefixes (coord-gen X Y)))
;;           (all-subsetp (dy1 sources d flg prefixes)
;;                        (coord-gen X Y)))
;;

(defthm subsetp-cdr-fwd
  (implies (subsetp l lst)
	   (subsetp (cdr l) lst))
  :rule-classes :forward-chaining)

(defthm all-subsetp-append
  (equal (all-subsetp (append l1 l2) S)
	 (and (all-subsetp l1 S)
	      (all-subsetp l2 S))))

(defthm subsetp-append-better
  (equal (subsetp (append l1 l2) S)
	 (and (subsetp l1 S)
	      (subsetp l2 S))))

(defthm subsetp-member-equal
  (implies (and (subsetp sources S)
		(consp sources))
	   (member-equal (car sources) S))
  :rule-classes :forward-chaining)

(defthm subsetp-append-l-all
  (equal (all-subsetp (append-l-all l l1) s)
	 (if (consp l1)
	     (and (subsetp l s) (all-subsetp l1 s))
	   t)))

(defthm all-subsetp-subsetp-extract-prefixes
  (implies (subsetp l s)
           (all-subsetp (extract-prefixes l d) s)))


(defthm subsetp-trans
  (implies (and (subsetp s1 s2)
                (subsetp s2 s3))
           (subsetp s1 s3)))

(defthm subsetp-getSources
  (subsetp (getSources1 lst d) lst))


(defthm subsetp-cdr-rev
  (implies (subsetp l s)
           (subsetp (cdr l) s)))

(defthm subsetp-getSources1-xy-routing
  (implies (and (not (equal s d))
                (coordinatep s) (coordinatep d)
                (natp X) (natp Y)
                (member-equal s (coord-gen X Y))
                (member-equal d (coord-gen X Y)))
           (subsetp (getSources1 (cdr (xy-routing s d)) d)
                    (coord-gen x y)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use (:instance subsetp-trans
                           (s1 (getSources1 (cdr (xy-routing s d)) d))
                           (s2 (cdr (xy-routing s d)))
                           (s3 (coord-gen x y)))
           :in-theory (disable coordinatep natp subsetp-trans)
           :do-not '(eliminate-destructors generalize fertilize))))


(defthm subsetp-getSources1-yx-routing
  (implies (and (not (equal s d))
                (coordinatep s) (coordinatep d)
                (natp X) (natp Y)
                (member-equal s (coord-gen X Y))
                (member-equal d (coord-gen X Y)))
           (subsetp (getSources1 (cdr (yx-routing s d)) d)
                    (coord-gen x y)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use (:instance subsetp-trans
                           (s1 (getSources1 (cdr (yx-routing s d)) d))
                           (s2 (cdr (yx-routing s d)))
                           (s3 (coord-gen x y)))
           :in-theory (disable coordinatep natp subsetp-trans)
           :do-not '(eliminate-destructors generalize fertilize))))

(defthm subsetp-apply-DoubleY-all-nodeset
  (implies (and (all-2d-mesh-nodesetp prefixes)
		(coordinatep d) (member-equal d (coord-gen X Y))
		(consp sources)
		(2d-mesh-nodesetp sources)
		(no-common-coordinate sources d)
		(natp X) (natp Y)
		(subsetp sources (coord-gen X Y))
		(all-subsetp prefixes (coord-gen X Y)))
	   (all-subsetp (dy1 sources d flg prefixes)
			(coord-gen X Y)))
  :hints (("GOAL"
	   :in-theory (e/d ()
			   (all-2d-mesh-nodesetp member-equal 2d-mesh-nodesetp coordinatep
			    no-common-coordinate xy-routing yx-routing extract-prefixes
			    getSources1 append-e-all append-l-all closerlistp subsetp))
	   :do-not '(eliminate-destructors generalize))))



;; III.1 c/ checkroutes of dy1
;; -------------------------------------------

;; now we put all-validroutep and all-subsetp together to prove checkroutes

(defthm checkroutes-apply-doubleY
  (implies (and (all-2d-mesh-nodesetp prefixes)
		(coordinatep (destm msv)) (member-equal (destm msv) (coord-gen X Y))
		(consp sources)
		(2d-mesh-nodesetp sources)
		(no-common-coordinate sources (destm msv))
		(natp X) (natp Y)
		(subsetp sources (coord-gen X Y))
		(all-subsetp prefixes (coord-gen X Y))
		(not (equal (orgm msv) (destm msv)))
		(coordinatep (orgm msv))
		(inv prefixes sources (orgm msv)))
	   (checkroutes (dy1 sources (destm msv) flg prefixes)
			msv
			(coord-gen X Y)))
  :otf-flg t
  :hints (("GOAL"
	   :use (:instance tactic-is-good
			   (routes (dy1 sources (destm msv) flg prefixes))
			   (nodeset (coord-gen X Y)))
	   :do-not '(eliminate-destructors generalize)
	   :in-theory (e/d () (coordinatep natp dy1 inv checkroutes
			       tactic-is-good))
	   :do-not-induct t)))



;; III.1 d/ correctroutesp of dy1
;; ---------------------------------------------

;; we can now conclude III.1

(defthm checkroutes-append
  (equal (checkroutes (append l1 l2) nodes S)
	 (and (checkroutes l1 nodes s)
	      (checkroutes l2 nodes s))))

(defthm nth3-cdddr
  (implies (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x)))
	   (equal (nth 3 x)
		  (car (cdddr x)))))

(defthm CorrectRoutesp-DoubleYRouting1
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (mesh-hyps Params)
                  (Missivesp Missives NodeSet))
           (CorrectRoutesp (DoubleYRouting1 Missives)
                           Missives NodeSet)))
  :otf-flg t
  :hints (("GOAL"
	   :do-not '(eliminate-destructors generalize)
	   :in-theory (e/d () (all-2d-mesh-nodesetp coordinatep coord-gen
			       all-subsetp))
           :induct (DoubleYRouting1 Missives)
           :do-not-induct t)
	  ("Subgoal *1/2.3.2"
	   :use (:instance checkroutes-apply-doubleY
			   (sources (list (cadar missives)))
			   (msv (car missives)) (flg T) (prefixes nil)
			   (x (car params)) (y (cadr params)))
	   :in-theory (e/d (coordinatep) (checkroutes-apply-doubleY)))
	  ("Subgoal *1/2.3.1"
	   :use (:instance checkroutes-apply-doubleY
			   (sources (list (cadar missives)))
			   (msv (car missives)) (flg nil) (prefixes nil)
			   (x (car params)) (y (cadr params)))
	   :in-theory (e/d (coordinatep) (checkroutes-apply-doubleY)))))


;; III.2. Proving TrLstp of DoubleYRouting1
;; ------------------------------------------------

(defthm V-ids-dy-=-M-ids
  (equal (V-ids (DoubleYRouting1 Missives))
         (M-ids Missives)))

(defthm consp-dy1
  (implies (and (consp sources)
		(closerlistp sources d)
		(no-common-coordinate sources d)
		(2d-mesh-nodesetp sources)
		(coordinatep d))
	   (consp (dy1 sources d flg prefixes)))
  :hints (("GOAL"
	   :in-theory (e/d ()
			   (all-2d-mesh-nodesetp member-equal 2d-mesh-nodesetp coordinatep
			    xy-routing yx-routing extract-prefixes
			    getSources1 append-e-all append-l-all closerlistp subsetp))
	   :do-not '(eliminate-destructors generalize))))

(defthm validfield-route-append
  (equal (validfield-route (append l1 l2))
	 (and (validfield-route l1)
	      (validfield-route l2))))


(defthm consp-cdr-append
  (implies (consp (cdr x))
	   (consp (cdr (append y x)))))

(defthm validfield-route-apply-doubleY-all
  (implies (and (consp sources)
		(closerlistp sources d)
		(no-common-coordinate sources d)
		(2d-mesh-nodesetp sources)
		(coordinatep d))
	   (validfield-route (dy1 sources d flg prefixes)))
  :otf-flg t
  :hints (("GOAL"
	   :do-not '(eliminate-destructors generalize)
	   :in-theory (e/d () (2d-mesh-nodesetp coordinatep xy-routing yx-routing
			       coordinatep extract-prefixes getSources1 closerlistp
			       no-common-coordinate))))
  )

(defthm TrLstp-DoubleYRouting1
  (let ((NodeSet (mesh-nodeset-gen Params)))
    (implies (and (Missivesp Missives NodeSet)
                  (mesh-hyps Params))
             (TrLstp (DoubleYRouting1 Missives))))
  :otf-flg t
  :hints (("GOAL"
	   :do-not-induct t
	   :do-not '(eliminate-destructors generalize)
           :induct (doubleYRouting1 missives))
	  ("Subgoal *1/2"
           :use ((:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (OrgM (car Missives))))
                 (:instance 2D-mesh-nodesetp-member-equal
                            (x (mesh-nodeset-gen Params))
                            (e (DestM (car Missives)))))
           :in-theory (disable 2D-mesh-nodesetp-member-equal
                               coordinatep))))



;; III.3. Checking Compliance with GeNoC
;; -------------------------------------


(defthm check-compliance-DoubleYRouting
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
                 (Routing DoubleYRouting))
           :in-theory (disable ToMissives-Routing
                               mesh-nodeset-gen
                               trlstp mesh-hyps
                               Missivesp))
          ("Subgoal 4" ; changed after v4-3 from "Subgoal 5", for tau system
           :in-theory (enable mesh-hyps))))

;; Q.E.D. !