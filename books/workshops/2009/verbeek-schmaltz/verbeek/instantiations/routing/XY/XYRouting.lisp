#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
;; we import the generic definition
(include-book "../../../generic-modules/GeNoC-routing")
;; we import the book with node definition for a 2D-mesh
(include-book "../../nodeset/2DMesh-no-ports/2DMesh")


;; we load the arithmetic books
(include-book "arithmetic-3/bind-free/top" :dir :system)
(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)



;; we define a new measure in this part taking into consideration
;; the difference between the input and output port
;; the objective is to consider the intra router routing a true hop to
;; be able to
;; implement the routing as it is presented in the book
;; this way the measure decreases also in the case of the intra
;; routing on the same node.

(defun XY-measure (current to)
  (let ((x_d (car to))
        (y_d (cadr to))
        (x_o (car current))
        (y_o (cadr current)))
    (nfix (+ (abs (- x_d x_o)) (abs (- y_d y_o))))))

(defthm O-P-XY-routing-with-ports
  ;; the measure must be an ordinal
  (O-P (XY-measure from to)))

(defun move-north (current)
  (list (car current) (1- (cadr current))))
(defun move-south (current)
  (list (car current) (1+ (cadr current))))
(defun move-east (current)
  (list (1+ (car current)) (cadr current)))
(defun move-west (current)
  (list (1- (car current)) (cadr current)))

(defun XYRoutingLogic (current to)
  (let ((x_d (car to))
        (y_d (cadr to))
        (x_o (car current))
        (y_o (cadr current)))
    (if (not (equal x_d x_o))
      (if (< x_d x_o)
        (move-west current)
        (move-east current))
      (if (< y_d y_o)
        (move-north current)
        (move-south current)))))

(defun XYrouting (current to)
  (declare (xargs :measure (XY-measure current to)))
  (if (or (not (2DMesh-Nodep current)) (not (2DMesh-Nodep to)))
    nil
    (let ((x_d (car to))
          (y_d (cadr to))
          (x_o (car current))
          (y_o (cadr current)))
      (if (and (equal x_d x_o) (equal y_d y_o))
        (cons current nil)
        (cons current (XYrouting (XYRoutingLogic current to) to))))))

(defthm first-XY-routing
  ;; the first element is the origin
  (implies (and (2DMesh-Nodep current)
                (2DMesh-Nodep to))
           (equal (car (XYrouting current to))
                  current)))

(defthm last-XY-routing
  ;; the last element is the destination
  (implies (and (2DMesh-Nodep current)
                (2DMesh-Nodep to))
           (equal (car (last (XYrouting current to)))
                  to)))
(defun all-x-<-max (L x-max)
  ;; we define a function that checks that every x-coordinate is less
  ;; than x-max
  (if (endp L)
    t
    (and (< (caar L) x-max) ;; x_i < x-max
         (all-x-<-max (cdr L) x-max))))

(defun all-y-<-max (L y-max)
  ;; we define a function that checks that every y-coordinate is less
  ;; than y-max
  (if (endp L)
    t
    (and (< (cadar L) y-max) ;; y_i < y-max
         (all-y-<-max (cdr L) y-max))))

(defthm member-equal-x-dim-gen
  ;; we prove that if x is a coordinate with its first part less than x-dim
  ;; and its second part equal to y-dim then x is a member of x-dim-gen.
  (implies (and (2DMesh-Nodep x)
                (< (car x) x-dim)
                (natp x-dim)
                (natp y-dim)
                (equal (cadr x) y-dim))
           (member-equal x (x-dim-gen x-dim y-dim))))

(defthm member-coord-generator-1
  ;; we prove something similar for the function coord-generator-1
  ;; both parts of x are less than x-dim and y-dim implies that x
  ;; is a member of coord-generator-1
  (implies (and (2DMesh-Nodep x)
                (natp y-dim)
                (natp x-dim)
                (< (car x) x-dim)
                (< (cadr x) y-dim))
           (member-equal x (coord-generator-1 x-dim y-dim))))

(defthm tactic1
  ;; we prove that our tactic is valid for membership
  (implies (and (2DMesh-NodeSetp L)
                (consp L)
                (all-x-<-max L x-dim)
                (natp x-dim)
                (all-y-<-max L y-dim)
                (natp y-dim))
           (member-equal (car L) (coord-generator-1 x-dim y-dim))))

(defthm member-equal-rev
  ;; this should go elsewhere
  (implies (member-equal x S)
           (member-equal x (rev S))))

(defthm tactic1-top
  ;; we now prove that our tactic is valid
  (implies (and (2DMesh-NodeSetp L)
                (all-x-<-max L x-dim) (natp x-dim)
                (all-y-<-max L y-dim) (natp y-dim))
           (subsetp L (coord-gen x-dim y-dim)))
  :hints (("GOAL"
           :in-theory (enable coord-gen))))

;; Then the strategy is to prove that XY-routing-with-ports satisfies
;; the hypotheses of this theorem
(defthm 2D-mesh-NodeSet-XY-routing
  ;; 1st hyp is trivial
  ;; a route is a list of valid coordinates
  (2DMesh-NodeSetp (XYrouting current to)))

(defthm x-<all
  (implies (and (2DMesh-NodeSetp L)
                (all-x-<-max L (car from)))
           (all-x-<-max L (1+ (car from)))))

(defthm x-1<all
  (implies (and (2DMesh-NodeSetp L)
                (all-x-<-max L (1- (car from))))
           (all-x-<-max L (1+ (car from)))))

(defthm y-<all
  (implies (and (2DMesh-NodeSetp L)
                (all-y-<-max L (cadr from)))
           (all-y-<-max L (1+ (cadr from)))))

(defthm y-1<all
  (implies (and (2DMesh-NodeSetp L)
                (all-y-<-max L (1- (cadr from))))
           (all-y-<-max L (1+ (cadr from)))))

;; let's go to the more tricky part.
;; First, every x-coord of any nodes produced by function XY-routing-with-ports
;; is strictly less than 1 + Max(from_x, to_x)(2D-mesh-nodeset-portsp
;; (xy-routing-with-ports from to))

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

(defthm routing-all-x-less
  (all-x-<-max (XYrouting current to)
               (1+ (max (car current) (car to))))
  :hints (("Goal"
           :in-theory (disable CONSP-APPEND  REDUCE-INTEGERP-+
                               INTEGERP-MINUS-X))))



(defthm routing-all-y-less
  (all-y-<-max (XYrouting current to)
               (1+ (max (cadr current) (cadr to)))))

(defthm XY-routing-with-ports-subsetp-coord-max
  (implies (and (2DMesh-Nodep current) (2DMesh-Nodep to))
           (subsetp (XYrouting current to)
                    (coord-gen (1+ (max (car current) (car to)))
                               (1+ (max (cadr current) (cadr to))))))
  :hints (("GOAL"
           :in-theory (disable max))))

(defthm all-max-coord-gen
  (and (all-x-<-max (coord-gen X Y) X)
       (all-y-<-max (coord-gen X Y) Y))
  :hints (("GOAL"
           :in-theory (enable coord-gen))))

;; now we prove that if (x1 y1) and (x2 y2) belong to (coord-gen NX NY)
;; then Max(x1, x2) < NX and Max(y1, y2) < NY

(defthm member-equal-x-dim-gen-plus
  (implies (and (<= x1 x2)  (natp x1) (< 0 x1) (natp x2))
           ( and (member-equal (list (+ -1 x1) y)
                               (x-dim-gen x2 y)) )))
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
  (implies (and (natp x1)
                (natp x2)
                (natp y1)
                (natp y2)
                (<= x1 x2)
                (< y1 y2))
           (subsetp (x-dim-gen x1 y1)
                    (coord-generator-1 x2 y2))))

(defthm subsetp-coord-gen-1
  (implies (and (<= x1 x2)
                (<= y1 y2)
                (natp x1)
                (natp x2)
                (natp y1)
                (natp y2))
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
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

(defthm XY-routing-with-ports-subsetp-nodeset
  ;; now we want to prove that if NodeSet = coord-gen x y, then
  ;; route is a subsetp of NodeSet.
  ;; current and to must be members of NodeSet
  ;; current and to must not be equal
  (implies (and (not (equal current to))
                (2DMesh-Nodep current)
                (2DMesh-Nodep to)
                (natp X)
                (natp Y)
                ;; it should be member-equal
                (member-equal current (coord-gen X Y))
                (member-equal to (coord-gen X Y)))
           (subsetp (XYrouting current to) (coord-gen X Y)))
  :otf-flg t
  :hints (("GOAL"
           :use ((:instance all-max-member-equal
                  (L (coord-gen X Y))
                  (x current) (y to)
                  (x-max X) (y-max Y))
                 (:instance XY-routing-with-ports-subsetp-coord-max))
           :do-not '(eliminate-destructors generalize fertilize)
           :in-theory (disable coord-gen 2DMesh-Nodep natp subsetp
                               all-max-member-equal
                               XY-routing-with-ports-subsetp-coord-max)
           :do-not-induct t)
          ("Subgoal 4"
           :use (:instance subsetp-coord-plus
                 (x1 (+ 1 (car current))) (x2 x)
                 (y1 (+ 1 (cadr current))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 3"
           :use (:instance subsetp-coord-plus
                 (x1 (+ 1 (car current))) (x2 x)
                 (y1 (+ 1 (cadr to))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 2"
           :use (:instance subsetp-coord-plus
                 (x1 (+ 1 (car to))) (x2 x)
                 (y1 (+ 1 (cadr current))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))
          ("Subgoal 1"
           :use (:instance subsetp-coord-plus
                 (x1 (+ 1 (car to))) (x2 x)
                 (y1 (+ 1 (cadr to))) (y2 y))
           :in-theory (disable subsetp-coord-plus
                               coord-gen subsetp))))

(set-irrelevant-formals-ok t)
(defun XY-routing-top (Missives nodeset)
  ;;(declare (ignore nodeset))
  (if (endp Missives)
    nil
    (let* ((miss (car Missives))
           (From (OrgTM miss))
           (current (CurTM miss))
           (to (DestTM miss))
           (id (IdTM miss))
           (frm (FrmTM miss))
           (flits (FlitTM miss))
           (Time (TimeTM miss)))
      (cons (list id from frm (list (XYrouting current to)) flits time)
            (XY-routing-top (cdr Missives) nodeset)))))

(set-irrelevant-formals-ok nil)

(defun XYRouting-main (Missives NodeSet)
  ;;(declare (ignore NodeSet))
  (XY-routing-top Missives nodeset))

;; 4.b Proof of compliance
;; ------------------------

(defthm xy-routing-nil
  ;; the routing has to return nil if the list of missives is nil
  (not (xy-routing-top nil NodeSet)))

(defthm true-listp-xy-
  (true-listp (xy-routing-top missives nodeset)))

;; 2. TrLstp
;;the next four theorems are necessary lemmas to prove the theorem
;;Trlstp-XY-routing

(defthm consp-XY-routing-with
  ;; should be systematically added (35 secondeS)
  (implies (and (2DMesh-Nodep current)
                (2DMesh-Nodep to))
           (consp (XYrouting current to))))

(defthm consp-XY-routing-with-ports-cdr
  ;; should be systematically added
  (implies (and (2DMesh-Nodep current) (not (equal current to))
                (2DMesh-Nodep to))
           (consp (cdr (XYrouting current to)))))

(defthm V-ids-XY-routing-with-ports-=-M-ids
  ;; this one too ...
  (equal (V-ids (XY-routing-top Missives nodeset))
         (TM-ids Missives)))

(defthm 2D-mesh-NodeSet-portsp-member-equal
  (implies (and (2DMesh-NodeSetp x)
                (member-equal e x))
           (2DMesh-Nodep e)))

(defthm no-consecutive-equals-XY-Routing
  (implies (and (2DMesh-Nodep current)
                (2DMesh-Nodep to))
           (no-consecutive-equals (XYrouting current to))))
(defthm no-hops-equal-to-dest-XY-Routing
  (implies (and (2DMesh-Nodep current)
                (2DMesh-Nodep to))
           (no-hops-equal-to-dest (XYrouting current to) to)))

(defthm TrLstp-XYRouting
  (let ((NodeSet (2dMesh-NodesetGenerator Params)))
    (implies (and (TMissivesp TMissives NodeSet)
                  (2DMesh-Validparamsp Params))
             (TrLstp (XY-routing-top TMissives nodeset) nodeset)))
  :hints (("GOAL" :induct (XY-routing-top tmissives nodeset))
          ("Subgoal *1/2"
           :use ((:instance last-XY-routing
                  (current (CADDAR TMISSIVES))
                  (to (CADDDR (CDAR TMISSIVES))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (OrgtM (car tMissives))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (CurtM (car tMissives))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (DesttM (car tMissives)))))
           :in-theory (disable 2D-mesh-NodeSet-portsp-member-equal
                               2DMesh-Nodep last-XY-routing))))

;; 3. CorrectRoutesp
(defthm CorrectRoutesp-XYRouting
  (let ((NodeSet (2DMesh-NodeSetGenerator Params)))
    (implies (and (2dMesh-ValidParamsp Params)
                  (TMissivesp TMissives NodeSet))
             (CorrectRoutesp (XY-routing-top TMissives nodeset)
                             TMissives NodeSet)))
  :hints (("GOAL"
           :induct (XY-routing-top TMissives nodeset)
           :do-not-induct t)
          ("Subgoal *1/2"
           :use ((:instance first-XY-routing
                  (current (CADDAR TMISSIVES))
                  (to (CADDDR (CDAR TMISSIVES))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (CurTM (car TMissives))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (OrgTM (car TMissives))))
                 (:instance 2D-mesh-NodeSet-portsp-member-equal
                  (x (2DMesh-NodeSetGenerator Params))
                  (e (DestTM (car TMissives)))))
           :in-theory (disable 2D-mesh-NodeSet-portsp-member-equal
                               2DMesh-Nodep))))

(definstance GenericRouting check-comlpiance-xyrouting
  :functional-substitution
  ((NodeSetGenerator 2DMesh-NodeSetGenerator)
   (NodeSetp 2DMesh-NodeSetp)
   (ValidParamsp 2DMesh-ValidParamsp)
   (Routing XY-Routing-top))
  :rule-classes nil
  :hints (("GOAL" :in-theory (disable ToMissives-Routing
                                      2DMesh-NodeSetGenerator
                                      trlstp 2DMesh-ValidParamsp
                                      TMissivesp))
          ("Subgoal 5"
           :in-theory (enable 2DMesh-ValidParamsp)))
  :otf-flg t)
