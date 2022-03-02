;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "invariants")

(defun alt-js-p (j ens)
  (let ((j (uav-id-fix j)))
  (implies
   (< 0 j)
   (or
    (and
     ;; |--------|--------|
     ;;             <<
     ;;              J
     (<= (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav j ens)))
     (< (UAV->direction (ith-uav j ens)) 0)
     (equal (UAV->location (ith-uav j ens))
            (UAV->location (ith-uav (+ -1 j) ens))))
    (and
     ;; |--------|--------|
     ;;       >   ^   <
     ;;               J
     ;; |--------|--------|
     ;;       <   ^   >
     ;;               J
     (<= (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav j ens)))
     (not (equal (UAV->direction (ith-uav j ens))
                 (UAV->direction (ith-uav (+ -1 j) ens))))
     (<= (UAV-left-boundary (ith-uav j ens))
         (average (UAV->location (ith-uav (+ -1 j) ens))
                  (UAV->location (ith-uav j ens)))))
    (and
     ;; |--------|--------|
     ;;       >     >
     ;;             J
     (<= (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav j ens)))
     (< 0 (UAV->direction (ith-uav j ens)))
     (< 0 (UAV->direction (ith-uav (+ -1 j) ens))))))))

(defthmd alt-js-p-property
  (implies
   (wf-ensemble ens)
   (iff (alt-js-p j ens)
        (js-p j ens))))

(defun not-JS-p (j ens)
  (and
   (<= 1 (UAV-ID-FIX J))   
   (or
    ;; |--------|--------|
    ;;   >   >
    ;;       J
    ;;       >>>0
    ;;
    ;; |--------|--------|
    ;;   <   >
    ;;       J
    ;;
    ;; x<<
    ;;       >>>0
    ;; |--------|--------|
    ;;   >   <
    ;;       J
    ;;
    ;; |--------|--------|
    ;;   <   <
    ;;       J
    ;; x<< <<<
    ;; >>> 
    (< (UAV->LOCATION (ITH-UAV J ENS))
       (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
    (and
     (EQUAL (UAV->DIRECTION (ITH-UAV J ENS)) -1)
     (NOT (EQUAL (UAV->LOCATION (ITH-UAV J ENS))
                 (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))))
     (or
      ;; |--------|--------|
      ;;    >   ^   <
      ;;            J
      ;;
      ;; |--------|--------|
      ;;    <   ^   <
      ;;            J
      (< (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                  (UAV->LOCATION (ITH-UAV J ENS)))
         (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
      ;;
      ;; |--------|--------|--------|
      ;;     <         ^         <
      ;;                         J
      ;;
      (EQUAL (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
             -1)
      ))
    (and
      ;;
      ;; |--------|-------
      ;;    <   ^   >
      ;;            J
     (EQUAL (UAV->DIRECTION (ITH-UAV J ENS))
            1)
     (EQUAL (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
            -1)
     (< (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                 (UAV->LOCATION (ITH-UAV J ENS)))
        (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
     )
    )
   ))

;; This is how we can explore a negated predicate in
;; disjunctive normal form.  ie: Each set of hyps is
;; a conjunction.
#+joe
(defstub pred (i ens) nil)

#+joe
(with-arithmetic
 (in-average-theory)
 (defthmd not-js-p-property
   (implies
    (and
     (wf-ensemble ens)
     (have-met-left-p (+ -1 (uav-id-fix i)) ens)
     (left-synchronized-p (+ -1 (uav-id-fix i)) ens)
     (not (left-synchronized-p i ens)))
    (pred i ens))
   :otf-flg t
   :hints (("Goal" :do-not-induct t
            :do-not '(fertilize)))))

 
(def::un not-LEFT-SYNCHRONIZED-p (j ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (and
   (<= 1 (UAV-ID-FIX J))
   (or
    ;;
    ;; |--------|--------| ;; J won't turn around until it reaches its right boarder.
    ;;     >  ^  >
    ;;           J
    ;;
    ;; |--------|--------| ;; After J's event, it will continue until it reaches its right boarder.
    ;;     >  ^  <
    ;;           J
    ;;
    ;; |--------|--------| ;; J won't turn around until it reaches its right boarder.
    ;; <      ^      >
    ;;               J
    ;;
    ;; |--------|--------| ;; After J's event, it will continue until it reaches its right boarder.
    ;; <      ^      <
    ;;               J
    (and (< (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                     (UAV->LOCATION (ITH-UAV J ENS)))
            (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
         (or
          (< 0 (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
          (equal (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                 (uav-left-boundary (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))))
    ;;
    ;; |--------|--------|--------|
    ;; <          ^          <
    ;;                       J
    (and
     (<= (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
         (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                  (UAV->LOCATION (ITH-UAV J ENS))))
     (equal (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
            (uav-left-boundary (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
     (< (UAV->DIRECTION (ITH-UAV J ENS)) 0)
     (< (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)) 0)
     ))))


;;
;; not-LEFT-SYNCHRONIZED-p is the negation of LEFT-SYNCHRONIZED-p under
;; the assumptions of have-met-left-p and left-synchronized-p
;;
(defthmd not-LEFT-SYNCHRONIZED-p-property
  (implies
   (and
    (wf-ensemble ens)
    (implies
     (< 0 (uav-id-fix j))
     (and
      (have-met-left-p (+ -1 (uav-id-fix j)) ens)
      (left-synchronized-p (+ -1 (uav-id-fix j)) ens))))
   (iff (LEFT-SYNCHRONIZED-p j ens)
        (not (not-LEFT-SYNCHRONIZED-p j ens))))
  :hints ((average-hint)))

(defun alt-left-synchronized-p (j ens)
  (or
   (UAV-ID-EQUIV J 0)
   (and
    (<= 1 (UAV-ID-FIX J))
    (or
     (AND
      (<= (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
          (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                   (UAV->LOCATION (ITH-UAV J ENS))))
      (or
       ;; |-------|-------|
       ;;       x  ^  >
       (EQUAL (UAV->DIRECTION (ITH-UAV J ENS))
              1)
       ;; |-------|-------|
       ;;       >  ^  x
       (EQUAL (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
              1)))
     ;; |-------|-------|
     ;;            x<
     (AND (<= (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
              (UAV->LOCATION (ITH-UAV J ENS)))
          (EQUAL (UAV->LOCATION (ITH-UAV J ENS))
                 (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
          )))))

(defthmd alt-left-synchronized-p-property
  (implies
   (wf-ensemble ens)
   (iff (alt-left-synchronized-p j ens)
        (left-synchronized-p j ens))))



