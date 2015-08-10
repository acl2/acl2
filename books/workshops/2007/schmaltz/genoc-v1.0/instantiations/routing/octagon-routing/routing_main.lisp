;; File: routing_main.lisp
;; Proof of the main theorem of Route
;; August 15th 2005
;; proof of compliance with GeNoC
(in-package "ACL2")

;; we import the definition of route and lemmas that prove its
;; correctness
(include-book "routing_local_lemmas")

;; 1. Correction of function Route
;; ------------------------------

;; we group the main properties of Route in one theorem

(local
 (defthm consp_len_>_0
   (implies (consp x)
            (< 0 (len x)))))

(defthm CORRECTNESS_OF_ROUTE
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (not (equal from to))
                (< 0 n)     (integerp n))
           (and ;; Route contains at least two nodes
                 (<= 2 (len (route from to n)))
                 ;; it is a consp
                 (consp (route from to n))
                 ;; every node is an integer
                 (OctagonNodeSetp (route from to n))
                 ;; every node is less than the maximum of nodes
                 (all_inf_np (route from to n) (* 4 n))
                 ;; the first node is the starting node
                 (equal (car (route from to n)) from)
                 ;; the last node is the final node
                 (equal (car (last (route from to n))) to))))


;; we load the book about the generic routing
;; it also imports the types and misc. of GeNoC
(include-book "../../../generic-modules/GeNoC-routing")

;; 2. Definition of OctagonRouting
;; -------------------------------
(defun octagon-routing (Missives Bound)
  (if (endp Missives)
      nil
    (let* ((miss (car Missives))
           (Id (IdM miss))
           (frm (FrmM miss))
           (origin (OrgM miss))
           (destination (DestM miss)))
      (cons (list Id frm (list
                          (route origin destination
                                 (/ Bound 4))))
            (octagon-routing (cdr Missives) Bound)))))

;; 3. Matching the hyps
;; --------------------
;; in order to use the theorem CORRECTNESS_OF_ROUTE
;; we need to go from GeNoC hyps to the Octagon hyps
(defthm member-of-naturals-hyp
  (implies (and (member-equal e (naturals N))
                (natp N))
           (and (natp e) (< e (+ 1 N)))))


(defthm len-naturalsp
  (implies (natp N)
           (equal (len (naturals N)) (+ 1 N))))


(defthm V-ids-M-ids-octagon-routing
  ;; this is the same lemma as for the witness
  (equal (V-ids (octagon-routing Missives NodeSet))
         (M-ids Missives)))


(defthm len->=-2-=>-consp-cdr
  (implies (<= 2 (len x))
           (consp (cdr x))))

;; the next theorem does not go through ... but should !!
;; check what's wrong ...

(defthm trlstp-octagon-routing
  ;; octagon-routing returns a TrLstp
  ;; the hints are very ugly.
  ;; They are all the same, but the proof does not go through
  ;; if I put the :use at the goal Subgoal *1/2.
  (let ((NodeSet (OctagonNodeSetGenerator Bound)))
    (implies (and (Missivesp M NodeSet)
;                  (equal NodeSet (Octagonnodesetgenerator Bound))
                  (OctagonValidParamsp Bound))
             (TrLstp (octagon-routing M (* 4 bound)))))
  :otf-flg t
  :hints (("GOAL"
           :induct (octagon-routing M (len (OctagonNodeSetGenerator Bound)))
           :do-not-induct t
           :in-theory (disable len))
          ("Subgoal *1/2.2"
           :use ((:instance member-of-naturals-hyp
                            (e (cadar M))
                            (N (+ -1 (* 4 Bound))))
                 (:instance member-of-naturals-hyp
                            (e (cadddr (car M)))
                            (N (+ -1 (* 4 Bound)))))
           :in-theory (disable member-of-naturals-hyp))
          ("Subgoal *1/2.1"
           :use ((:instance member-of-naturals-hyp
                            (e (cadar M))
                            (N (+ -1 (* 4 Bound))))
                 (:instance member-of-naturals-hyp
                            (e (cadddr (car M)))
                            (N (+ -1 (* 4 Bound)))))
           :in-theory (disable member-of-naturals-hyp))))


(defthm naturals_member
  (implies (and (<= a b) (natp a) (natp b))
           (member-equal a (naturals b))))

(defthm naturals_subset_all_inf
  (implies (and (all_inf_np L n1)
                (natp n1) (OctagonNodeSetp L))
           (subsetp L (naturals (1- n1)))))

(defthm subsetp-route-valid-nodes
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (not (equal from to))
                (integerp n) (< 0 n))
           (let ((route (route from to n)))
             (subsetp route (naturals (1- (* 4 n)))))))

(defthm CorrectRoutesp-Octagon-Routing
  (let ((NodeSet (Naturals (+ -1 (* 4 N)))))
    (implies (and (Missivesp M NodeSet)
;                  (equal NodeSet (Naturals (+ -1 (* 4 N))))
                  (OctagonValidParamsp N))
             (CorrectRoutesp (octagon-routing M (* 4 n))
                             M NodeSet)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize fertilize)
           :induct (true-listp M)
           :do-not-induct t)
          ("Subgoal *1/1"
           :use ((:instance member-of-naturals-hyp
                            (N (+ -1 (* 4 N)))
                            (e (nth 1 (car M))))
                 (:instance member-of-naturals-hyp
                            (N (+ -1 (* 4 N)))
                            (e (nth 3 (car M)))))
           :in-theory (disable member-of-naturals-hyp))))

(defthm ToMissives-octagon-routing
  (let ((NodeSet (Naturals (+ -1 (* 4 N)))))
    (implies (and (Missivesp M NodeSet)
                  (OctagonValidParamsp N))
;                  (equal NodeSet (Naturals (+ -1 (* 4 N)))))
             (equal (ToMissives (octagon-routing M
                                                 (* 4 N)))
                    M)))
    :otf-flg t
    :hints (("GOAL"
             :do-not '(eliminate-destructors generalize fertilize)
             :induct (true-listp M)
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;              :in-theory (disable no-duplicatesp->no-duplicatesp-equal)
             :do-not-induct t)
            ("Subgoal *1/1"
             :use ((:instance member-of-naturals-hyp
                            (N (+ -1 (* 4 N)))
                            (e (nth 1 (car M))))
                 (:instance member-of-naturals-hyp
                            (N (+ -1 (* 4 N)))
                            (e (nth 3 (car M)))))
           :in-theory (disable member-of-naturals-hyp))))


(defun OctagonRouting (M NodeSet)
  ;; definition that is conform to GeNoC-routing
  (octagon-routing M (len NodeSet)))

(defthm check-octagonrouting-compliance
  t
  :rule-classes nil
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use (:instance
                 (:functional-instance
                  trlstp-routing
                  (NodeSetGenerator OctagonNodeSetGenerator)
                  (NodeSetp OctagonNodeSetp)
                  (ValidParamsp OctagonValidParamsp)
                  (routing OctagonRouting)))
           :in-theory (disable trlstp-routing
                               trlstp missivesp))))
