;; Julien Schmaltz
;; File: packet-scheduling.lisp
;; Modeling of a packet switching algorithm
;; Jan. 4th 2005
;; Updated August 17th, 2005

(in-package "ACL2")

(include-book "../../generic-modules/GeNoC-scheduling")
(include-book "intersect")

;;---------------------------------------------------------------------
;;
;;                      PACKET ALGORITHM
;;
;;---------------------------------------------------------------------

;; Our packet algorithm works as follows. For each step of the routes,
;; it extracts a set of non-overlapping travels.
;; for instance, if the routes are ( (0 4 5) (1 5 6) (2 1) (5 4))
;; the first three routes do not overlap, the last one is thrown out.
;; At each step in a route, a node must not be used by other routes.

(defun rev (x)
  ;; we need this definition again :-)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defun consume-attempts (att)
  ;; this function substracts one attempt to every node
  ;; in the current model at each call of the scheduler
  ;; (function packet-scheduling) each node consumes one attempt,
  ;; i.e. each node tries to send a message.
  (if (zp (SumOfAttempts att))
      att
    (let* ((top (car att))
           (node (car top))
           (att-i (cadr top)))
      (if (zp att-i)
          (cons top
                (consume-attempts (cdr att)))
        (cons (list node (1- att-i))
              (consume-attempts (cdr att)))))))

(defun no_intersectp_packet (route prev)
  ;; In the packet mode, prev is the list of the nodes used
  ;; for each step.
  ;; This function checks that every node of a route
  ;; is not already used at the corresponding step.
  (if (endp route)
      t
    (and (not (member (car route) (car prev)))
         (no_intersectp_packet (cdr route) (cdr prev)))))

(defun test_prev_routes (routes prev)
  ;; returns a route that does not overlap previous
  ;; travels if such a route exists in routes. returns
  ;; nil otherwise.
  (if (endp routes)
      nil
    (let ((r (car routes)))
      (if (no_intersectp_packet r prev)
          r
        (test_prev_routes (cdr routes) prev)))))

(defun update-prev (prev route)
  ;; update prev properly with route
  (if (endp route)
      prev
    (cons (cons (car route) (car prev))
          (update-prev (cdr prev) (cdr route)))))

(defun update_route (tr route)
  ;; updates the route of tr to be a list containing
  ;; only route
  (list (IdV tr) (FrmV tr) (list route)))

(defun pkt-scheduler (TrLst Scheduled Delayed prev)
  ;; core function for the packet scheduler.
  (if (endp TrLst)
      ;; we use prev to keep the ordering of the ids
      (mv (rev scheduled) (rev delayed))
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      ;; if there is a good route in routes
      ;; we update prev properly and schedule the travel
      (if r?
          (pkt-scheduler (cdr TrLst)
                         (cons (update_route tr r?) scheduled)
                         delayed (update-prev prev r?))
        ;; otherwise the travel is delayed
        (pkt-scheduler (cdr TrLst)
                       scheduled (cons tr delayed) prev)))))

(defun packet-scheduling (TrLst att)
  ;; Function that matches the generic definition
  ;; TrLst is the travel list, att is the list of attempts
  (if (zp (SumOfAttempts att))
      (mv nil  ;; nothing is scheduled if there is no attempt left
          TrLst ;; everything is delayed
          Att)
    ;; otherwise we call pkt-scheduler and consume attempts
    (mv-let (scheduled delayed)
            (pkt-scheduler TrLst nil nil nil)
            (mv Scheduled Delayed (consume-attempts att)))))


(defun pkt-sched-nt-sched (TrLst prev)
  ;; to simplify proofs we define a non-tail version of
  ;; pkt-scheduler that computes the scheduled travels
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      (if r?
          (cons (update_route tr r?)
                (pkt-sched-nt-sched (cdr TrLst)
                                    (update-prev prev r?)))
        (pkt-sched-nt-sched (cdr TrLst) prev)))))


(defthm pkt-scheduler-=-non-tail-scheduled
  ;; we prove that our non-tail definition is correct
  (equal (car (pkt-scheduler TrLst scheduled delayed prev))
         (append (rev scheduled)
                 (pkt-sched-nt-sched TrLst prev))))

(defun pkt-sched-nt-del (TrLst prev)
  ;; we proceed similarly for the delayed transfers
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      (if r?
          (pkt-sched-nt-del (cdr TrLst)
                            (update-prev prev r?))
        (cons tr
              (pkt-sched-nt-del (cdr TrLst) prev))))))

(defthm pkt-scheduler-=-non-tail-delayed
  (equal (mv-nth 1 (pkt-scheduler TrLst scheduled delayed prev))
         (append (rev delayed)
                 (pkt-sched-nt-del TrLst prev))))
;;-----------------------------------------------------------------



;;---------------------------------------------------------------------
;;
;; PROOF OF GeNoC CONSTRAINTS
;;
;;---------------------------------------------------------------------


;; 1/ consume at least one attempt to ensure termination

(defthm consume-at-least-one-attempt-packet-scheduling
  ;; the scheduling policy should consume at least one attempt
  ;; this is a sufficient condition to prove that
  ;; the full network function terminates
  (mv-let (Scheduled Delayed newatt)
          (packet-scheduling TrLst att)
          (declare (ignore Scheduled Delayed))
          (implies (not (zp (SumOfAttempts att)))
                   (< (SumOfAttempts newatt)
                      (SumOfAttempts att)))))
;;----------------------------------------------------------

;; 2/ we prove that the ids of the delayed and scheduled travels
;; are part of the initial travel list
;; -----------------------------------
(defthm subsetp-scheduled-pkt
  (implies (TrLstp TrLst)
           (subsetp (V-ids (pkt-sched-nt-sched TrLst prev))
                    (V-ids TrLst))))

(defthm subsetp-delayed-pkt
  (implies (TrLstp TrLst)
           (subsetp (V-ids (pkt-sched-nt-del TrLst prev))
                    (V-ids TrLst))))
;------------------------------------------------------------------

;; 3/ we prove that the list of scheduled travels is a
;; valid travel list
;; --------------------------------------------------


(defthm validfield-route-test_prev_routes
  (let ((r? (test_prev_routes routes prev)))
    (implies (and (validfield-route routes)
                  r?)
             (and (consp r?) (consp (cdr r?))))))


;; proof for the scheduled travels
;; -------------------------------
(local
 (defthm validfields-trlst-pkt-sched
   (implies (ValidFields-TrLst TrLst)
            (ValidFields-TrLst
             (pkt-sched-nt-sched TrLst prev)))))

(local
 (defthm not-member-V-ids-pkt-sched
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (pkt-sched-nt-sched TrLst prev)))))))

(local (defthm no-duplicatesp-pkt-sched
         (implies (no-duplicatesp-equal (V-ids TrLst))
                  (no-duplicatesp-equal
                   (V-ids (pkt-sched-nt-sched TrLst prev))))))

(defthm cons-v-ids
  (equal (consp (v-ids TrLst))
         (consp TrLst)))

(defthm TrLstp-scheduled-ct
  (implies (TrLstp TrLst)
           (TrLstp (pkt-sched-nt-sched TrLst prev))))

;; proof for the delayed travels
;; -----------------------------
(local
 (defthm validfields-trlst-pkt-del
   (implies (ValidFields-TrLst TrLst)
            (ValidFields-TrLst
             (pkt-sched-nt-del TrLst prev)))))

(local
 (defthm not-member-V-ids-pkt-del
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (pkt-sched-nt-del TrLst prev)))))))

(local (defthm no-duplicatesp-pkt-del
         (implies (no-duplicatesp-equal (V-ids TrLst))
                  (no-duplicatesp-equal
                   (V-ids (pkt-sched-nt-del TrLst prev))))))

(defthm TrLstp-delayed-pkt
  (implies (TrLstp TrLst)
           (TrLstp (pkt-sched-nt-del TrLst prev))))
;;--------------------------------------------------------------------


;; 4/ correctness of the scheduled travels
;; ------------------------------------------------------

(defthm extract-sublst-cons
  (implies (not (member-equal id Ids))
           (equal (extract-sublst (cons (list id frm routes) L)
                                  Ids)
                  (extract-sublst L Ids))))


(defthm test_prev_routes-member-equal
  (let ((r? (test_prev_routes routes prev)))
    (implies r?
             (member-equal r? routes))))

(defthm pkt-scheduled-correctness
    (let ((Scheduled (pkt-sched-nt-sched TrLst prev)))
      (implies (TrLstp TrLst)
               (s/d-travel-correctness
                scheduled
                (extract-sublst TrLst (V-ids Scheduled))))))

;; 5/ We prove that Delayed is equal to filtering TrLst
;; according to the ids of Delayed
;; ----------------------------------------------------
(defthm pkt-delayed-correctness
  (let ((delayed (pkt-sched-nt-del TrLst prev)))
    (implies (TrLstp TrLst)
             (equal delayed
                    (extract-sublst TrLst (V-ids delayed)))))
  :rule-classes nil)
; -----------------------------------------------------------

;; 6/ we prove that the ids of the delayed travels are distinct
;; from those of the scheduled travels
;; ------------------------------------------------------------

(defthm not-in-cons
  ;; same lemma as in the packet scheduling
  (implies (and (not-in x y) (not (member-equal e x)))
           (not-in x (cons e y))))

(defthm not-in-v-ids-ct
  (implies (TrLstp trlst)
           (not-in (v-ids (pkt-sched-nt-del trlst prev))
                   (v-ids (pkt-sched-nt-sched trlst prev)))))


;; Finally, we check that our circuit scheduling function
;; is a valid instance of GeNoC-scheduling
;; ------------------------------------------------------
(defthm check-compliance-packet-scheduling
  t
  :rule-classes nil
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use
           ((:functional-instance
             consume-at-least-one-attempt
             (scheduling packet-scheduling)))
           :in-theory (disable consume-at-least-one-attempt
                               missivesp))
          ("Subgoal 6"
           :use (:instance pkt-delayed-correctness
                           (prev nil)))
          ("Subgoal 3"
           :in-theory (disable packet-scheduling))))

;;---------------------------------------------------------------------
;;
;;            CORRECTNESS OF THE PACKET ALGORITHM
;;
;;---------------------------------------------------------------------
(defun create_steps (TrLst steps)
  ;; creates the lists of the nodes used at every step
  ;; by the routes in TrLst (the only route kept by the scheduler)
  ;; steps is nil at function call and contains the lists of
  ;; the step-nodes. steps = ( (r0[0] r1[0] ...) (r0[1] r1[1] ...) ...)
  (if (endp TrLst)
      steps
    (let* ((tr (car TrLst))
           (r (car (RoutesV tr))))
      (create_steps (cdr TrLst) (update-prev steps r)))))

(defun all_no_duplicates-steps (steps)
  ;; the packet policy is correct is a node is used only once
  ;; at a given step.
  (if (endp steps)
      t
    (let ((step-i (car steps)))
      (and (no-duplicatesp-equal step-i)
           (all_no_duplicates-steps (cdr steps))))))

(defthm test_prev_routes-all_no-dup
  (let ((r? (test_prev_routes r prev)))
    (implies (and r?
                  (all_no_duplicates-steps prev))
             (all_no_duplicates-steps (update-prev prev r?)))))

(defthm pkt-scheduling-correctness
  (implies (and (TrLstp TrLst)
                (all_no_duplicates-steps prev))
           (all_no_duplicates-steps
            (create_steps (pkt-sched-nt-sched TrLst prev)
                          prev)))
  :otf-flg t
  :hints (("GOAL"
           :induct (pkt-sched-nt-sched trlst prev)
           :do-not-induct t
           :do-not '(eliminate-destructors generalize))))

;;-----------------------------------------------------------------
;; end of packet scheduling
;;-----------------------------------------------------------------
