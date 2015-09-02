;; Julien Schmaltz
;; File: circuit-scheduling.lisp
;; here we define a function that realises a circuit switching
;; technique, we prove it correct and we prove that it is a valid
;; instance of the scheduling function of GeNoC.
;; Revised: Nov 13th 2005, JS


(in-package "ACL2")
(include-book "../../generic-modules/GeNoC-scheduling")
(include-book "intersect")

;;-----------------------------------------------------
;;
;; DEFINITION OF THE CIRCUIT SWITCHED SCHEDULING POLICY
;;
;;-----------------------------------------------------

(defun rev (x)
  ;; put this definition in a book !!
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defun consume-attempts (AttLst)
  ;; any node that has a attempt, consumes one
  (if (zp (SumOfAttempts AttLst))
      AttLst
    (let* ((top (car AttLst))
           (node (car top))
           (att (cadr top)))
      (if (zp att)
          (cons top
                (consume-attempts (cdr AttLst)))
        (cons (list node (1- att))
              (consume-attempts (cdr AttLst)))))))

(defun test_prev_routes (routes prev)
  ;; function that returns a route that uses nodes
  ;; that are not in prev or returns nil if there is no
  ;; such route.
  (if (endp routes)
      nil
    (let ((r (car routes)))
      (if (no_intersectp r prev)
          r
        (test_prev_routes (cdr routes) prev)))))

(defun update_route (tr route)
  ;; updates the route of tr to be a list containing
  ;; only route
  (list (IdV tr) (FrmV tr) (list route)))

(defun ct-scheduler (TrLst Scheduled Delayed prev)
  (if (endp TrLst)
      (mv (rev scheduled) (rev delayed))
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      (if r?
          ;; if there is a good route in routes
          ;; we update prev and schedule the transaction
          (ct-scheduler (cdr TrLst)
                        (cons (update_route tr r?) Scheduled)
                        Delayed (append r? prev))
        ;; otherwise the transaction is delayed
        (ct-scheduler (cdr TrLst) scheduled
                      (cons tr Delayed) prev)))))

(defun circuit-scheduling (TrLst att)
  ;; definition compatible with GeNoC-scheduling
  (if (zp (SumOfAttempts att))
      ;; nothing is scheduled if there is no attempt left
      ;; so everything is delayed
      (mv nil TrLst att)
    ;; otherwise we call ct-scheduler and consume attempts
    (mv-let (scheduled delayed)
            (ct-scheduler TrLst nil nil nil)
            (mv Scheduled Delayed (consume-attempts att)))))

(defun ct-sched-nt-sched (TrLst prev)
  ;; to simplify proofs we define a non-tail version of
  ;; ct-scheduler that computes the scheduled transactions
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      (if r?
          (cons (update_route tr r?)
                (ct-sched-nt-sched (cdr TrLst)
                                   (append r? prev)))
        (ct-sched-nt-sched (cdr TrLst) prev)))))

(defthm scheduler-=-non-tail-scheduled
  ;; we prove that our non-tail definition is correct
  (equal (car (ct-scheduler TrLst scheduled delayed prev))
         (append (rev scheduled)
                 (ct-sched-nt-sched TrLst prev))))

(defun ct-sched-nt-del (TrLst prev)
  ;; we proceed similarly for the delayed transfers
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (routes (RoutesV tr))
           (r? (test_prev_routes routes prev)))
      (if r?
          (ct-sched-nt-del (cdr TrLst)
                           (append r? prev))
        (cons tr
              (ct-sched-nt-del (cdr TrLst) prev))))))

(defthm scheduler-=-non-tail-delayed
  (equal (mv-nth 1 (ct-scheduler TrLst scheduled delayed prev))
         (append (rev delayed)
                 (ct-sched-nt-del TrLst prev))))
;;-----------------------------------------------------------------

;;-------------------------------------------------------------------------
;;
;;                 Compliance with GeNoC SCHEDULING
;;
;;-------------------------------------------------------------------------

;; 1/ consume at least one attempt to ensure termination
;; -----------------------------------------------------
 (defthm consume-at-least-one-attempt-circuit-scheduling
   ;; the scheduling policy should consume at least one attempt
   ;; this is a sufficient condition to prove that
   ;; the full network function terminates
   (mv-let (Scheduled Delayed newAtt)
	   (circuit-scheduling TrLst att)
	   (declare (ignore Scheduled Delayed))
	   (implies (not (zp (SumOfAttempts att)))
		    (< (SumOfAttempts newAtt)
		       (SumOfAttempts att)))))
;;----------------------------------------------------------

;; 2/ we prove that the ids of the delayed and scheduled travels
;; are part of the initial travel list
;; -----------------------------------
(defthm subsetp-scheduled-ct
  (implies (TrLstp TrLst)
           (subsetp (V-ids (ct-sched-nt-sched TrLst prev))
                    (V-ids TrLst))))

(defthm subsetp-delayed-ct
  (implies (TrLstp TrLst)
           (subsetp (V-ids (ct-sched-nt-del TrLst prev))
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
 (defthm validfields-trlst-ct-sched
   (implies (ValidFields-TrLst TrLst)
            (ValidFields-TrLst
             (ct-sched-nt-sched TrLst prev)))))

(local
 (defthm not-member-V-ids-ct-sched
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (ct-sched-nt-sched TrLst prev)))))))

(local (defthm no-duplicatesp-ct-sched
         (implies (no-duplicatesp-equal (V-ids TrLst))
                  (no-duplicatesp-equal
                   (V-ids (ct-sched-nt-sched TrLst prev))))))

(defthm cons-v-ids
  (equal (consp (v-ids TrLst))
         (consp TrLst)))

(defthm TrLstp-scheduled-ct
  (implies (TrLstp TrLst)
           (TrLstp (ct-sched-nt-sched TrLst prev))))

;; proof for the delayed travels
;; -----------------------------
(local
 (defthm validfields-trlst-ct-del
   (implies (ValidFields-TrLst TrLst)
            (ValidFields-TrLst
             (ct-sched-nt-del TrLst prev)))))

(local
 (defthm not-member-V-ids-ct-del
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (ct-sched-nt-del TrLst prev)))))))

(local (defthm no-duplicatesp-ct-del
         (implies (no-duplicatesp-equal (V-ids TrLst))
                  (no-duplicatesp-equal
                   (V-ids (ct-sched-nt-del TrLst prev))))))

(defthm TrLstp-delayed-ct
  (implies (TrLstp TrLst)
           (TrLstp (ct-sched-nt-del TrLst prev))))
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

(defthm ct-scheduled-correctness
    (let ((Scheduled (ct-sched-nt-sched TrLst prev)))
      (implies (TrLstp TrLst)
               (s/d-travel-correctness
                scheduled
                (extract-sublst TrLst (V-ids Scheduled))))))

;; 5/ We prove that Delayed is equal to filtering TrLst
;; according to the ids of Delayed
;; ----------------------------------------------------
(defthm ct-delayed-correctness
  (let ((delayed (ct-sched-nt-del TrLst prev)))
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
           (not-in (v-ids (ct-sched-nt-del trlst prev))
                   (v-ids (ct-sched-nt-sched trlst prev)))))


;; Finally, we check that our circuit scheduling function
;; is a valid instance of GeNoC-scheduling
;; ------------------------------------------------------
(defthm check-compliance-circuit-scheduling
  t
  :rule-classes nil
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use
           ((:functional-instance
             consume-at-least-one-attempt
             (scheduling circuit-scheduling)))
           :in-theory (disable consume-at-least-one-attempt
                               missivesp))
          ("Subgoal 6"
           :use (:instance ct-delayed-correctness
                           (prev nil)))
          ("Subgoal 3"
           :in-theory (disable circuit-scheduling))))

;;-----------------------------------------------------------------
;;
;;            Validation of function circuit-scheduling
;;
;;-----------------------------------------------------------------

(defun all_no_intersectp (route TrLst)
  ;; return t if route has an empty intersection with every
  ;; route of TrLst.
  (if (endp TrLst)
      t
    (let* ((tr (car TrLst))
           (r (RoutesV tr)))
      (and (no_intersectp route (car r))
           (all_no_intersectp route (cdr TrLst))))))

(defun FullNoIntersectp (TrLst)
  ;; this function checks that every route in TrLst
  ;; has at least one attempt left and it has an empty
  ;; intersection with every following route.
  ;; This defines the correctness of the circuit scheduling
  ;; policy.
  ;; JS Nov 13th. Checking that every node of a route has at least
  ;; one attempt is stupid !
  (if (or (endp TrLst) (endp (cdr TrLst)))
      t
    (let* ((tr (car TrLst))
           (r (RoutesV tr)))
      (and (all_no_intersectp (car r) (cdr TrLst))
;           (check_attempt (car r) att)
           (FullNoIntersectp (cdr TrLst))))))

(defthm test_prev_routes-check-no_intersectp
  (let ((r? (test_prev_routes routes prev)))
    (implies r?
;             (and (check_attempt r? att)
             (no_intersectp prev r?))))


(defthm all_no_intersectp-append
  (implies (all_no_intersectp (append l1 l2) l)
           (and (all_no_intersectp l1 l)
                (all_no_intersectp l2 l))))

(defthm FullNoIntersectp-All_no_intersectp
  (implies (FullNoIntersectp (ct-sched-nt-sched l prev))
           (all_no_intersectp prev
                              (ct-sched-nt-sched l prev))))

(defthm FullNoIntersectp-ct-scheduler
  (implies (TrLstp TrLst)
           (FullNoIntersectp (ct-sched-nt-sched TrLst prev)))
  :hints (("Subgoal *1/5"
           :use
           (:instance
            FullNoIntersectp-All_no_intersectp
            (l (cdr TrLst))
            (prev (append (test_prev_routes (nth 2 (car trlst))
                                            prev)
                          prev)))
           :in-theory (disable FullNoIntersectp-All_no_intersectp))))

;;-----------------------------------------------------------------
;; end of circuit scheduling
;;-----------------------------------------------------------------


