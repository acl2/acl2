#|$ACL2s-Preamble$;
;; Amr HELMY
;; 27th, March 2008
;; GeNoC-synchronisation.lisp
;; this file contains the generic representation of the local
;; synchronisation policies
;; between the nodes, ex: 2 steps and 4 steps handshaking algorithm
;;still a Draft
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "GeNoC-misc")#|ACL2s-ToDo-Line|#


(defspec genericsynchronisation
  (;;req_tans is the equivalent of requesting a transmission in a
   ;;synchronisation protocol, it takes whatever action is suuposed to
   ;;be taken to initialise a communication
   ((req_trans *) => *)
   ;;next function is the function that checks if we can put the
   ;;acknowledge to 1 or not really
   ((process_req * * ) => *)
   ;; this function checks if it's possible to do the transmission and
   ;; if so, it takes the action in case of the possibility of a communication
   ((chk_avail * * * *) => *)
   ;; the next function uses chk_avail to see if it's possible to do a
   ;; transmission it send back the st updated with the required
   ;; action or leaves it as it is
   ;; the check to decide wether the transmission will be done or not
   ;; will be done in the scheduling function by looking at the state
   ;; after the action has been taken by the next function
   ;; the usage of the state only to make the decision is attractive
   ;; however it means we imply the presence of a certain entry to
   ;; change, thus we prefer two values as the  result
   ;; the result of the test + the updated state, in this case the
   ;; user can use the result of the test and not the state
   ((good_route? * * * * ) => (mv * *))
   ;; a cover fucntion used from the scheduling instance that calls
   ;; the previous function
   ((test_routes * *) => (mv * *))
   ;;a test function that will be used by the scheduling in the
   ;;actual check to verify the condition for a communication
   ;;and it sends back a true or nil
   ((check_ack * * *) => *))


  (local
   (defun req_trans (st)
     ;;local witness
     st))
  (local
   ;;modify the name into ack_trans
   (defun process_req (st dest)
     (declare (ignore st dest))
     t))
  (local
   (defun chk_avail (st org dest route)
       (declare (ignore st))
     ;; this local witness is complicated for the simple reason that,
     ;; one of the proof obligations needed to
     ;;prove necessitate the definition of such witness
     ;; the function checks three major conditions needed to verify
     ;; that the origin of a message is different
     ;;from its destination, last element of a route is equal to a route
     ;; finally if the message is not arrived to its destination(route
     ;; length equal 2), the next hop is not equal to the destination
     ;; in instants of this function the user should provide the
     ;; necessary extra conditions needed to schedule a travel
     (and ;(if (equal (len route) 2)
          ;    t
          ;  (not (equal (cadr route) (car (last route)))))
          (not (equal org (car (last (cdr route)))))
          (equal (car (last (cdr route))) dest)
          (no-hops-equal-to-dest route dest)
          (no-consecutive-equals route))))


  (local
   (defun good_route? (st org dest routes)
     (if (endp routes)
         (mv st nil)
       (let ((route (car routes)))
         (if (chk_avail st org dest route)
             (mv st (car route))
           (good_route? st org dest (cdr routes)))))))

  (local
   (defun test_routes (st tr)
     (let* ((routes  (routesv tr))
            (dest (car (last (car routes))))
            (org (orgv tr)))
       (mv-let (newst r?)
               (good_route? st org dest routes)
               (mv newst r?) ))))

  (local
   (defun check_ack (st cur dest)
     (declare (ignore st cur dest))
     t))
  ;;proof obligations
  ;; the result of req_trans is a valid state
  (defthm state-req-trand
    (implies (validstate ntkstate)
             (validstate (req_trans ntkstate))))
  ;; the definition of chk_avail must guarantee the next three conditions
  (defthm chk_avail_obligation-for-scheduling
    (implies (chk_avail st org dest route)
             (and ;(if (equal (len route) 2)  t
                  ;  (not (equal (cadr route) (car (last route)))))
                  ;(not (equal org (car (last (cdr route)))))
                  (equal (car (last (cdr route))) dest)
                  (no-hops-equal-to-dest route dest)
                  (no-consecutive-equals route)))
    :rule-classes :forward-chaining)
  ;; the result of good_route? is a valid state
  (defthm validstate-good_route?
    (implies (validstate ntkstate)
             (validstate (mv-nth 0 (good_route? ntkstate org dest
                                                routes)))))
    ;; the result of test_route is a valid state
  (defthm validdtate-test_routes
    (implies (validstate ntkstate)
             (validstate (mv-nth 0 (test_routes ntkstate tr))))
    :hints (("Goal" :in-theory (disable mv-nth)))))