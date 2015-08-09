#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")


(include-book "../../../generic-modules/GeNoC-synchronization")
(include-book "../../ntkstate/simple/simple")


(defun has-empty-buffers (route ntkstate)
  (if (endp route)
    t
    (if (has-empty-buffer (inst-readbuffers (car route) ntkstate))
      (has-empty-buffers (cdr route) ntkstate)
      nil)))

;; This function checks if all hops in route are free
;; or not in the current state of the network.
;;
;; The function also verifies the route
;; to prove the obligation chk_avail_obligation-for-scheduling.
;;
(defun ct-chk_avail (ntkstate org dest route)
    (and (has-empty-buffers (cdr route) ntkstate)
         (not (equal org (car (last (cdr route)))))
         (equal dest (car (last (cdr route))))
         (no-consecutive-equals route)
         (no-hops-equal-to-dest route dest)
         (>= (len route) 2)))

;; finds a possible route in routes
(defun ct-good_route? (ntkstate org dest routes)
  (if (endp routes)
    (mv ntkstate nil)
    (if (ct-chk_avail ntkstate org dest (car routes))
      (mv ntkstate (car routes))
      ; for now, routes has only one route
      (mv ntkstate nil))))
      ;(ct-good_route? ntkstate org dest (cdr routes)))))

;; the top function to check the route
(defun ct-test_routes (ntkstate tr)
  (let* ((routes  (routesv tr))
         (dest (car (last (car routes))))
         (org (orgv tr)))
    (mv-let (newntkstate r?)
            (ct-good_route? ntkstate org dest routes)
            (mv newntkstate r?))))

(defun ct-req_trans (st)
  st)
(defun ct-process_req (st dest)
  (declare (ignore st dest))
  t)
(defun ct-check_ack (st cur dest)
  (declare (ignore st cur dest))
  t)

;-------------------------------------
; the instantiations used in this file
;------------------------------------
(defmacro inst-chk_avail (ntkstate org dest route)
         (list 'ct-chk_avail ntkstate org dest route))
(defmacro inst-good_route? (ntkstate org dest routes)
         (list 'ct-good_route? ntkstate org dest routes))
(defmacro inst-test_routes (ntkstate tr)
         (list 'ct-test_routes ntkstate tr))
(defmacro inst-req_trans (st)
         (list 'ct-req_trans st))
(defmacro inst-process_trans (st dest)
         (list 'ct-process_trans st dest))
(defmacro inst-check_ack (st cur dest)
         (list 'ct-check_ack st cur dest))


(definstance genericsynchronisation check-compliance-ct-synchronization
  :functional-substitution
  ((req_trans ct-req_trans)
   (process_req ct-process_req)
   (chk_avail ct-chk_avail)
   (good_route? ct-good_route?)
   (test_routes ct-test_routes)
   (check_ack ct-check_ack)
   (loadbuffers inst-Loadbuffers)
   (readbuffers inst-Readbuffers)
   (StateGenerator inst-StateGenerator)
   (ValidstateParamsp inst-ValidStateParamsp))
  :rule-classes nil)#|ACL2s-ToDo-Line|#
