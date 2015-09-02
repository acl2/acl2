#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec" :dir :system)
(include-book "types")#|ACL2s-ToDo-Line|#

(include-book "datalink")
(include-book "routecontrol")
(include-book "flowcontrol")





;;
;; Router
;;

(defspec GenericRouter
  (((Router * *) => (mv * *)))

  (local (defun router (node memory)
           ;; This function represents the router component of a Node.
           ;; Applies the different processes in a router in the correct order.
           (mv-let (node memory)
                   (RouteControl (ProcessInputs node) memory)
                   (mv-let (node memory)
                           (Flowcontrol node memory)
                           (mv (ProcessOutputs node) memory))))))



