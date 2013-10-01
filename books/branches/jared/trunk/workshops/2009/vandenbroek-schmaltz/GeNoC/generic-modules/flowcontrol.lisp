#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec" :dir :system)#|ACL2s-ToDo-Line|#

(include-book "types")





;;
;; Router
;;

(defspec GenericFlowControl
  (((flowControl * *) => (mv * *)))
  (local (defun FlowControl (node memory)
           ;; This is the function that performs the flowcontrol in a router. This consists of scheduling the routed input nodes and switching the sheduled msg.
           (mv  node memory))))



