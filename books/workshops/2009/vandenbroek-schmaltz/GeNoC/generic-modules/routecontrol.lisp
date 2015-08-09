#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")#|ACL2s-ToDo-Line|#


(include-book "make-event/defspec" :dir :system)
(include-book "types")

;;
;; Router
;;

(defspec GenericRouteControl
  (((routeControl * *) => (mv * *)))

  (local (defun routeControl (node memory)
           ;; Route a node by trying to route its input ports.
           (mv node memory))))



