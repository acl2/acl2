#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/router")
(include-book "../../datalink/simple/datalink")
(include-book "../../routecontrol/xy/routecontrol")
(include-book "../../flowcontrol/packet/flowcontrol")

(defun XY-packet-router (node memory)
  ;; This function represents the router component of a Node.
  ;; Applies the different processes in a router in the correct order. The RouterControl and FlowControl get as arguments the memory.
  ;;
  ;; Arguments:
  ;; - node : list of ports in a node
  ;; - memory : the global memory of a node
  (mv-let (node memory)
          (xy-RouteControl (simple-ProcessInputs node) memory)
          (mv-let (node memory)
                  (packet-Flowcontrol node memory)
                  (mv (simple-ProcessOutputs node) memory))))

(definstance GenericRouter check-compliance-router
  :functional-substitution
  ((router XY-packet-router)))


