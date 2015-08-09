#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/routecontrol")
;
;; RouteControl
;;

(defun msg-header (msg)
  ;; Return the destination of the message
  (DestT msg))

(defun portUpdateRoute (port out-port-id)
  ;; Update the value of the localstatus. Which is the routing field with the out-port-id.
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - out-put-id : Port id of the port should be routed to.
  (if (port-bufferhead port)
    (port-updatestatus port (status-updateLocal (port-status port) (list out-port-id)))
    (port-updatestatus port (status-updateLocal (port-status port) (list nil)))))


(defun XYRoutingLogic (current to)
  ;; Compute the output port in order to reach the destination node.
  ;; In XY routing first the horizontal distinance is reduced (x coord)
  ;; If there is no horizaontal diffrence the vertical distance is reduced.
  ;; Finaly if the message is a the destination node the message is routed to the local output.

  ;; Arguments:
  ;; - current : coords of the current node.
  ;; - to : coords of the destination node.
  (let ((x_d (car to))
        (y_d (cadr to))
        (x_o (car current))
        (y_o (cadr current)))
    (if (equal current  to)
      'loc
      (if (not (equal x_d x_o))
        (if (< x_d x_o)
          'W
          'E)
        (if (< y_d y_o)
          'N
          'S)))))#|ACL2s-ToDo-Line|#


(defun routePorts (ports)
  ;; If a input port is has a msg in its buffer that has as destination this node route it to the local output port, else
  ;; Route it to the clockwize output port.
  ;;
  ;; Arguments:
  ;; - ports : a list ports
  (if (endp ports)
    nil
    (let* ((port (car ports))
           (dest_id (destT (port-bufferhead port))))
      (if (and (equal (port-dir port) 'in)
               (msg-header (port-bufferHead port)))
        (cons (portUpdateRoute port (XYRoutingLogic (port-id  port) dest_id ))
              (RoutePorts (cdr ports)))
        (cons port (RoutePorts (cdr ports)))))))

(defun xy-routeControl (node memory)

  ;; Route a node by trying to route its input ports.
  (mv (routePorts node) memory))

(definstance GenericRouteControl check-compliance-routecontrol
  :functional-substitution
  ((routecontrol xy-routeControl )))


