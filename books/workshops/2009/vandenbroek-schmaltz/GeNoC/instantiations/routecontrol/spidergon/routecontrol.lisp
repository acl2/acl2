#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")#|ACL2s-ToDo-Line|#


(include-book "../../../generic-modules/routecontrol")
;
;; RouteControl
;;

(defun msg-header (msg)
  (DestT msg))

(defun msg-tail (msg)
  (not (FlitT msg)))


(defun portUpdateRoute (port out-port-id)
  ;; Update the value of the localstatus. Which is the routing field with the out-port-id.
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - out-put-id : Port id of the port should be routed to.
  (if (port-bufferHead port)
    (port-updateStatus port (status-updatelocal (port-status port) (update-nth 0 out-port-id (port-statusLocal port))))
    (port-updateStatus port (status-updatelocal (port-status port)  (update-nth 0 out-port-id (port-statusLocal port))))))



(defun spidergonRoutingLogic (s d n)
  ;; calculate the the output port.
  ;;
  ;; Arguments:
  ;; - s : current node id
  ;; - d : destination node id
  ;; - n : number of nodes mod 4

  (cond ((equal s d)
         'loc)
        ((and (< 0 (mod (- d s) (* 4 n)))
              (<= (mod (- d s) (* 4 n)) n))
         'cw)
        ((<= (* 3 n) (mod (- d s) (* 4 n)))
         ;;we go ccw
         'ccw)
        (t  ;; we go accross
         'acr)))


(defun routePorts (ports size)
  ;; If a input port is has a msg in its buffer that has as destination this node route it to the local output port, else
  ;; Route it to the clockwize output port.
  ;;
  ;; Arguments:
  ;; - ports : a list ports
  ;; - id : node id
  ;; - size : number of nodes in the network
  (if (endp ports)
    nil
    (let* ((port (car ports))
           (dest_id (destT (port-bufferHead port))))
    (if (and (equal (port-dir port) 'in)
             (msg-header (port-bufferHead port)))
      ;;If the message is at its destination route to local output port
      ;; else route clockwize
         (cons (portUpdateRoute port (SpidergonRoutingLogic (port-id  port) dest_id size)) (RoutePorts (cdr ports) size))
      (cons port (RoutePorts (cdr ports) size))))))

(defun spidergon-routeControl (node memory)
  ;; Route a node by trying to route its input ports.
  (mv (routePorts node memory) memory))


(definstance GenericRouteControl check-compliance-routecontrol
  :functional-substitution
  ((routecontrol spidergon-routeControl )))


