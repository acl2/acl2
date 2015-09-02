#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/flowcontrol")
(include-book "../../datalink/simple/datalink")
;;
;; Flowcontrol
;;
(defun switchBuffer (nst from to)
  ;; move the head of the buffer of the from port to the tail of the buffer of the to port.
  ;;returns the update nst list.
  ;;
  ;; Arguments:
  ;; - nst : the list of all ports of this node
  ;; - from : The input port which is switched
  ;; - to : The output port which is switched
  (if (endp nst)
    nil
    (if (equal (port-address (car nst)) (port-address to))
      (cons (port-updateBuffer to (port-buffer from)) (switchBuffer (cdr nst) from to))
      (if (equal (port-address (car nst)) (port-address from))
        (cons (port-updateBuffer from nil) (switchBuffer (cdr nst) from to))
        (cons (car nst) (switchBuffer (cdr nst) from to))))))


(defun switch-port (portlist nst from)
  ;; Switch the input port from by looping over the nst in portlist until the port where the from port is routed to is reached.
  ;;
  ;; Arguments:
  ;; - portlist : The list of output ports of this node
  ;; - nst : the list of all ports of this node
  ;; - from : The input port which is switched
  (let ((to (car portlist)))
    (cond ((endp portlist)
           nst)
          ((and (equal (port-portname to) (status-route (port-status from)))
                (endp (port-buffer to)))
           (switchBuffer nst from to))
          (t (switch-port (cdr portlist) nst from)))))


(defun switch-ports (portslist nst)
  ;; Switches each port in portlist. If a port has a msg in its buffer switch the port. The switched ports are returned.
  ;;
  ;; Arguments:
  ;; - portlist : The list of input ports of this node
  ;; - nst : the list of all ports of this node
  (if (endp portslist)
    nst
    (let* ((inport (car portslist)))
      (if (not (endp (port-buffer inport)))  ;; and something to send
        (switch-ports (cdr portslist) (switch-port (ports-outputports nst) nst inport)) ;; clean
        (switch-ports (cdr portslist) nst)))))

(defun packet-FlowControl (nst memory)
  ;; This is the function that performs the flowcontrol in a router. This consists of scheduling the routed input nodes and switching the sheduled msg.
  ;;
  ;; Arguments:
  ;; - nst : list of ports in a node
  ;; - memory : the global memory of a node
  (mv (switch-ports (ports-inputports nst) nst) memory))

(definstance GenericFlowControl check-compliance-Flowcontrol
  :functional-substitution
  ((flowcontrol packet-FlowControl)))#|ACL2s-ToDo-Line|#



