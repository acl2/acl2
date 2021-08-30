#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/flowcontrol")
(include-book "../../datalink/simple/datalink")

;;
;; Flowcontrol
;;
;; A circuit consist of a tuple consisting of (port_id, state)
;; In this implementation the circuit is the seccond position of the locate state of a port.

(defun port-circuitState (port)
   (mv-nth 1 (mv-nth 2 (mv-nth 1 port))))

(defun port-circuitId (port)
   (mv-nth 2 (mv-nth 2 (mv-nth 1 port))))


(defun port-updateCircuit (port cstate id)
  ;; Updates a virtual channel.
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - cstate : the state to which the the circuit should be set. most often 'booked
  ;; - id : the id of the port the circuit is connected to.
   (port-updateStatus port (status-updatelocal (port-status port) (update-nth 2  id (update-nth 1 cstate (port-statusLocal port))))))


(defun clearCircuit (nst portname1 portname2)
 ;; Clears the state of the virtual channel
  ;;
  ;; Arguments:
  ;; - nst : list of ports in the node
  ;; - portname1 : name of the from port of the circuit
  ;; - portname2 : name of the to port of the circuit
  (if (endp nst)
    nil
    (cond ((equal (port-portname (car nst)) portname1)
           (cons (port-updateCircuit (car nst) nil nil) (clearCircuit (cdr nst) portname1 portname2 )))
          ((equal (port-portname (car nst)) portname2)
           (cons (port-updateCircuit (car nst) nil nil) (clearCircuit (cdr nst) portname1 portname2 )))
          (t (cons (car nst) (clearCircuit (cdr nst) portname1 portname2 ))))))

(defun updateCircuit (nst portname1 portname2 cstate)
  ;; This function updates and/or creates the state of the virtual channel
  ;;
  ;; Arguments:
  ;; - nst : list of ports in the node
  ;; - portname1 : name of the from port of the circuit
  ;; - portname2 : name of the to port of the circuit
  ;; - cstate : Virtual channel state.
  (if (endp nst)
    nil
    (cond ((equal (port-portname (car nst)) portname1)
           (cons (port-updateCircuit (car nst) cstate portname2) (updateCircuit (cdr nst) portname1 portname2 cstate)))
          ((equal (port-portname (car nst)) portname2)
           (cons (port-updateCircuit (car nst) cstate  portname1) (updateCircuit (cdr nst) portname1 portname2 cstate)))
          (t (cons (car nst) (updateCircuit (cdr nst) portname1 portname2 cstate))))))#|ACL2s-ToDo-Line|#


(defun sendack (nst portname)
  (if (endp nst)
    nil
    (if (and (equal (port-portname (car nst)) portname)
               (equal (port-dir (car nst)) 'out))
           (cons (port-BufferMsg (car nst) '(ack)) (cdr nst))
           (cons (car nst) (sendack (cdr nst) portname)))))


(defun switchBuffer (nst from to)
  ;; move the head of the buffer of the from port to the tail of the buffer of the to port.
  ;;returns the update ports list.
  ;;
  ;; Arguments:
  ;; - nst : the list of all ports of this node
  ;; - from : The input port which is switched
  ;; - to : The output port which is switched
  (if (endp nst)
    nil
    (if (equal (port-address (car nst)) (port-address to))
      (cons (port-BufferMsg to (port-bufferHead from)) (switchBuffer (cdr nst) from to))
      (if (equal (port-address (car nst)) (port-address from))
        (cons (port-popBuffer from) (switchBuffer (cdr nst) from to))
        (cons (car nst) (switchBuffer (cdr nst) from to))))))


(defun switch-port (portlist nst from)
  ;; This function loops over the portlist until the output port that the from port is routed to is found.
  ;; Depending on the state of the output port and the virtual channel the port is switched.
  ;; There are five possible cases.
  ;; 1) Its a tail flit and the circuit can be switched and cleared.
  ;; 2) Its a data flit and the flit can be swtiched.
  ;; 3) Its a ack flit and the circuit state can be changes from 'request to 'booked
  ;; 4) Its an arived header flit and a ack can be send back.
  ;; 5) Its a header flit not a the destination and the circuit can be requested.
  ;;
  ;; Arguments:
  ;; - portlist : list of output ports of the node
  ;; - nst : list of pors in the node
  ;; - from : input port trying to switch
  (let ((to (car portlist)))
    (cond ((endp portlist)
           nst)
          ((and (equal (port-portname to) (status-route (port-status from))) ;booked
                 (not (port-bufferFull to))  ;; and space in buffer
                (equal (port-circuitState to) 'booked)
                (equal (port-circuitId to) (port-portname from))
                (equal (flitT (port-buffer from)) 0))
           (clearCircuit (switchBuffer nst from to) (port-portname to) (port-portname from)))

          ((and (equal (port-portname to) (status-route (port-status from))) ;booked
                 (not (port-bufferFull to))  ;; and space in buffer
                (equal (port-circuitState to) 'booked)
                (equal (port-circuitId to) (port-portname from)))
           (switchBuffer nst from to))

          ((and (equal (port-buffer from) '(ack)) ;request to booked
                (not (port-bufferFull to)) ;; and space in buffer
                (equal (port-circuitState to) 'request)
                (equal (port-circuitId to) (port-portname from)))
           (updateCircuit (switchBuffer nst from to) (port-portname to) (port-portname from) 'booked))

          ((and (equal (port-portname to) (status-route (port-status from))) ; send ack
                (not (port-bufferFull to))  ;; and space in buffer
                (equal (port-portname to) 'loc)
                (not (port-circuitState to)))
           (sendack (updateCircuit (switchBuffer nst from to) (port-portname to) (port-portname from) 'booked)
                    (port-portname from)))

          ((and (equal (port-portname to) (status-route (port-status from))) ;request
                (not (port-bufferFull to))  ;; and space in buffer
                (not (port-circuitState to)))
           (updateCircuit (switchBuffer nst from to) (port-portname to) (port-portname from) 'request))

          (t (switch-port (cdr portlist) nst from)))))


(defun switch-ports (portslist nst)
  ;; Switches each port in portlist.
  ;; if a port is routed and has a msg in its buffer switch the port
  (if (endp portslist)
    nst
    (let* ((inport (car portslist)))
      (if (not (endp (port-bufferHead inport)))  ;; and something to send
        (switch-ports (cdr portslist) (switch-port (ports-outputports nst) nst inport)) ;; clean
        (switch-ports (cdr portslist) nst)))))

(defun circuit-FlowControl (nst memory)
  ;; This is the function that performs the flowcontrol in a router. This consists of scheduling the routed input nodes and switching the sheduled msg.
  (mv (switch-ports (ports-inputports nst) nst) memory))

(definstance GenericFlowControl check-compliance-Flowcontrol
  :functional-substitution
  ((flowcontrol circuit-FlowControl)))
