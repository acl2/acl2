#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/flowcontrol")
(include-book "../../datalink/simple/datalink")

;;
;; Flowcontrol
;;
;; VC stands for Virtualchannel
;; A VC consist of a tuple consisting of (port_id, state)
;; In this implementation the VC is the seccond position of the locate state of a port.

(defun port-VCState (port)
   (mv-nth 1 (mv-nth 2 (mv-nth 1 port))))

(defun port-VCId (port)
   (mv-nth 2 (mv-nth 2 (mv-nth 1 port))))


(defun port-updateVC (port cstate id)
  ;; Updates a virtual channel.
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - cstate : the state to which the the vc should be set. most often 'booked
  ;; - id : the id of the port the vc is connected to.
   (port-updateStatus port (status-updatelocal (port-status port) (update-nth 2  id (update-nth 1 cstate (port-statusLocal port))))))


(defun clearVC (nst portname1)
  ;; Clears the state of the virtual channel
  ;;
  ;; Arguments:
  ;; - nst : list of nst in the node
  ;; - portname1 : name of the from port of the VC
  ;; - portname2 : name of the to port of the VC
  (if (endp nst)
    nil
    (cond ((equal (port-portname (car nst)) portname1)
           (cons (port-updateVC (car nst) nil nil) (clearVC (cdr nst) portname1 )))
          (t (cons (car nst) (clearVC (cdr nst) portname1 ))))))

(defun updateVC (nst portname1 portname2 cstate)
  ;; This function updates and/or creates the state of the virtual channel
  ;;
  ;; Arguments:
  ;; - nst : list of nst in the node
  ;; - portname1 : name of the from port of the VC
  ;; - portname2 : name of the to port of the VC
  ;; - cstate : Virtual channel state.
  (if (endp nst)
    nil
    (cond ((equal (port-portname (car nst)) portname1)
           (cons (port-updateVC (car nst) cstate portname2) (updateVC (cdr nst) portname1 portname2 cstate)))
          (t (cons (car nst) (updateVC (cdr nst) portname1 portname2 cstate))))))


(defun switchBuffer (nst from to)
  ;; move the head of the buffer of the from port to the tail of the buffer of the to port.
  ;;returns the update nst list.
  ;;
  ;; Arguments:
  ;; - nst : the list of all nst of this node
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
  ;; There are three possible cases.
  ;; 1) Its a tail flit and the virtual channel can be switched and cleared.
  ;; 2) Its a data flit and the flit can be swtiched.
  ;; 3) Its a header flit and the virtual channel can be booked.
  ;;
  ;; Arguments:
  ;; - portlist : list of output nst of the node
  ;; - nst : list of pors in the node
  ;; - from : input port trying to switch
  (let ((to (car portlist)))
    (cond ((endp portlist)
           nst)
          ((and (equal (port-portname to) (status-route (port-status from))) ;booked
                (not (port-bufferFull to))  ;; and space in buffer
                (equal (port-VCState to) 'booked) ;was booked
                (equal (port-VCId to) (port-portname from))
                (equal (flitT (port-bufferHead from)) 0))
           (clearVC (switchBuffer nst from to) (port-portname to)))

          ((and (equal (port-portname to) (status-route (port-status from))) ;booked
                (not (port-bufferFull to))  ;; and space in buffer
                (equal (port-VCState to) 'booked)
                (equal (port-VCId to) (port-portname from)))
           (switchBuffer nst from to))

          ((and (equal (port-portname to) (status-route (port-status from))) ;request
                (not (port-bufferFull to))  ;; and space in buffer
                (not (port-VCState to)))
           (updateVC (switchBuffer nst from to) (port-portname to) (port-portname from) 'booked))

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

(defun wormhole-FlowControl (nst memory)
  ;; This is the function that performs the flowcontrol in a router. This consists of scheduling the routed input nodes and switching the sheduled msg.
  (mv (switch-ports (ports-inputports nst) nst) memory))


(definstance GenericFlowControl check-compliance-Flowcontrol
  :functional-substitution
  ((flowcontrol wormhole-FlowControl)))#|ACL2s-ToDo-Line|#
