#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;;----------------------------------------------|
;;                                              |
;;                TRANSACTIONS                  |
;;                                              |
;;----------------------------------------------|
;; A transaction is a tuple t = (id A msg B  flits time)
;; Accessors are IdT, OrgT, MsgT, destT, FlitT, TimeT
;; TimeT represent the departure time of the flit

(defun Idt (trans) (car trans))
(defun OrgT (trans) (nth 1 trans))
(defun MsgT (trans) (nth 2 trans))
(defun DestT (trans) (nth 3 trans))
(defun FlitT (trans) (nth 4 trans))
(defun TimeT (trans) (nth 5 trans))

;;
;; Status
;;

(defun PortStatusIn ()
  ;; Construct the structure which contains signals of an input port.
  ;; In this case the nil represants the ackrx signal
  (list nil))

(defun PortStatusOut ()
  ;; Construct the structure which contains signals of an output port.
  ;; In this case the nil represants the tx signal
  (list nil))

(defun PortStatusLocal ()
  ;; Construct the structure of an local flags and registers of a port
  ;; In this case this is just the id of the output port this current input buffer is routed to
  (list nil))

(defun status-updatelocal (status local)
  ;; update the local status of the status
  ;;
  ;; Arguments:
  ;; - status : status of a port
  ;; - local : the local status of a status
  (update-nth 2 local status))


(defun Port (address status data buffer)
  ;; Construct a port
  ;;
  ;; Arguments:
  ;; - adress : The adress of the port
  ;; - status : the status of the port
  ;; - data : the data that is on the connection of the port
  ;; - buffer : The buffer structure of this port
  (list address status data buffer))

(defun port-address (port)
  ;; Get the if of the node of this port
  (mv-nth 0 port))


(defun port-id (port)
  ;; Get the if of the node of this port
  (mv-nth 0 (mv-nth 0 port)))

(defun port-portname (port)
  ;; Get the nodeid of the port. This is the id of the node the port is connected to
  (mv-nth 1 (mv-nth 0 port)))

(defun port-dir (port)
  ;; Get the direction of the port. This can have two values: 'in 'out
  (mv-nth 2 (mv-nth 0 port)))

(defun port-status (port)
  ;; Get the status of the port.
  (mv-nth 1 port))

(defun port-statuslocal (port)
  ;; Get the local status of a port status
  (mv-nth 2 (port-status port)))

(defun port-data (port)
  ;; Get the data of the port.
  (mv-nth 2 port))

(defun port-buffer (port)
  ;; Get the buffer of the port.
  (mv-nth 3 port))

(defun port-nodeAddress (port)
  ;; returns a list of the id of the port and the port name.
  (list (port-id port) (port-portname port)))


(defun port-updateStatus (port status)
  ;; replace the status of a port with a new status
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - status : a Status
  (update-nth 1 status port))

(defun port-updateData (port data)
  ;; replace the data of a port with a new status
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - data : Data of a port
  (update-nth 2 data port))

(defun port-updateBuffer (port buffer)
  ;; replace the buffer of a port with a new status
  ;;
  ;; Arguments:
  ;; - port : a port
  ;; - buffer : buffer of a port
  (update-nth 3 buffer port))

(defun port-updatestatusremote (port)
  ;; Update the second statusof a the status construct of and port. This is the status of the port this port is connected to.
  ;; It should be noted that a node can/should "never" update the status of another node and thus this function should only be used
  ;; When updating the connections after a simulation step in the model. For example in the function updateNeighbours.
  (port-updateStatus port (update-nth 1 (list t) (port-status port))))

(defun port-cleanstatus (port)
  ;; This function "cleans" the status. This means it resets the all but the local status of a the status of a port.
  (port-updateStatus port (list (list nil) (list nil) (port-statuslocal port))))

(defun port-bufferHead (port)
  ;; This function return the head of the buffer
  (car (port-buffer port)))

(defun port-popBuffer (port)
  ;; This function removes the head of the buffer
  (port-updateBuffer port (cdr (port-buffer port))))

(defun port-bufferMsg (port msg)
  ;; This function adds msg to the end of a buffer
  (port-updateBuffer port (append (port-buffer port) (list msg))))


(defun ports-getport (ports id portname dir)
  ;;return the port with id and dir and portname
  ;;
  ;; Arguments:
  ;; - ports : a list of ports
  ;; - id : a id of an port
  ;; - portname : a name of an port
  ;; - dir : a direction of a port
  (if (endp ports)
    nil
    (let ((port (car ports)))
      (if (equal (port-address port) (list id portname dir))
        port
        (ports-getPort (cdr ports) id portname dir)))))

;;
;; Ports
;;

(defun ports-updatePort (ports newport)
  ;;replace port in ports which has the same id and direction whith the new port
  ;;
  ;; Arguments:
  ;; - ports : a list of ports
  ;; - newport : a port
  (if (endp ports)
    nil
    (let ((port (car ports)))
      (if (and (equal (port-id port) (port-id newport))
               (equal (port-dir port) (port-dir newport)))
        (cons newport (cdr ports))
        (cons port (ports-updatePort (cdr ports) newport))))))

(defun ports-getDirection (ports direction)
  ;; returns the list of ports with with the correct direction either 'in or 'out
  ;;
  ;; Arguments:
  ;; - ports : a list of ports
  ;; - dir : a direction of a port
  (if (endp ports)
    nil
    (if (equal (port-dir (car ports)) direction)
      (cons (car ports) (ports-getDirection (cdr ports) direction))
      (ports-getDirection (cdr ports) direction))))


(defun ports-inputPorts (ports)
  ;;Get the list of input ports
  (ports-getDirection ports 'in))


(defun ports-outputPorts (ports)
  ;;Get the list of output ports
  (ports-getDirection ports 'out))

(defun Ports  (topo)
  ;; Construct the list of ports of a node.
  ;; The order statuses of the input and output ports are different. A node is only able to change the first status and the local status.
  ;; The second status is the state of the port it is connected to an thus should be considered read-only from the perspective of the node.
  ;;
  ;; Arguments:
  ;; - topo : a topology
  (list  (port (append topo '(in)) (list (portstatusIn) (portstatusOut) (portstatusLocal)) nil nil)
         (port (append topo '(out)) (list (portstatusOut) (portstatusIn) (portstatusLocal)) nil nil)))


;;
;; Nodes
;;

(defun nodes (topo)
  ;; Build a list of nodes  in the range [x, max]
  ;;
  ;; Arguments:
  ;; - x : start of range
  ;; - max : max of ids
  (if (endp topo)
    nil
    (append  (ports (caar topo))  (Nodes (cdr topo)))))


(defun ports-update (ports node)
  ;; Replace the node in nodes with the node when the id of the node matches
  ;;
  ;; Arguments:
  ;; - nodes : a list of nodes
  ;; - node : node
  (if (or (endp ports)
          (endp node))
    ports
    (if (equal (port-address (car ports)) (port-address (car node)))
      (cons (car node) (ports-update (cdr ports) (cdr node)))
      (cons (car ports) (ports-update (cdr ports) node)))))

(defun ports-nodelist (ports node)
  ;; trasforms a list of ports into al list of lists  of ports in the same node.
  ;; The node variable should be nil in the original call.
  ;;
  ;; Arguments:
  ;; - nodes : a list of nodes
  ;; - node : The current node accumulator
  (if (endp ports)
    nil
    (if (or (equal (port-id (car ports)) (port-id (cadr ports)))
            (not node))
      (ports-nodelist (cdr ports) (append node (list (car ports)) ))
      (append (list (append  node (list (car ports))))  (ports-nodelist (cdr ports) nil)))))



;;
;; Departure
;;


(defun ntkst-arrive (ntkst)
  ;; Extract the arrive messages from the local output ports. Returns  the list of message pressent on the local output ports.
  ;;
  ;; - ntkst : list of ports
  (if (endp ntkst)
    nil
    (if (and (equal (port-portName (car ntkst)) 'loc)
             (equal (port-dir (car ntkst)) 'out))
      (let ((data (port-data (car ntkst))))
        (if data
          (append (list data) (ntkst-arrive (cdr ntkst)))
          (ntkst-arrive (cdr ntkst))))
      (ntkst-arrive (cdr ntkst)))))

(defun ntkst-depart (ntkst msg)
  ;; inserts the transaction into the  input port if the origin of the transaction matches the port
  ;;
  ;; Arguments:
  ;; - ntkst : a list ports
  ;; - msg : the transaction
  (if (endp ntkst)
    nil
    (if (and (equal (port-id (car ntkst)) (orgT msg))
             (equal (port-portname (car ntkst)) 'loc)
             (equal (port-dir (car ntkst)) 'in))
      (cons (port-updatestatusremote (port-updatedata (car ntkst) msg)) (ntkst-depart (cdr ntkst) msg))
      (cons (car ntkst) (ntkst-depart (cdr ntkst) msg)))))

(defun ntkst-canDepart (ntkst msg)
  ;; This function tests if a msg can depart. A msg can depart if the correct port is data line is empty.
  ;;
  ;; Arguments:
  ;; - ntkst : a list ports
  ;; - msg : the transaction
  (if (endp ntkst)
    nil
    (if (and (equal (port-id (car ntkst)) (orgT msg))
             (equal (port-portname (car ntkst)) 'loc)
             (equal (port-dir (car ntkst)) 'in)
             (equal (port-data (car ntkst)) nil))
      t
      (ntkst-canDepart (cdr ntkst) msg))))

(defun ntkst-clearlocaloutputs (ntkst)
  ;; Updates the local output port of the node with "clean" port provides by the function port-clean
  ;;
  ;; Arguments:
  ;; - ntkst : a list of ntkst.
  (if (endp ntkst)
    nil
    (if (and (equal (port-portname (car ntkst)) 'loc)
             (equal (port-dir (car ntkst)) 'out))
      (cons (port-cleanstatus (port-updateData (car ntkst) nil)) (ntkst-clearlocaloutputs (cdr ntkst)))
      (cons (car ntkst) (ntkst-clearlocaloutputs (cdr ntkst))))))

