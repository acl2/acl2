#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/datalink")

;;
;; Inputs
;;

(defun status-ackrx (status)
  ;; get the ack recieve flag
  (car (mv-nth 0 status)))

(defun status-rx (status)
  ;; get the recieve flag
  (car (mv-nth 1 status)))

(defun port-updateAckRX (port flag)
  ;; Update the ack recieve flag
  (update-nth 1 (update-nth 0  (list flag) (port-status port)) port))

(defun port-updateRX (port flag)
  ;; Update the recieve flag
  (update-nth 1 (update-nth 1  (list flag) (port-status port)) port))

(defun port-bufferFull (port)
  ;; Move the data to the buffer field
  (> (len (port-buffer port)) 2))

(defun port-Data2buffer (port)
  ;; Move the data to the buffer field
  (port-bufferMsg port (port-data port)))

(defun readData (port)
  ;; Move the data to the buffer field and set the ack recieve flag.
  (port-updateAckRX (port-Data2Buffer port) t))

(defun simple-processInputs (ports)
  ;; Process the input ports. There are 3 cases.
  ;; if processing the local input port and the recieve flag is set and the ack flag is not set read the data and clear the port.
  ;; if recieve flag is set and not the ack flag read the data.
  ;; if there is an ack, but there is nothing to send clear the input port
  ;; else do nothing
  (if (endp ports)
    nil
    (if (equal (port-dir (car ports)) 'in)
      (cond

       ((and (equal (port-portname (car ports)) 'loc)
             (status-rx (port-status (car ports)))
             (not (status-ackrx (port-status (car ports))))
             (not (port-bufferFull (car ports))))
        (cons (port-updateRX (port-updateData (readData (car ports)) nil) nil) (simple-processInputs (cdr ports))))

       ((and (status-rx (port-status (car ports)))
             (not (status-ackrx (port-status (car ports))))
             (not (port-bufferFull (car ports))))
        (cons (readData (car ports)) (simple-processInputs (cdr ports))))

       ((status-ackrx (port-status (car ports)))
        (cons (port-updateAckRX (car ports) nil) (simple-processInputs (cdr ports))))

       (t (cons (car ports) (simple-processInputs (cdr ports)))))
      (cons (car ports) (simple-processInputs (cdr ports))))))


;;
;; Outputs
;;

(defun status-tx (status)
  ;;Set the transmission flag
  (car(mv-nth 0 status)))

(defun status-acktx (status)
  ;;Get the response flag
  (car(mv-nth 1 status)))


(defun port-updateTX (port flag)
  ;;Set the transmission flag
  (update-nth 1 (update-nth 0  (list flag) (port-status port)) port))

(defun port-Buffer2Data (port)
  ;;Move the buffer to the data field
  (port-popBuffer (port-updateData port (port-bufferHead port) )))

(defun status-route (status)
  ;; Return the value of the local state of an port. This is used the route value.
  (car (mv-nth 2 status)))

(defun sendData (port)
  ;;Move the buffer to the data field and set the transmission flag.
  (port-updateTx (port-Buffer2Data port) t))



(defun simple-processOutputs (ports)
  ;; Process the output ports. There are 3 cases.
  ;; if sending but there is an ack and there is a msg is ready in the buffer send msg.
  ;; if not sending but msg is ready in the buffer send msg.
  ;; if there is an ack, but there is nothing to send clear the output port
  ;; else do nothing
  (if (endp ports)
    nil
    (if (equal (port-dir (car ports)) 'out)
      (cond

       ((and (status-tx (port-status (car ports)))
             (status-acktx (port-status (car ports)))
             (port-bufferHead (car ports)))
        (cons (sendData (car ports)) (simple-processOutputs (cdr ports))))

       ((and (not (status-tx (port-status (car ports))))
             (port-bufferHead (car ports)))
        (cons (sendData (car ports)) (simple-processOutputs (cdr ports))))

       ((and (status-acktx (port-status (car ports))))
        (cons (port-updatedata (port-updateTX (car ports) nil) nil) (simple-processOutputs (cdr ports))))
       (t (cons (car ports) (simple-processOutputs (cdr ports)))))

      (cons (car ports) (simple-processOutputs (cdr ports))))))

(definstance GenericDatalink check-compliance-datalink
  :functional-substitution
  ((processInputs simple-processInputs)
   (processOutputs simple-processOutputs)))
