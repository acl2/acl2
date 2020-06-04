;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Package: USOCKET; Base: 10 -*-


;;;; See LICENSE for licensing information.

(in-package :usocket)

(defclass genera-socket ()
    ((foreign-address :initform 0 :initarg :foreign-address :accessor gs-foreign-address)
     (foreign-port :initform 0 :initarg :foreign-port :accessor gs-foreign-port)
     (local-address :initform 0 :initarg :local-address :accessor gs-local-address)
     (local-port :initform 0 :initarg :local-port :accessor gs-local-port))
  )

(defclass genera-stream-socket (genera-socket)
    ((stream :initform nil :initarg :stream :accessor gs-stream))
  )

(defclass genera-stream-server-socket (genera-socket)
    ((backlog :initform nil :initarg :backlog :accessor gs-backlog)
     (element-type :initform nil :initarg :element-type :accessor gs-element-type)
     (pending-connections :initform nil :accessor gs-pending-connections))
  )

(defclass genera-datagram-socket (genera-socket)
    ((connection :initform nil :initarg :connection :accessor gs-connection))
  )

(defun host-to-host-object (host)
  (let ((host (host-to-hostname host)))
    (cond ((string-equal host "localhost")
	   net:*local-host*)
	  ((ip-address-string-p host)
	   (let ((quad (dotted-quad-to-vector-quad host)))
	     ;;---*** NOTE: This test is temporary until we have a loopback interface
	     (if (= (aref quad 0) 127)
		 net:*local-host*
		 (net:parse-host (format nil "INTERNET|~A" host)))))
	  (t
	   (net:parse-host host)))))

(defun element-type-to-format (element-type protocol)
  (cond ((null element-type)
	 (ecase protocol
	   (:stream :text)
	   (:datagram :binary)))
	((subtypep element-type 'character)
	 :text)
	(t :binary)))

(defun handle-condition (condition &optional (socket nil) (host-or-ip nil))
  (typecase condition
    ;;---*** TODO: Add additional conditions as appropriate
    (sys:connection-refused
      (error 'connection-refused-error :socket socket))
    ((or tcp::tcp-destination-unreachable-during-connection tcp::udp-destination-unreachable)
      (error 'host-unreachable-error :socket socket))
    (sys:host-not-responding-during-connection
      (error 'timeout-error :socket socket))
    (sys:unknown-host-name
      (error 'ns-host-not-found-error :host-or-ip host-or-ip))
    (sys:network-error
      (error 'unknown-error :socket socket :real-error condition :errno -1))))

(defun socket-connect (host port &key (protocol :stream) element-type
			    timeout deadline (nodelay nil nodelay-p)
			    local-host local-port)
  (declare (ignore local-host))
  (when deadline
    (unsupported 'deadline 'socket-connect))
  (when (and nodelay-p (not (eq nodelay :if-supported)))
    (unsupported 'nodelay 'socket-connect))
  (with-mapped-conditions (nil host)
    (ecase protocol
      (:stream
	(let* ((host-object (host-to-host-object host))
	       (format (element-type-to-format element-type protocol))
	       (characters (eq format :text))
	       (timeout (if timeout
			    (* 60 timeout)
			    tcp:*tcp-connect-timeout*))
	       (stream (tcp:open-tcp-stream host-object port local-port
					    :characters characters
					    :ascii-translation characters
					    :timeout timeout))
	       (gs (make-instance 'genera-stream-socket
				  :stream stream)))
	  (setf (gs-foreign-address gs) (scl:send stream :foreign-address))
	  (setf (gs-foreign-port gs) (scl:send stream :foreign-port))
	  (setf (gs-local-address gs) (scl:send stream :local-address))
	  (setf (gs-local-port gs) (scl:send stream :local-port))
	  (make-stream-socket :socket gs :stream stream)))
      (:datagram
	;;---*** TODO
	(unsupported 'datagram 'socket-connect)))))

(defmethod socket-close ((usocket usocket))
  (with-mapped-conditions (usocket)
    (socket-close (socket usocket))))

(defmethod socket-close ((socket genera-stream-socket))
  (with-slots (stream) socket
    (when stream
      (scl:send (shiftf stream nil) :close nil))))

(defmethod socket-close ((socket genera-stream-server-socket))
  (with-slots (local-port pending-connections) socket
    (when local-port
      (tcp:remove-tcp-port-listener local-port))
    (dolist (tcb pending-connections)
      (tcp::reject-tcb tcb))))

(defmethod socket-close ((socket genera-datagram-socket))
  (with-slots (connection) socket
    (when connection
      (scl:send (shiftf connection nil) :close nil))
    ;;---*** TODO: listening?
    ))

;;; Cribbed from TCP::MAKE-TCB
(defun gensym-tcp-port ()
  (loop as number = (incf tcp::*last-gensym-port-number*) then tcp::*last-gensym-port-number*
	do (cond ((loop for existing-tcb in tcp::*tcb-list*
			thereis (= number (tcp::tcb-local-port existing-tcb))))
		 ((and (<= #.(expt 2 10) number) (< number #.(expt 2 16)))
		  (return number))
		 (t
		  (setq tcp::*last-gensym-port-number* #.(expt 2 10))))))

(defun socket-listen (host port &key (reuse-address nil reuse-address-p)
				     (reuseaddress nil reuseaddress-p)
				     (backlog 5) (element-type 'character))
  (let ((host-object (host-to-host-object host))
	(port (if (zerop port) (gensym-tcp-port) port))
	(reuse-address (cond (reuse-address-p reuse-address)
			     (reuseaddress-p reuseaddress)
			     (t nil))))
    (when (<= port 1024)
      ;; Don't allow listening on "privileged" ports to mimic Unix/Linux semantics
      (error 'operation-not-permitted-error :socket nil))
    (when (tcp:tcp-port-protocol-name port)
      ;; Can't replace a Genera server
      (error 'address-in-use-error :socket nil))
    (when (tcp:tcp-port-listener port)
      (unless reuse-address
	(error 'address-in-use-error :socket nil)))
    (let ((gs (make-instance 'genera-stream-server-socket
			     :backlog backlog
			     :element-type element-type)))
      (setf (gs-local-address gs)
	    (loop for (network address) in (scl:send host-object :network-addresses)
		  when (typep network 'tcp:internet-network)
		    return address))
      (setf (gs-local-port gs) port)
      (flet ((add-to-queue (tcb)
	       (cond ((and (not (zerop (gs-local-address gs)))
			   (not (= (gs-local-address gs) (tcp::tcb-local-address tcb))))
		      ;; Reject if not destined for the proper address
		      (tcp::reject-tcb tcb))
		     ((<= (length (gs-pending-connections gs)) (gs-backlog gs))
		      (tcp::accept-tcb tcb)
		      (tcp::tcb-travel-through-states tcb "Accept" nil :listen :syn-received)
		      (setf (gs-pending-connections gs)
			    (append (gs-pending-connections gs) (list tcb))))
		      (t
			;; Reject if backlog is full
			(tcp::reject-tcb tcb)))))
	(tcp:add-tcp-port-listener port #'add-to-queue))
      (make-stream-server-socket gs :element-type element-type))))

(defmethod socket-accept ((socket stream-server-usocket) &key element-type)
  (with-slots (pending-connections) (socket socket)
    (loop
      (process:process-block "Wait for connection" #'(lambda ()
						       (not (null pending-connections))))
      (let ((tcb (pop pending-connections)))
	(when tcb
	  (let* ((format (element-type-to-format (or element-type (element-type socket))
						 :stream))
		 (characters (eq format :text))
		 (stream (tcp::make-tcp-stream tcb
					       :characters characters
					       :ascii-translation characters))
		 (gs (make-instance 'genera-stream-socket
				    :stream stream)))
	    (setf (gs-foreign-address gs) (scl:send stream :foreign-address))
	    (setf (gs-foreign-port gs) (scl:send stream :foreign-port))
	    (setf (gs-local-address gs) (scl:send stream :local-address))
	    (setf (gs-local-port gs) (scl:send stream :local-port))
	    (return (make-stream-socket :socket gs :stream stream))))))))

(defmethod get-local-address ((usocket usocket))
  (hbo-to-vector-quad (gs-local-address (socket usocket))))

(defmethod get-peer-address ((usocket stream-usocket))
  (hbo-to-vector-quad (gs-foreign-address (socket usocket))))

(defmethod get-local-port ((usocket usocket))
  (gs-local-port (socket usocket)))

(defmethod get-peer-port ((usocket stream-usocket))
  (gs-foreign-port (socket usocket)))

(defmethod get-local-name ((usocket usocket))
  (values (get-local-address usocket)
          (get-local-port usocket)))

(defmethod get-peer-name ((usocket stream-usocket))
  (values (get-peer-address usocket)
          (get-peer-port usocket)))

(defmethod socket-send ((usocket datagram-usocket) buffer size &key host port (offset 0))
  ;;---*** TODO
  (unsupported 'datagram 'socket-send))

(defmethod socket-receive ((socket datagram-usocket) buffer length &key)
  ;;---*** TODO
  (unsupported 'datagram 'socket-receive))

(defun get-host-by-address (address)
  ) ;; TODO

(defun get-hosts-by-name (name)
  (with-mapped-conditions (nil name)
    (let ((host-object (host-to-host-object name)))
      (loop for (network address) in (scl:send host-object :network-addresses)
	    when (typep network 'tcp:internet-network)
	      collect (hbo-to-vector-quad address)))))

(defun %setup-wait-list (wait-list)
  (declare (ignore wait-list)))

(defun %add-waiter (wait-list waiter)
  (declare (ignore wait-list waiter)))

(defun %remove-waiter (wait-list waiter)
  (declare (ignore wait-list waiter)))

(defun wait-for-input-internal (wait-list &key timeout)
  (with-mapped-conditions ()
    (process:process-block-with-timeout timeout "Wait for input"
      #'(lambda (wait-list)
	  (let ((ready-sockets nil))
	    (dolist (waiter (wait-list-waiters wait-list) ready-sockets)
	      (setf (state waiter)
		    (cond ((stream-usocket-p waiter)
			   (if (listen (socket-stream waiter))
			       :read
			       nil))
			  ((datagram-usocket-p waiter)
			   (let ((connection (gs-connection (socket waiter))))
			     (if (and connection
				      (not (scl:send connection :connection-pending-p)))
				 :read
				 nil)))
			  ((stream-server-usocket-p waiter)
			   (if (gs-pending-connections (socket waiter))
			       :read
			       nil))))
	      (when (not (null (state waiter)))
		(setf ready-sockets t)))))
      wait-list)
    wait-list))

