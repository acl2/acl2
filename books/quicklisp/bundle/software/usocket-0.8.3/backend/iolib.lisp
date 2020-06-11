;;;; See LICENSE for licensing information.

(in-package :usocket)

(defparameter *backend* :iolib)

(eval-when (:load-toplevel :execute)
  (shadowing-import 'iolib/sockets:socket-option)
  (export 'socket-option))

(defparameter +iolib-error-map+
 `((iolib/sockets:socket-address-in-use-error        . address-in-use-error)
   (iolib/sockets:socket-address-family-not-supported-error . socket-type-not-supported-error)
   (iolib/sockets:socket-address-not-available-error . address-not-available-error)
   (iolib/sockets:socket-network-down-error          . network-down-error)
   (iolib/sockets:socket-network-reset-error         . network-reset-error)
   (iolib/sockets:socket-network-unreachable-error   . network-unreachable-error)
   ;; (iolib/sockets:socket-no-network-error . ?)
   (iolib/sockets:socket-connection-aborted-error    . connection-aborted-error)
   (iolib/sockets:socket-connection-reset-error      . connection-reset-error)
   (iolib/sockets:socket-connection-refused-error    . connection-refused-error)
   (iolib/sockets:socket-connection-timeout-error    . timeout-error)
   ;; (iolib/sockets:socket-connection-in-progress-error . ?)
   (iolib/sockets:socket-endpoint-shutdown-error     . network-down-error)
   (iolib/sockets:socket-no-buffer-space-error       . no-buffers-error)
   (iolib/sockets:socket-host-down-error             . host-down-error)
   (iolib/sockets:socket-host-unreachable-error      . host-unreachable-error)
   ;; (iolib/sockets:socket-already-connected-error . ?)
   (iolib/sockets:socket-not-connected-error         . connection-refused-error)
   (iolib/sockets:socket-option-not-supported-error  . operation-not-permitted-error)
   (iolib/syscalls:eacces                            . operation-not-permitted-error)
   (iolib/sockets:socket-operation-not-supported-error . operation-not-supported-error)
   (iolib/sockets:unknown-protocol                   . protocol-not-supported-error)
   ;; (iolib/sockets:unknown-interface . ?)
   (iolib/sockets:unknown-service                    . protocol-not-supported-error)
   (iolib/sockets:socket-error                       . socket-error)

   ;; Nameservice errors (src/sockets/dns/conditions.lisp)
   (iolib/sockets:resolver-error                     . ns-error)
   (iolib/sockets:resolver-fail-error                . ns-host-not-found-error)
   (iolib/sockets:resolver-again-error               . ns-try-again-condition)
   (iolib/sockets:resolver-no-name-error             . ns-no-recovery-error)
   (iolib/sockets:resolver-unknown-error             . ns-unknown-error)
   ))

;; IOlib uses (SIMPLE-ARRAY (UNSIGNED-BYTE 16) (8)) to represent IPv6 addresses,
;; while USOCKET shared code uses (SIMPLE-ARRAY (UNSIGNED-BYTE 8) (16)). Here we do the
;; conversion.
(defun iolib-vector-to-vector-quad (host)
  (etypecase host
    ((or (vector t 4)  ; IPv4
         (array (unsigned-byte 8) (4)))
     host)
    ((or (vector t 8) ; IPv6
         (array (unsigned-byte 16) (8)))
      (loop with vector = (make-array 16 :element-type '(unsigned-byte 8))
            for i below 16 by 2
            for word = (aref host (/ i 2))
            do (setf (aref vector i) (ldb (byte 8 8) word)
                     (aref vector (1+ i)) (ldb (byte 8 0) word))
            finally (return vector)))))

(defun handle-condition (condition &optional (socket nil) (host-or-ip nil))
  "Dispatch correct usocket condition."
  (let* ((usock-error (cdr (assoc (type-of condition) +iolib-error-map+)))
	 (usock-error (if (functionp usock-error)
			  (funcall usock-error condition)
                          usock-error)))
    (if usock-error
        (if (typep usock-error 'socket-error)
            (cond ((subtypep usock-error 'ns-error)
                  (error usock-error :socket socket :host-or-ip host-or-ip))
                 (t
                  (error usock-error :socket socket)))
            (cond ((subtypep usock-error 'ns-condition)
                  (signal usock-error :socket socket :host-or-ip host-or-ip))
                 (t
                  (signal usock-error :socket socket))))
        (error 'unknown-error
               :real-error condition
               :socket socket))))

(defun ipv6-address-p (host)
  (iolib/sockets:ipv6-address-p (iolib/sockets:ensure-hostname host)))

(defun socket-connect (host port &key (protocol :stream) (element-type 'character)
                       timeout deadline
                       (nodelay t) ;; nodelay == t is the ACL default
                       local-host local-port)
  (declare (ignore element-type deadline nodelay))
  (with-mapped-conditions (nil host)
    (let* ((remote (when (and host port) (iolib/sockets:ensure-hostname host)))
	   (local  (when (and local-host local-port)
		     (iolib/sockets:ensure-hostname local-host)))
	   (ipv6-p (or (and remote (ipv6-address-p remote)
		       (and local  (ipv6-address-p local)))))
	   (socket (apply #'iolib/sockets:make-socket
			  `(:type ,protocol
			    :address-family :internet
			    :ipv6 ,ipv6-p
			    :connect ,(cond ((eq protocol :stream) :active)
					    ((and host port)       :active)
					    (t                     :passive))
			    ,@(when local
				`(:local-host ,local :local-port ,local-port))
			    :nodelay nodelay))))
      (when remote
	(apply #'iolib/sockets:connect
	       `(,socket ,remote :port ,port ,@(when timeout `(:wait ,timeout))))
	(unless (iolib/sockets:socket-connected-p socket)
	  (close socket)
	  (error 'iolib/sockets:socket-error)))
      (ecase protocol
	(:stream
	 (make-stream-socket :stream socket :socket socket))
	(:datagram
	 (make-datagram-socket socket :connected-p (and remote t)))))))

(defmethod socket-close ((usocket usocket))
  (close (socket usocket)))

(defmethod socket-shutdown ((usocket stream-usocket) direction)
  (with-mapped-conditions ()
    (case direction
      (:input
       (iolib/sockets:shutdown (socket usocket) :read t))
      (:output
       (iolib/sockets:shutdown (socket usocket) :write t))
      (t ; :io by default
       (iolib/sockets:shutdown (socket usocket) :read t :write t)))))

(defun socket-listen (host port
                           &key reuseaddress reuse-address
                           (backlog 5)
                           (element-type 'character))
  (declare (ignore element-type))
  (with-mapped-conditions (nil host)
    (make-stream-server-socket
      (iolib/sockets:make-socket :connect :passive
				 :address-family :internet
				 :local-host (iolib/sockets:ensure-hostname host)
				 :local-port port
				 :backlog backlog
				 :reuse-address (or reuse-address reuseaddress)))))

(defmethod socket-accept ((usocket stream-server-usocket) &key element-type)
  (declare (ignore element-type))
  (with-mapped-conditions (usocket)
    (let ((socket (iolib/sockets:accept-connection (socket usocket))))
      (make-stream-socket :socket socket :stream socket))))

(defmethod get-local-address ((usocket usocket))
  (iolib-vector-to-vector-quad
   (iolib/sockets:address-to-vector (iolib/sockets:local-host (socket usocket)))))

(defmethod get-peer-address ((usocket stream-usocket))
  (iolib-vector-to-vector-quad
   (iolib/sockets:address-to-vector (iolib/sockets:remote-host (socket usocket)))))

(defmethod get-local-port ((usocket usocket))
  (iolib/sockets:local-port (socket usocket)))

(defmethod get-peer-port ((usocket stream-usocket))
  (iolib/sockets:remote-port (socket usocket)))

(defmethod get-local-name ((usocket usocket))
  (values (get-local-address usocket)
          (get-local-port usocket)))

(defmethod get-peer-name ((usocket stream-usocket))
  (values (get-peer-address usocket)
          (get-peer-port usocket)))

(defmethod socket-send ((usocket datagram-usocket) buffer size &key host port (offset 0))
  (apply #'iolib/sockets:send-to
	 `(,(socket usocket) ,buffer :start ,offset :end ,(+ offset size)
			     ,@(when (and host port)
				 `(:remote-host ,(iolib/sockets:ensure-hostname host)
				   :remote-port ,port)))))

(defmethod socket-receive ((usocket datagram-usocket) buffer length &key start end)
  (multiple-value-bind (buffer size host port)
      (iolib/sockets:receive-from (socket usocket)
				  :buffer buffer :size length :start start :end end)
    (values buffer size (iolib-vector-to-vector-quad host) port)))

(defun get-hosts-by-name (name)
  (with-mapped-conditions (nil name)
    (multiple-value-bind (address more-addresses)
        (iolib/sockets:lookup-hostname name :ipv6 iolib/sockets:*ipv6*)
      (mapcar #'(lambda (x) (iolib-vector-to-vector-quad
                             (iolib/sockets:address-name x)))
              (cons address more-addresses)))))

(defun get-host-by-address (address)
  (with-mapped-conditions (nil address)
    nil)) ;; TODO

(defvar *event-base*
  (make-instance 'iolib/multiplex:event-base))

(defun %setup-wait-list (wait-list)
  (setf (wait-list-%wait wait-list)
	(or *event-base*
	    ;; iolib/multiplex:*default-multiplexer* is used here
	    (make-instance 'iolib/multiplex:event-base))))

(defun make-usocket-read-handler (usocket disconnector)
  (lambda (fd event exception)
    (declare (ignore fd event exception))
    (handler-case
	(if (eq (state usocket) :write)
	    (setf (state usocket) :read-write)
	  (setf (state usocket) :read))
      (end-of-file ()
	(funcall disconnector :close)))))

(defun make-usocket-write-handler (usocket disconnector)
  (lambda (fd event exception)
    (declare (ignore fd event exception))
    (handler-case
	(if (eq (state usocket) :read)
	    (setf (state usocket) :read-write)
	  (setf (state usocket) :write))
      (end-of-file ()
	(funcall disconnector :close))
      (iolib/streams:hangup ()
	(funcall disconnector :close)))))

(defun make-usocket-error-handler (usocket disconnector)
  (lambda (fd event exception)
    (declare (ignore fd event exception))
    (handler-case
	(setf (state usocket) nil)
      (end-of-file ()
	(funcall disconnector :close))
      (iolib/streams:hangup ()
	(funcall disconnector :close)))))

(defun make-usocket-disconnector (event-base usocket)
  (declare (ignore event-base))
  (lambda (&rest events)
    (let ((socket (socket usocket)))
      ;; if were asked to close the socket, we do so here
      (when (member :close events)
	(close socket :abort t)))))

(defun %add-waiter (wait-list waiter)
  (let ((event-base (wait-list-%wait wait-list))
	(fd (iolib/sockets:socket-os-fd (socket waiter))))
    ;; reset socket state
    (setf (state waiter) nil)
    ;; set read handler
    (unless (iolib/multiplex::fd-monitored-p event-base fd :read)
      (iolib/multiplex:set-io-handler
        event-base fd :read
	(make-usocket-read-handler waiter
				   (make-usocket-disconnector event-base waiter))))
    ;; set write handler
    #+ignore
    (unless (iolib/multiplex::fd-monitored-p event-base fd :write)
      (iolib/multiplex:set-io-handler
        event-base fd :write
	(make-usocket-write-handler waiter
				    (make-usocket-disconnector event-base waiter))))
    ;; set error handler
    (unless (iolib/multiplex::fd-has-error-handler-p event-base fd)
      (iolib/multiplex:set-error-handler
        event-base fd
	(make-usocket-error-handler waiter
				    (make-usocket-disconnector event-base waiter))))))

(defun %remove-waiter (wait-list waiter)
  (let ((event-base (wait-list-%wait wait-list)))
    (iolib/multiplex:remove-fd-handlers event-base
					(iolib/sockets:socket-os-fd (socket waiter))
					:read t
					:write nil
					:error t)))

;; NOTE: `wait-list-waiters` returns all usockets
(defun wait-for-input-internal (wait-list &key timeout)
  (let ((event-base (wait-list-%wait wait-list)))
    (handler-case
	(iolib/multiplex:event-dispatch event-base :timeout timeout)
      (iolib/streams:hangup ())
      (end-of-file ()))
    ;; close the event-base after use
    (unless (eq event-base *event-base*)
      (close event-base))))
