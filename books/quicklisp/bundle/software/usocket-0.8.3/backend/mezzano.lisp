;;;; -*- Mode: Common-Lisp -*-

;;;; See LICENSE for licensing information.

(in-package :usocket)

(defun handle-condition (condition &optional (socket nil))
  (typecase condition
    ;; TODO: Add additional conditions as appropriate
    (mezzano.network.tcp:connection-timed-out
     (error 'timeout-error :socket socket))))

(defun socket-connect (host port &key (protocol :stream) element-type
                                      timeout deadline (nodelay nil nodelay-p)
                                      local-host local-port)
  (declare (ignore local-host local-port))
  (when deadline
    (unsupported 'deadline 'socket-connect))
  (when (and nodelay-p (not (eq nodelay :if-supported)))
    (unsupported 'nodelay 'socket-connect))
  (when timeout
    (unsupported 'timeout 'socket-connect))
  (with-mapped-conditions ()
    (ecase protocol
      (:stream
       (let ((s (mezzano.network.tcp:tcp-stream-connect host port :element-type element-type)))
         (make-stream-socket :socket s
                             :stream s)))
      (:datagram
       ;; TODO:
       (unsupported 'datagram 'socket-connect)))))

(defun socket-listen (host port &key reuseaddress
                                     (reuse-address nil reuse-address-supplied-p)
                                     (backlog 5)
                                     (element-type 'character))
  (declare (ignore reuseaddress reuse-address reuse-address-supplied-p))
  (let ((ip (mezzano.network.ip:make-ipv4-address host)))
    (make-stream-server-socket (mezzano.network.tcp:tcp-listen ip port :backlog backlog)
                               :element-type element-type)))

(defun get-hosts-by-name (name)
  (declare (ignore name)))

(defun get-host-by-address (address)
  (declare (ignore address)))

(defun %setup-wait-list (wait-list)
  (declare (ignore wait-list)))

(defun %add-waiter (wait-list waiter)
  (declare (ignore wait-list waiter)))

(defun %remove-waiter (wait-list waiter)
  (declare (ignore wait-list waiter)))

(defun wait-for-input-internal (wait-list &key timeout)
  (declare (ignore wait-list timeout)))

(defmethod socket-close ((usocket stream-usocket))
  (with-mapped-conditions ()
    (close (socket-stream usocket))))

(defmethod socket-close ((usocket stream-server-usocket))
  (with-mapped-conditions ()
    (mezzano.network.tcp:close-tcp-listener (socket usocket))))

(defmethod socket-accept ((usocket stream-server-usocket) &key element-type)
  (declare (ignore element-type))
  (with-mapped-conditions (usocket)
    (let ((s (mezzano.network.tcp:tcp-accept (socket usocket))))
      (make-stream-socket :socket s
                          :stream s))))

(defmethod get-local-name ((usocket stream-usocket))
  (values (get-local-address usocket)
          (get-local-port usocket)))

(defmethod get-peer-name ((usocket stream-usocket))
  (values (get-peer-address usocket)
          (get-peer-port usocket)))

(defmethod get-local-address ((usocket stream-usocket))
  (mezzano.network.ip:ipv4-address-to-string
   (mezzano.network.tcp:tcp-connection-local-ip
    (mezzano.network.tcp:tcp-stream-connection (socket usocket)))))

(defmethod get-local-port ((usocket stream-usocket))
  (mezzano.network.tcp:tcp-connection-local-port
   (mezzano.network.tcp:tcp-stream-connection (socket usocket))))

(defmethod get-peer-address ((usocket stream-usocket))
  (mezzano.network.ip:ipv4-address-to-string
   (mezzano.network.tcp:tcp-connection-remote-ip
    (mezzano.network.tcp:tcp-stream-connection (socket usocket)))))

(defmethod get-peer-port ((usocket stream-usocket))
  (mezzano.network.tcp:tcp-connection-remote-port
   (mezzano.network.tcp:tcp-stream-connection (socket usocket))))
