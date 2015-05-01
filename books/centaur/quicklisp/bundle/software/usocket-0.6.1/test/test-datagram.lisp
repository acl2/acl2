;;;; $Id: test-datagram.lisp 660 2011-05-11 13:08:19Z ctian $
;;;; $URL: svn://common-lisp.net/project/usocket/svn/usocket/tags/0.6.1/test/test-datagram.lisp $

(in-package :usocket-test)

(defvar *echo-server*)
(defvar *echo-server-port*)

(defun start-server ()
  (multiple-value-bind (thread socket)
      (usocket:socket-server "127.0.0.1" 0 #'identity nil
			     :in-new-thread t
			     :protocol :datagram)
    (setq *echo-server* thread
	  *echo-server-port* (usocket:get-local-port socket))))

(defparameter *max-buffer-size* 32)

(defvar *send-buffer*
  (make-array *max-buffer-size* :element-type '(unsigned-byte 8) :initial-element 0))

(defvar *receive-buffer*
  (make-array *max-buffer-size* :element-type '(unsigned-byte 8) :initial-element 0))

(defun clean-buffers ()
  (fill *send-buffer* 0)
  (fill *receive-buffer* 0))

;;; UDP Send Test #1: connected socket
(deftest udp-send.1
  (progn
    (unless (and *echo-server* *echo-server-port*)
      (start-server))
    (let ((s (usocket:socket-connect "127.0.0.1" *echo-server-port* :protocol :datagram)))
      (clean-buffers)
      (replace *send-buffer* #(1 2 3 4 5))
      (usocket:socket-send s *send-buffer* 5)
      (usocket:wait-for-input s :timeout 3)
      (multiple-value-bind (buffer size host port)
	  (usocket:socket-receive s *receive-buffer* *max-buffer-size*)
	(declare (ignore buffer size host port))
	(reduce #'+ *receive-buffer* :start 0 :end 5))))
  15)

;;; UDP Send Test #2: unconnected socket
(deftest udp-send.2
  (progn
    (unless (and *echo-server* *echo-server-port*)
      (start-server))
    (let ((s (usocket:socket-connect nil nil :protocol :datagram)))
      (clean-buffers)
      (replace *send-buffer* #(1 2 3 4 5))
      (usocket:socket-send s *send-buffer* 5 :host "127.0.0.1" :port *echo-server-port*)
      (usocket:wait-for-input s :timeout 3)
      (multiple-value-bind (buffer size host port)
	  (usocket:socket-receive s *receive-buffer* *max-buffer-size*)
	(declare (ignore buffer size host port))
	(reduce #'+ *receive-buffer* :start 0 :end 5))))
  15)
