;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; Package: USOCKET-TEST -*-

(in-package :usocket-test)

;; Test code from "INVALID-ARGUMENT-ERROR on socket-receive (#48)"

;; Author: @4lph4-Ph4un
;; Environment: SBCL 1.4.16, WSL on Windows 10

(defun UDP-one-shot-V1 (&optional (port 1232))
  (let ((socket (usocket:socket-connect
		 nil
		 nil
		 :protocol     :datagram
		 :element-type '(unsigned-byte 8)
		 :local-host   "127.0.0.1"
		 :local-port   port))
	(buffer (make-array 8 :element-type '(unsigned-byte 8))))
    (unwind-protect
	 (multiple-value-bind (received size remote-host remote-port)
	     ;; NOTE: An explicit buffer can be given. If the length
	     ;; is nil buffer's length will be used.
	     (usocket:socket-receive socket buffer 8)
	   (format t "~A~%" received)
	   (usocket:socket-send socket
				(reverse received)
				size
				:host remote-host
				:port remote-port))
      (usocket:socket-close socket))))

#|
Backtrace:
  0: (USOCKET::HANDLE-CONDITION #<SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR {100375B833}> #<USOCKET:DATAGRAM-USOCKET {100375B773}>)
      Locals:
        CONDITION = #<SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR {100375B833}>
        SOCKET = #<USOCKET:DATAGRAM-USOCKET {100375B773}>
  1: (SB-KERNEL::%SIGNAL #<SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR {100375B833}>)
      Locals:
        CONDITION = #<SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR {100375B833}>
        HANDLER-CLUSTERS = (((#<SB-KERNEL::CLASSOID-CELL SB-IMPL::EVAL-ERROR> . #<CLOSURE # {7F0C5FD9DE0B}>)) ((#<SB-KERNEL::CLASSOID-CELL SB-C:COMPILER-ERROR> . #<FUNCTION # {5222748B}>)) ..)
  2: (ERROR SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR :ERRNO 22 :SYSCALL "recvfrom")
      Locals:
        CONDITION = #<SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR {100375B833}>
        #:G8039 = SB-BSD-SOCKETS:INVALID-ARGUMENT-ERROR
        SB-DEBUG::MORE = (:ERRNO 22 :SYSCALL "recvfrom")
  3: (SB-BSD-SOCKETS:SOCKET-ERROR "recvfrom" 22)
      Locals:
        ERRNO = 22
        WHERE = "recvfrom"
  4: ((FLET SB-BSD-SOCKETS::WITH-SOCKET-ADDR-THUNK :IN SB-BSD-SOCKETS:SOCKET-RECEIVE) #<SB-ALIEN-INTERNALS:ALIEN-VALUE :SAP #X7F0C58001230 :TYPE (* (SB-ALIEN:STRUCT SB-BSD-SOCKETS-INTERNAL::SOCKADDR-IN (SB..
      Locals:
        SB-BSD-SOCKETS::COPY-BUFFER = #<SB-ALIEN-INTERNALS:ALIEN-VALUE :SAP #X7F0C58001250 :TYPE (* (ARRAY (SB-ALIEN:UNSIGNED 8) 1))>
        SB-BSD-SOCKETS::SIZE = 16
        SB-BSD-SOCKETS::SOCKADDR = #<SB-ALIEN-INTERNALS:ALIEN-VALUE :SAP #X7F0C58001230 :TYPE (* ..)>
  5: (SB-BSD-SOCKETS::CALL-WITH-SOCKET-ADDR #<SB-BSD-SOCKETS:INET-SOCKET 127.0.0.1:1232, fd: 3 {100375B203}> NIL #<CLOSURE (FLET SB-BSD-SOCKETS::WITH-SOCKET-ADDR-THUNK :IN SB-BSD-SOCKETS:SOCKET-RECEIVE) {7..
      Locals:
        SOCKADDR = #<SB-ALIEN-INTERNALS:ALIEN-VALUE :SAP #X7F0C58001230 :TYPE (* ..)>
        SOCKADDR-ARGS = NIL
        SOCKET = #<SB-BSD-SOCKETS:INET-SOCKET 127.0.0.1:1232, fd: 3 {100375B203}>
        THUNK = #<CLOSURE (FLET SB-BSD-SOCKETS::WITH-SOCKET-ADDR-THUNK :IN SB-BSD-SOCKETS:SOCKET-RECEIVE) {7F0C5FD9DB8B}>
  6: ((:METHOD SB-BSD-SOCKETS:SOCKET-RECEIVE (SB-BSD-SOCKETS:SOCKET T T)) #<SB-BSD-SOCKETS:INET-SOCKET 127.0.0.1:1232, fd: 3 {100375B203}> #(0 0 0 0 0 0 ...) 8 :OOB NIL :PEEK NIL :WAITALL NIL :DONTWAIT NIL..
      Locals:
        #:.DEFAULTING-TEMP. = (UNSIGNED-BYTE 8)
        SB-BSD-SOCKETS::BUFFER = #(0 0 0 0 0 0 ...)
        SB-BSD-SOCKETS::BUFFER#1 = #(0 0 0 0 0 0 ...)
        SB-BSD-SOCKETS::DONTWAIT = NIL
        SB-BSD-SOCKETS::ELEMENT-TYPE = (UNSIGNED-BYTE 8)
        LENGTH = 8
        LENGTH#1 = 8
        SB-BSD-SOCKETS::OOB = NIL
        SB-BSD-SOCKETS::PEEK = NIL
        SB-BSD-SOCKETS:SOCKET = #<SB-BSD-SOCKETS:INET-SOCKET 127.0.0.1:1232, fd: 3 {100375B203}>
        SB-BSD-SOCKETS::WAITALL = NIL
  7: ((:METHOD USOCKET:SOCKET-RECEIVE (USOCKET:DATAGRAM-USOCKET T T)) #<USOCKET:DATAGRAM-USOCKET {100375B773}> #(0 0 0 0 0 0 ...) 8 :ELEMENT-TYPE (UNSIGNED-BYTE 8)) [fast-method]
      Locals:
        USOCKET::BUFFER = #(0 0 0 0 0 0 ...)
        USOCKET::ELEMENT-TYPE = (UNSIGNED-BYTE 8)
        LENGTH = 8
        USOCKET:SOCKET = #<USOCKET:DATAGRAM-USOCKET {100375B773}>
  8: (MASTER-CLASS/SRC/SERVER-03:UDP-ONE-SHOT-V1 1232)
      Locals:
        PORT = 1232
        SOCKET = #<USOCKET:DATAGRAM-USOCKET {100375B773}>
|#

