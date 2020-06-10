;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; Package: USOCKET-TEST -*-
;;;; See LICENSE for licensing information.

;;;; Usage: (usoct:run-usocket-tests) or (usoct:do-tests)

(in-package :usocket-test)

(defparameter +non-existing-host+ "1.2.3.4")
(defparameter +unused-local-port+ 15213)

(defparameter *fake-usocket*
  (usocket::make-stream-socket :socket :my-socket
                               :stream :my-stream))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *common-lisp-net*
    (get-host-by-name "common-lisp.net")))

(defvar *local-ip*)

(defmacro with-caught-conditions ((expect throw) &body body)
  `(catch 'caught-error
     (handler-case
         (handler-bind ((unsupported
                         #'(lambda (c)
                             (declare (ignore c)) (continue))))
           (progn ,@body))
       (unknown-error (c) (if (typep c ',expect)
                                      (throw 'caught-error ,throw)
                                    (progn
                                      (describe c)
                                      (describe
                                       (usocket::usocket-real-error c))
                                      c)))
       (error (c) (if (typep c ',expect)
                      (throw 'caught-error ,throw)
                    (progn
                      (describe c)
                      c)))
       (unknown-condition (c) (if (typep c ',expect)
                                          (throw 'caught-error ,throw)
                                        (progn
                                          (describe c)
                                          (describe
                                           (usocket::usocket-real-condition c))
                                          c)))
       (condition (c) (if (typep c ',expect)
                          (throw 'caught-error ,throw)
                        (progn
                          (describe c)
                          c))))))

(deftest make-socket.1 (socket *fake-usocket*) :my-socket)
(deftest make-socket.2 (socket-stream *fake-usocket*) :my-stream)

(deftest socket-no-connect.1
  (with-caught-conditions (socket-error nil)
    (socket-connect "127.0.0.1" +unused-local-port+ :timeout 1)
    t)
  nil)

(deftest socket-no-connect.2
  (with-caught-conditions (socket-error nil)
    (socket-connect #(127 0 0 1) +unused-local-port+ :timeout 1)
    t)
  nil)

(deftest socket-no-connect.3
  (with-caught-conditions (socket-error nil)
    (socket-connect 2130706433 +unused-local-port+ :timeout 1) ;; == #(127 0 0 1)
    t)
  nil)

(deftest socket-failure.1
  (with-caught-conditions (timeout-error nil)
    (socket-connect 2130706433 +unused-local-port+ :timeout 1) ;; == #(127 0 0 1)
    :unreach)
  nil)

(deftest socket-failure.2
  (with-caught-conditions (timeout-error nil)
    (socket-connect +non-existing-host+ 80 :timeout 1) ;; 80 = just a port
    :unreach)
  nil)

;; let's hope c-l.net doesn't move soon, or that people start to
;; test usocket like crazy..
(deftest socket-connect.1
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect "common-lisp.net" 80)))
      (unwind-protect
          (when (typep sock 'usocket) t)
        (socket-close sock))))
  t)

(deftest socket-connect.2
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect *common-lisp-net* 80)))
      (unwind-protect
          (when (typep sock 'usocket) t)
        (socket-close sock))))
  t)

(deftest socket-connect.3
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect (usocket::host-byte-order *common-lisp-net*) 80)))
      (unwind-protect
          (when (typep sock 'usocket) t)
        (socket-close sock))))
  t)

;; let's hope c-l.net doesn't change its software any time soon
(deftest socket-stream.1
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect "common-lisp.net" 80)))
      (unwind-protect
          (progn
            (format (socket-stream sock)
                    "GET / HTTP/1.0~2%")
            (force-output (socket-stream sock))
            (subseq (read-line (socket-stream sock)) 0 4))
        (socket-close sock))))
  "HTTP")

(deftest socket-name.1
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect *common-lisp-net* 80)))
      (unwind-protect
          (get-peer-address sock)
        (socket-close sock))))
  #.*common-lisp-net*)

(deftest socket-name.2
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect *common-lisp-net* 80)))
      (unwind-protect
          (get-peer-port sock)
        (socket-close sock))))
  80)

(deftest socket-name.3
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect *common-lisp-net* 80)))
      (unwind-protect
          (get-peer-name sock)
        (socket-close sock))))
  #.*common-lisp-net* 80)

#+ignore
(deftest socket-name.4
  (with-caught-conditions (nil nil)
    (let ((sock (socket-connect *common-lisp-net* 80)))
      (unwind-protect
          (equal (get-local-address sock) *local-ip*)
        (socket-close sock))))
  t)

(deftest socket-shutdown.1
    (with-caught-conditions (nil nil)
      (let ((sock (socket-connect *common-lisp-net* 80)))
        (unwind-protect
             (usocket::ignore-unsupported-warnings
               (socket-shutdown sock :input))
          (socket-close sock))
        t))
  t)

(deftest socket-shutdown.2
    (with-caught-conditions (nil nil)
      (let ((sock (socket-connect *common-lisp-net* 80)))
        (unwind-protect
             (usocket::ignore-unsupported-warnings
               (socket-shutdown sock :output))
          (socket-close sock))
        t))
  t)

(defun run-usocket-tests ()
  (do-tests))
