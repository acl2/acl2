;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2008  David Lichteblau
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(defpackage #:cl+ssl-test-client-server
  (:use #:cl))
(in-package #:cl+ssl-test-client-server)

(5am:def-suite :cl+ssl.client-server :in :cl+ssl
  :description "Old tests that start a server and communicated with it.
Includes a simple echo test and deadline tests.")

(5am:in-suite :cl+ssl.client-server)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (when bordeaux-threads:*supports-threads-p*
    (push :lisp-with-threads *features*)))

(defvar *port* 8080)

;; The certificate and privatre key were generated with
;;    openssl req -new -x509 -days 365000 -subj / -keyout private-key.pem -noenc -out certificate.pem -outform PEM
(defparameter *cert*
  (namestring
   (asdf:system-relative-pathname "cl+ssl.test"
                                  "test/client-server-certificate.pem")))
(defparameter *key*
  (namestring
   (asdf:system-relative-pathname "cl+ssl.test"
                                  "test/client-server-private-key.pem")))

(defparameter *tests* '())

(defvar *sockets* '())
(defvar *sockets-lock* (bordeaux-threads:make-lock))

(defun record-socket (socket)
  (unless (integerp socket)
    (bordeaux-threads:with-lock-held (*sockets-lock*)
      (push socket *sockets*)))
  socket)

(defun forget-socket (socket)
  (bordeaux-threads:with-lock-held (*sockets-lock*)
    (setf *sockets*
          (delete socket *sockets*)))
  socket)

(defun close-socket (socket &key abort)
  (if (streamp socket)
      (close socket :abort abort)
      (trivial-sockets:close-server socket))
  (forget-socket socket))

(defun check-sockets ()
  ;; Sockets for which close-socket were called
  ;; will be absent in the *sockets*. This includes
  ;; server sockets, which are not streams.
  ;; Stream sockets which are closed by with-open-stream
  ;; will remain in the *sockets*, but in the closed state.
  ;; Everything else is a failure.
  (let ((failures nil))
    (bordeaux-threads:with-lock-held (*sockets-lock*)
      (dolist (socket *sockets*)
        (when (or (not (streamp socket))
                  (open-stream-p socket))
          (push socket failures)))
      (setf *sockets* nil))
    (dolist (sock failures)
      (close-socket sock :abort t))
    (when failures
      (error "failed to close sockets properly:~{  ~A~%~}" failures))))

(defmacro deftest (name &body body)
  `(progn
     (defun ,name ()
       (let ((cl+ssl:*make-ssl-client-stream-verify-default* nil))
         (format t "~%----- ~A ----------------------------~%" ',name)
         (handler-case
             (progn
               ,@body
               (check-sockets)
               (format t "===== [OK] ~A ====================~%" ',name)
               t)
           (error (c)
             (when (typep c 'trivial-sockets:socket-error)
               (setf c (trivial-sockets:socket-nested-error c)))
             (format t "~%===== [FAIL] ~A: ~S ~A~%" ',name (type-of c) c)
             (handler-case
                 (check-sockets)
               (error (c)
                 (format t "muffling follow-up error: ~S: ~A~%" (type-of c) c)))
             nil))))
     (push ',name *tests*)))

(defun run-all-tests ()
  (when (not bordeaux-threads:*supports-threads-p*)
    (format t "~&No thread support in this Lisp implementation~%"))
  (unless (probe-file *cert*) (error "~A not found" *cert*))
  (unless (probe-file *key*) (error "~A not found" *key*))
  (let ((n 0)
        (nok 0))
    (dolist (test (reverse *tests*))
      (when (funcall test)
        (incf nok))
      (incf n))
    (format t "~&passed ~D/~D tests~%" nok n)
    (values nok n)))

(define-condition quit (condition)
  ())

(defparameter *please-quit* t)

(defun make-test-thread (name init main &rest args)
  "Start a thread named NAME, wait until it has funcalled INIT with ARGS
   as arguments, then continue while the thread concurrently funcalls MAIN
   with INIT's return values as arguments."
  (let ((cv (bordeaux-threads:make-condition-variable))
        (lock (bordeaux-threads:make-lock name))
        ;; redirect io manually, because swan's global redirection isn't as
        ;; global as one might hope
        (out *terminal-io*)
        (init-ok nil))
    (bordeaux-threads:with-lock-held (lock)
      (setf *please-quit* nil)
      (prog1
          (bordeaux-threads:make-thread
           (lambda ()
             (flet ((notify ()
                      (bordeaux-threads:with-lock-held (lock)
                        (bordeaux-threads:condition-notify cv))))
               (let ((*terminal-io* out)
                     (*standard-output* out)
                     (*trace-output* out)
                     (*error-output* out))
                 (handler-case
                     (let ((values (multiple-value-list (apply init args))))
                       (setf init-ok t)
                       (notify)
                       (apply main values))
                   (quit ()
                     (notify)
                     t)
                   (error (c)
                     (when (typep c 'trivial-sockets:socket-error)
                       (setf c (trivial-sockets:socket-nested-error c)))
                     (format t "aborting test thread ~A: ~A" name c)
                     (notify)
                     nil)))))
           :name name)
        (bordeaux-threads:condition-wait cv lock)
        (unless init-ok
          (error "failed to start background thread"))))))

(defmacro with-thread ((name init main &rest args) &body body)
  `(invoke-with-thread (lambda () ,@body)
                       ,name
                       ,init
                       ,main
                       ,@args))

(defun invoke-with-thread (body name init main &rest args)
  (let ((thread (apply #'make-test-thread name init main args)))
    (unwind-protect
         (funcall body)
      (setf *please-quit* t)
      (loop
        for delay = 0.0001 then (* delay 2)
        while (and (< delay 0.5) (bordeaux-threads:thread-alive-p thread))
        do
           (sleep delay))
      (when (bordeaux-threads:thread-alive-p thread)
        (format t "~&thread doesn't want to quit, killing it~%")
        (force-output)
        (bordeaux-threads:interrupt-thread thread (lambda () (error 'quit)))
        (loop
          for delay = 0.0001 then (* delay 2)
          while (bordeaux-threads:thread-alive-p thread)
          do
             (sleep delay))))))

(defun init-server (&key (unwrap-stream-p t))
  (format t "~&SSL server listening on port ~d~%" *port*)
  (values (record-socket (trivial-sockets:open-server :port *port*))
          unwrap-stream-p))

(defun test-server (listening-socket unwrap-stream-p)
  (format t "~&SSL server accepting...~%")
  (unwind-protect
       (let* ((socket (record-socket
                       (trivial-sockets:accept-connection
                        listening-socket
                        :element-type '(unsigned-byte 8))))
              (callback nil))
         (when (eq unwrap-stream-p :caller)
           (setf callback (let ((s socket)) (lambda () (close-socket s))))
           (setf socket (cl+ssl:stream-fd socket))
           (setf unwrap-stream-p nil))
         (let ((client (record-socket
                        (cl+ssl:make-ssl-server-stream
                         socket
                         :unwrap-stream-p unwrap-stream-p
                         :close-callback callback
                         :external-format :iso-8859-1
                         :certificate *cert*
                         :key *key*))))
           (unwind-protect
                (loop
                  for line = (prog2
                                 (when *please-quit* (return))
                                 (read-line client nil)
                               (when *please-quit* (return)))
                  while line
                  do
                     (cond
                       ((equal line "freeze")
                        (format t "~&Freezing on client request~%")
                        (loop
                          (sleep 1)
                          (when *please-quit* (return))))
                       (t
                        (format t "~&Responding to query ~A...~%" line)
                        (format client "(echo ~A)~%" line)
                        (force-output client))))
             (close-socket client))))
    (close-socket listening-socket)))

(defun init-client (&key (unwrap-stream-p t))
  (let ((socket (record-socket
                 (trivial-sockets:open-stream
                  "127.0.0.1"
                  *port*
                  :element-type '(unsigned-byte 8))))
        (callback nil))
    (when (eq unwrap-stream-p :caller)
      (setf callback (let ((s socket)) (lambda () (close-socket s))))
      (setf socket (cl+ssl:stream-fd socket))
      (setf unwrap-stream-p nil))
    (cl+ssl:make-ssl-client-stream
     socket
     :unwrap-stream-p unwrap-stream-p
     :close-callback callback
     :external-format :iso-8859-1)))

;; CCL requires specifying the
;; deadline at the socket cration (
;; in constrast to SBCL which has
;; the WITH-TIMEOUT macro).
;;
;; Therefore a separate INIT-CLIENT
;; function is needed for CCL when
;; we need read/write deadlines on
;; the SSL client stream.
#+clozure-common-lisp
(defun ccl-init-client-with-deadline (&key (unwrap-stream-p t)
                                        seconds)
  (let* ((deadline
           (+ (get-internal-real-time)
              (* seconds internal-time-units-per-second)))
         (low
           (record-socket
            (ccl:make-socket
             :address-family :internet
             :connect :active
             :type :stream
             :remote-host "127.0.0.1"
             :remote-port *port*
             :deadline deadline))))
    (cl+ssl:make-ssl-client-stream
     low
     :unwrap-stream-p unwrap-stream-p
     :external-format :iso-8859-1)))

;;; Simple echo-server test.  Write a line and check that the result
;;; watches, three times in a row.
#+lisp-with-threads
(deftest echo
  (with-thread ("simple server" #'init-server #'test-server)
    (with-open-stream (socket (init-client))
      (write-line "test" socket)
      (force-output socket)
      (assert (equal (read-line socket) "(echo test)"))
      (write-line "test2" socket)
      (force-output socket)
      (assert (equal (read-line socket) "(echo test2)"))
      (write-line "test3" socket)
      (force-output socket)
      (assert (equal (read-line socket) "(echo test3)")))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *impl-specific-deadline-condition*
    #+clozure-common-lisp
    'ccl:communication-deadline-expired
    #+sbcl
    'sb-sys:deadline-timeout
    #-(or sbcl clozure-common-lisp)
    nil))

(defun mentions-deadline-p (condition)
  (format t "mentions-deadline-p: ~A: ~A~%" (type-of condition) condition)
  (search (symbol-name *impl-specific-deadline-condition*)
          (format nil "~A" condition)))

;; TODO: that's a bit fragile, becasue missing-deadline-p
;;       expects the text of the deadline condition captured by
;;       Lisp BIO to be copied through OpenSSL error queue to the
;;       condition signalled by ensure-ssl-funcall.
;;       But passing the text to OpenSSL error queue from Lisp BIO
;;       uses vararg functions and will not work on Lips where CFFI
;;       does not support vararg functions. So if we extend deadline
;;       testing to such lisps this approach will not work.
;;       (Note also, if BIO failed to pupulate error queue,
;;       we will have ssl-error-syscall instead of ssl-error-ssl).
(deftype deadline-condition ()
  `(or ,*impl-specific-deadline-condition*
       (and cl+ssl::ssl-error-ssl
            (satisfies mentions-deadline-p))))

#+clozure-common-lisp
(defun ccl-clear-deadline (ssl-flexi-stream)
  (let ((socket-stream (cl+ssl::ssl-stream-socket
                        (flex:flexi-stream-stream ssl-flexi-stream))))
    (assert (ccl:stream-deadline socket-stream))
    (setf (ccl:stream-deadline socket-stream) nil)))


;;; Run tests with different BIO setup strategies:
;;;   - :UNWRAP-STREAMS T
;;;     In this case, CL+SSL will convert the socket to a file descriptor.
;;;   - :UNWRAP-STREAMS :CALLER
;;;     Convert the socket to a file descriptor manually, and give that
;;;     to CL+SSL.
;;;   - :UNWRAP-STREAMS NIL
;;;     Let CL+SSL write to the stream directly, using the Lisp BIO.
(macrolet ((deftests (name (var &rest values) &body body)
             `(progn
                ,@(loop
                    for value in values
                    collect
                    `(deftest ,(intern (format nil "~A-~A" name value))
                       (let ((,var ',value))
                         ,@body))))))

  #+lisp-with-threads
  (deftests unwrap-strategy (usp nil t :caller)
    (with-thread ("echo server for strategy test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (with-open-stream (socket (init-client :unwrap-stream-p usp))
        (write-line "test" socket)
        (force-output socket)
        (assert (equal (read-line socket) "(echo test)")))))

  #+clozure-common-lisp
  (deftests read-deadline (usp nil t :caller)
    (with-thread ("echo server for deadline test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (with-open-stream
          (socket
           (ccl-init-client-with-deadline
            :unwrap-stream-p usp
            :seconds 3))
        (write-line "test" socket)
        (force-output socket)
        (assert (equal (read-line socket) "(echo test)"))
        (unwind-protect
             (handler-case
                 (progn
                   (read-char socket)
                   (error "unexpected data"))
               (deadline-condition ()))
          ;; Prevent the expired deadline
          ;; breaking the socket closure by
          ;; with-open-stream
          (ccl-clear-deadline socket)))))

  #+sbcl
  (deftests read-deadline (usp nil t :caller)
    (with-thread ("echo server for deadline test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (sb-sys:with-deadline (:seconds 3)
        (with-open-stream (socket (init-client :unwrap-stream-p usp))
          (write-line "test" socket)
          (force-output socket)
          (assert (equal (read-line socket) "(echo test)"))
          (handler-case
              (progn
                (read-char socket)
                (error "unexpected data"))
            (deadline-condition ()))))))

  #+clozure-common-lisp
  (deftests write-deadline (usp nil t)
    (with-thread ("echo server for deadline test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (with-open-stream
          (socket
           (ccl-init-client-with-deadline
            :unwrap-stream-p usp
            :seconds 3))
        (unwind-protect
             (progn
               (write-line "test" socket)
               (force-output socket)
               (assert (equal (read-line socket) "(echo test)"))
               (write-line "freeze" socket)
               (force-output socket)
               (let ((n 0))
                 (handler-case
                     (loop
                       (write-line "deadbeef" socket)
                       (incf n))
                   (deadline-condition ()))
                 ;; should have written a couple of lines before the deadline:
                 (assert (> n 100))))
          (handler-case
              (close-socket socket
                            ;; abort, becasue otherwise
                            ;; we would be blocked when close
                            ;; calls SSL_shutdown, which
                            ;; would be unable to send the "close notify"
                            ;; alert to the frozen server
                            :abort t)
            (deadline-condition ()))))))

  #+sbcl
  (deftests write-deadline (usp t
                                ;; nil is not used currently, because
                                ;; SBCL's with-deadline does not work
                                ;; for writing to socket streams (see
                                ;; https://groups.google.com/g/sbcl-devel/c/-eLw-Wv3Prc )
                                ;; So if the Lisp BIO hangs blocked during writing,
                                ;; it remains hanging, deadline does not interrupt it.
                                )
    (with-thread ("echo server for deadline test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (with-open-stream (socket (init-client :unwrap-stream-p usp))
        (unwind-protect
             (sb-sys:with-deadline (:seconds 3)
               (write-line "test" socket)
               (force-output socket)
               (assert (equal (read-line socket) "(echo test)"))
               (write-line "freeze" socket)
               (force-output socket)
               (let ((n 0))
                 (handler-case
                     (loop
                       (write-line "deadbeef" socket)
                       (incf n))
                   (deadline-condition ()))
                 ;; should have written a couple of lines before the deadline:
                 (assert (> n 100))))
          (handler-case
              (close-socket socket :abort t)
            (deadline-condition ()))))))

  #+clozure-common-lisp
  (deftests read-char-no-hang/test (usp nil t :caller)
    (with-thread ("echo server for read-char-no-hang test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (with-open-stream
          (socket (ccl-init-client-with-deadline
                   :unwrap-stream-p usp
                   :seconds 3))
        (write-line "test" socket)
        (force-output socket)
        (assert (equal (read-line socket) "(echo test)"))
        (handler-case
            (when (read-char-no-hang socket)
              (error "unexpected data"))
          (deadline-condition ()
            (error "read-char-no-hang hangs"))))))

  #+sbcl
  (deftests read-char-no-hang/test (usp nil t :caller)
    (with-thread ("echo server for read-char-no-hang test"
                  (lambda () (init-server :unwrap-stream-p usp))
                  #'test-server)
      (sb-sys:with-deadline (:seconds 3)
        (with-open-stream (socket (init-client :unwrap-stream-p usp))
          (write-line "test" socket)
          (force-output socket)
          (assert (equal (read-line socket) "(echo test)"))
          (handler-case
              (when (read-char-no-hang socket)
                (error "unexpected data"))
            (deadline-condition ()
              (error "read-char-no-hang hangs"))))))))

(5am:test all-tests
      (multiple-value-bind (passed total)
          (run-all-tests)
        (5am:is (= passed total))))
