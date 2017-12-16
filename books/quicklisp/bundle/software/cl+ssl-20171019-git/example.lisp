;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

#|
(load "example.lisp")
(ssl-test::test-https-client "www.google.com")
(ssl-test::test-https-server)
|#

(defpackage :ssl-test
  (:use :cl))
(in-package :ssl-test)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (asdf:operate 'asdf:load-op :trivial-sockets))

(defun read-line-crlf (stream &optional eof-error-p)
  (let ((s (make-string-output-stream)))
    (loop
        for empty = t then nil
  for c = (read-char stream eof-error-p nil)
  while (and c (not (eql c #\return)))
  do
    (unless (eql c #\newline)
      (write-char c s))
  finally
    (return
      (if empty nil (get-output-stream-string s))))))

(defun test-nntps-client (&optional (host "snews.gmane.org") (port 563))
  (let* ((fd (trivial-sockets:open-stream host port
            :element-type '(unsigned-byte 8)))
         (nntps (cl+ssl:make-ssl-client-stream fd :external-format '(:iso-8859-1 :eol-style :lf))))
    (format t "NNTPS> ~A~%" (read-line-crlf nntps))
    (write-line "HELP" nntps)
    (force-output nntps)
    (loop :for line = (read-line-crlf nntps nil)
          :until (string-equal "." line)
          :do (format t "NNTPS> ~A~%" line))))


;; open an HTTPS connection to a secure web server and make a
;; HEAD request
(defun test-https-client (host &optional (port 443))
  (let* ((deadline (+ (get-internal-real-time)
          (* 3 internal-time-units-per-second)))
   (socket (ccl:make-socket :address-family :internet
          :connect :active
          :type :stream
          :remote-host host
          :remote-port port
;;            :local-host (resolve-hostname local-host)
;;           :local-port local-port
          :deadline deadline))
         (https
    (progn
      (cl+ssl:make-ssl-client-stream
       socket
       :unwrap-stream-p t
       :external-format '(:iso-8859-1 :eol-style :lf)))))
    (unwind-protect
  (progn
    (format https "GET / HTTP/1.0~%Host: ~a~%~%" host)
    (force-output https)
    (loop :for line = (read-line-crlf https nil)
          :while line :do
          (format t "HTTPS> ~a~%" line)))
    (close https))))

;; start a simple HTTPS server. See the mod_ssl documentation at
;; <URL:http://www.modssl.org/> for information on generating the
;; server certificate and key
;;
;; You can stress-test the server with
;;
;;    siege -c 10 -u https://host:8080/foobar
;;
(defun test-https-server
    (&key (port 8080)
    (cert "/home/david/newcert.pem")
    (key "/home/david/newkey.pem"))
  (format t "~&SSL server listening on port ~d~%" port)
  (trivial-sockets:with-server (server (:port port))
    (loop
      (let* ((socket (trivial-sockets:accept-connection
          server
          :element-type '(unsigned-byte 8)))
       (client (cl+ssl:make-ssl-server-stream
          socket
          :external-format '(:iso-8859-1 :eol-style :lf)
          :certificate cert
          :key key)))
  (unwind-protect
      (progn
        (loop :for line = (read-line-crlf client nil)
        :while (> (length line) 1) :do
        (format t "HTTPS> ~a~%" line))
        (format client "HTTP/1.0 200 OK~%")
        (format client "Server: SSL-CMUCL/1.1~%")
        (format client "Content-Type: text/plain~%")
        (terpri client)
        (format client "G'day at ~A!~%"
          (multiple-value-list (get-decoded-time)))
        (format client "CL+SSL running in ~A ~A~%"
          (lisp-implementation-type)
          (lisp-implementation-version)))
    (close client))))))
