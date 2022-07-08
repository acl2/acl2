;;; Copyright (C) 2011  David Lichteblau
;;;
;;; See LICENSE for details.

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

;; from cl+ssl/example.lisp
(defun read-line-crlf-2 (stream &optional eof-error-p)
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

(defun write-ssl-certificate-names (ssl-stream &optional (output-stream t))
  (let* ((ssl (ssl-stream-handle ssl-stream))
         (cert (ssl-get-peer-certificate ssl)))
    (unless (cffi:null-pointer-p cert)
      (unwind-protect
           (multiple-value-bind (issuer subject)
               (x509-certificate-names cert)
             (format output-stream
                     "  issuer: ~a~%  subject: ~a~%" issuer subject))
        (x509-free cert)))))

;; from cl+ssl/example.lisp
(defun test-https-client-2 (host &key (port 443) show-text-p)
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
         https)
    (unwind-protect
         (handler-bind
             ((ssl-error-verify
               (lambda (c)
                 (write-ssl-certificate-names (ssl-error-stream c)))))
           (setf https
                 (cl+ssl:make-ssl-client-stream
                  socket
                  :unwrap-stream-p t
                  :external-format '(:iso-8859-1 :eol-style :lf)))
           (write-ssl-certificate-names https)
           (format https "GET / HTTP/1.0~%Host: ~a~%~%" host)
           (force-output https)
           (loop :for line = (read-line-crlf-2 https nil)
              for cnt from 0
              :while line :do
              (when show-text-p
                (format t "HTTPS> ~a~%" line))
              finally (return cnt)))
      (if https
          (close https)
          (close socket)))))

(defparameter *rayservers-ca-certificate-pem-file*
  "rayservers-ca-certificate.pem")

(defparameter *rayservers-ca-certificate-path*
  (merge-pathnames *rayservers-ca-certificate-pem-file*
                   (asdf:system-source-directory :cl+ssl)))

(defparameter *rayservers-ca-certificate-pem*
    "-----BEGIN CERTIFICATE-----
MIIElTCCA32gAwIBAgIJALoXNnj+yvJCMA0GCSqGSIb3DQEBBQUAMIGNMQswCQYD
VQQGEwJQQTELMAkGA1UECBMCTkExFDASBgNVBAcTC1BhbmFtYSBDaXR5MRgwFgYD
VQQKEw9SYXlzZXJ2ZXJzIEdtYkgxGjAYBgNVBAMTEWNhLnJheXNlcnZlcnMuY29t
MSUwIwYJKoZIhvcNAQkBFhZzdXBwb3J0QHJheXNlcnZlcnMuY29tMB4XDTA5MTAx
OTE3MzgyMFoXDTE5MTAxNzE3MzgyMFowgY0xCzAJBgNVBAYTAlBBMQswCQYDVQQI
EwJOQTEUMBIGA1UEBxMLUGFuYW1hIENpdHkxGDAWBgNVBAoTD1JheXNlcnZlcnMg
R21iSDEaMBgGA1UEAxMRY2EucmF5c2VydmVycy5jb20xJTAjBgkqhkiG9w0BCQEW
FnN1cHBvcnRAcmF5c2VydmVycy5jb20wggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAw
ggEKAoIBAQC9rNsCCM+TNp6xDk2yxhXQOStmPTd0txFyduNAj02/nLZV4eq0ZS5n
xXBE6l3MYIMBMV3BgKiy7LsdiRJeZ5HdsV/HRZzXCQI+k4acBjlRC1ZdWMNsIR+H
QUVx2y0wgp+QpcMrgBQZdPI7PobnXCZ6+Fmc50kM7xbIsoWZUzQDpRtUymgOhnnT
4TSb1/XufFHHhDMReRA7s3Co911hzcnZJqL9gFWULlB/RI2ZeVbkp0K4lUXyMZ/R
fnOtCdAA+TkQcpzoyBETV9p5MO8KBOPBskvyGYqVcIZNuxwfC2uoKx0s5b6eMRKR
54B4mB/hIi7i0uGjzuAZdt5iDXQHYaM3AgMBAAGjgfUwgfIwHQYDVR0OBBYEFOyu
Fp80LSc1gwnq5rghs/P8bMgrMIHCBgNVHSMEgbowgbeAFOyuFp80LSc1gwnq5rgh
s/P8bMgroYGTpIGQMIGNMQswCQYDVQQGEwJQQTELMAkGA1UECBMCTkExFDASBgNV
BAcTC1BhbmFtYSBDaXR5MRgwFgYDVQQKEw9SYXlzZXJ2ZXJzIEdtYkgxGjAYBgNV
BAMTEWNhLnJheXNlcnZlcnMuY29tMSUwIwYJKoZIhvcNAQkBFhZzdXBwb3J0QHJh
eXNlcnZlcnMuY29tggkAuhc2eP7K8kIwDAYDVR0TBAUwAwEB/zANBgkqhkiG9w0B
AQUFAAOCAQEAqScS+A2Hajjb+jTKQ19LVPzTpRYo1Jz0SPtzGO91n0efYeRJD5hV
tU+57zGSlUDszARvB+sxzLdJTItK+wEpDM8pLtwUT/VPrRKOoOUBkKBshcTD4HmI
k8uJlNed0QQLP41hFjr+mYd7WM+N5LtFMQAUBMUN6dzEqQIx69EnIoVp0KB8kDwW
/QK5ogKY0g8DmRTFiV036bHQH93kLzyV6FNAldO8vBDqcTeru/uU2Kcn6a8YOfO1
T6MVYory7prWbBaGPKsGw0VgrV9OGbxhbw9EOEYSOgdejvbi9VhgMvEpDYFN7Hnq
0wiHJq5jKECf3bwRe9uVzVMrIeCap/r2uA==
-----END CERTIFICATE-----")

(defun write-rayservers-certificate-pem ()
  (with-open-file (s *rayservers-ca-certificate-path*
                     :direction :output
                     :if-exists :supersede
                     :if-does-not-exist :create)
    (write-string *rayservers-ca-certificate-pem* s)
    *rayservers-ca-certificate-path*))

(defun install-rayservers-ca-certificate ()
  (let ((path (write-rayservers-certificate-pem)))
    (ssl-load-global-verify-locations path)))

(defun test-loom-client (&optional show-text-p)
  (test-https-client-2 "secure.loom.cc" :show-text-p show-text-p))

(defun test-yahoo-client (&optional show-text-p)
  (test-https-client-2 "yahoo.com" :show-text-p show-text-p))

(defmacro expecting-no-errors (&body body)
  `(handler-case
       (progn ,@body)
     (error (c)
       (error "Got an unexpected error: ~a" c))))

(defmacro expecting-error ((type) &body body)
  `(let ((got-error-p nil))
     (handler-case
       (progn ,@body)
       (error (c)
         (unless (typep c ',type)
           (error "Got an unexpected error type: ~a" c))
         (setf got-error-p t)))
     (unless got-error-p
       (error "Did not get expected error."))))

(defun test-verify (&optional quietly)
  (let ((*standard-output*
         ;; test-https-client-2 prints the certificate names
         (if quietly (make-broadcast-stream) *standard-output*)))
    (expecting-no-errors
      (reload)
      (test-loom-client)
      (test-yahoo-client)
      (setf (ssl-check-verify-p) t))
    ;; The Mac appears to have no way to get rid of the default CA certificates
    ;; #+darwin-host is only true in Clozure Common Lisp running on a Mac,
    ;; So this test will fail in SBCL on a Mac
    #-darwin-host
    (expecting-error (ssl-error-verify)
      (test-yahoo-client))
    #+darwin-host
    (expecting-no-errors
      (test-yahoo-client))
    (expecting-error (ssl-error-verify)
      (test-loom-client))
    (expecting-no-errors
      (install-rayservers-ca-certificate)
      (test-loom-client))
    (expecting-no-errors
      (ssl-set-global-default-verify-paths)
      (test-yahoo-client))))
