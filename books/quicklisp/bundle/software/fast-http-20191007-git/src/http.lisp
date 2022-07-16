(in-package :cl-user)
(defpackage fast-http.http
  (:use :cl)
  (:export :http
           :http-request
           :http-response
           :make-http
           :make-http-request
           :make-http-response
           :http-p
           :http-request-p
           :http-response-p

           :http-major-version
           :http-minor-version
           :http-version
           :http-method
           :http-status
           :http-content-length
           :http-chunked-p
           :http-upgrade-p

           :http-headers
           :http-resource
           :http-status-text

           :http-header-read
           :http-mark
           :http-state

           ;; Types
           :status-code

           ;; States
           :+state-first-line+
           :+state-headers+
           :+state-chunk-size+
           :+state-body+
           :+state-chunk-body-end-crlf+
           :+state-trailing-headers+))
(in-package :fast-http.http)

;;
;; Types

(deftype status-code () '(integer 0 10000))

;;
;; States

(defconstant +state-first-line+ 0)
(defconstant +state-headers+ 1)
(defconstant +state-chunk-size+ 2)
(defconstant +state-body+ 3)
(defconstant +state-chunk-body-end-crlf+ 4)
(defconstant +state-trailing-headers+ 5)

(defstruct (http (:conc-name :http-))
  (method nil :type symbol)
  (major-version 0 :type fixnum)
  (minor-version 9 :type fixnum)
  (status 0 :type status-code)
  (content-length nil :type (or null integer))
  (chunked-p nil :type boolean)
  (upgrade-p nil :type boolean)

  headers

  ;; private
  (header-read 0 :type fixnum)
  (mark -1 :type fixnum)
  (state +state-first-line+ :type fixnum))

(defun http-version (http)
  (float
   (+ (http-major-version http)
      (/ (http-minor-version http) 10))))

(defstruct (http-request (:include http)
                         (:conc-name :http-))
  resource)

(defstruct (http-response (:include http)
                          (:conc-name :http-))
  status-text)
