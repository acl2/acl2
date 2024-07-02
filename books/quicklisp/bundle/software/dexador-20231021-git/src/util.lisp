(in-package :cl-user)
(defpackage dexador.util
  (:use :cl)
  (:import-from :fast-io
                :with-fast-output
                :fast-write-byte
                :fast-write-sequence)
  (:import-from :quri
                :uri-path
                :uri-query
                :uri-host
                :uri-port
                :render-uri)
  (:export :*default-connect-timeout*
           :*default-read-timeout*
           :*verbose*
           :*default-proxy*
           :*not-verify-ssl*
           :defun-speedy
           :defun-careful
           :octets
           :ascii-string-to-octets
           :+crlf+
           :*default-user-agent*
           :write-first-line
           :write-header
           :with-header-output
           :write-connect-header
           :make-random-string))
(in-package :dexador.util)

(defvar *default-connect-timeout* 10)
(defvar *default-read-timeout* 10)
(defvar *verbose* nil)
(defvar *not-verify-ssl* nil)
(defvar *default-proxy* (or #-windows (uiop:getenv "HTTPS_PROXY")
                            #-windows (uiop:getenv "HTTP_PROXY"))
  "If specified will be used as the default value of PROXY in calls to dexador.  Defaults to
 the value of the environment variable HTTPS_PROXY or HTTP_PROXY if not on Windows.")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *speedy-declaration* '(declare (optimize (speed 3) (safety 0) (space 0) (compilation-speed 0))))
  (defvar *careful-declaration* '(declare (optimize (speed 3) (safety 2)))))

(defmacro defun-speedy (name lambda-list &body body)
  `(progn
     (declaim (notinline ,name))
     (defun ,name ,lambda-list
       ,*speedy-declaration*
       ,@body)))

(defmacro defun-careful (name lambda-list &body body)
  `(progn
     (declaim (notinline ,name))
     (defun ,name ,lambda-list
       ,*careful-declaration*
       ,@body)))

(deftype octets (&optional (len '*)) `(simple-array (unsigned-byte 8) (,len)))

(declaim (ftype (function (simple-string) octets) ascii-string-to-octets))
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun-speedy %ascii-string-to-octets (string)
    (let ((result (make-array (length string) :element-type '(unsigned-byte 8))))
      (declare (type octets result))
      (dotimes (i (length string) result)
        (declare (type fixnum i))
        (setf (aref result i)
              (char-code (aref string i))))))

  (defun-speedy ascii-string-to-octets (string)
    (%ascii-string-to-octets string))

  (define-compiler-macro ascii-string-to-octets (&whole form string)
    (if (constantp string)
        (%ascii-string-to-octets string)
        form))

  (declaim (type octets +crlf+))
  (defvar +crlf+ (ascii-string-to-octets (format nil "~C~C" #\Return #\Newline))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *dexador-version*
    (asdf:component-version (asdf:find-system :dexador)))

  (defparameter *default-user-agent*
    (format nil "Dexador/~A (~A~@[ ~A~]); ~A;~@[ ~A~]"
            *dexador-version*
            (or (lisp-implementation-type) "Common Lisp")
            (or (lisp-implementation-version) "")
            (or #-clisp (software-type)
                #+(or win32 mswindows) "Windows"
                #-(or win32 mswindows) "Unix")
            (or #-clisp (software-version)))))

(defparameter *header-buffer* nil)

(defun write-first-line (method uri version &optional (buffer *header-buffer*))
  (fast-write-sequence (ascii-string-to-octets (string method)) buffer)
  (fast-write-byte #.(char-code #\Space) buffer)
  (fast-write-sequence (ascii-string-to-octets
                         (format nil "~A~:[~;~:*?~A~]"
                                 (or (uri-path uri) "/")
                                 (uri-query uri)))
                       buffer)
  (fast-write-byte #.(char-code #\Space) buffer)
  (fast-write-sequence (ecase version
                         (1.1 (ascii-string-to-octets "HTTP/1.1"))
                         (1.0 (ascii-string-to-octets "HTTP/1.0")))
                       buffer)
  (fast-write-sequence +crlf+ buffer))

(defun write-header-field (name buffer)
  (fast-write-sequence (if (typep name 'octets)
                           name
                           (ascii-string-to-octets (string-capitalize name)))
                       buffer))

(defun write-header-value (value buffer)
  (fast-write-sequence (if (typep value 'octets)
                           value
                           (ascii-string-to-octets (princ-to-string value)))
                       buffer))

(defun write-header (name value &optional (buffer *header-buffer*))
  (write-header-field name buffer)
  (fast-write-sequence (ascii-string-to-octets ": ") buffer)
  (write-header-value value buffer)
  (fast-write-sequence +crlf+ buffer))

(define-compiler-macro write-header (name value &optional (buffer '*header-buffer*))
  `(progn
     ,(if (and (constantp name)
               (typep name '(or keyword string)))
          `(fast-write-sequence (ascii-string-to-octets ,(string-capitalize name)) ,buffer)
          `(write-header-field ,name ,buffer))
     (fast-write-sequence (ascii-string-to-octets ": ") ,buffer)
     ,(if (constantp value)
          `(fast-write-sequence (ascii-string-to-octets ,(string value)) ,buffer)
          `(write-header-value ,value ,buffer))
     (fast-write-sequence +crlf+ ,buffer)))

(defmacro with-header-output ((buffer &optional output) &body body)
  `(with-fast-output (,buffer ,output)
     (declare (ignorable ,buffer))
     (let ((*header-buffer* ,buffer))
       ,@body)))

(defun write-connect-header (uri version buffer &optional proxy-auth)
  (fast-write-sequence (ascii-string-to-octets "CONNECT") buffer)
  (fast-write-byte #.(char-code #\Space) buffer)
  (fast-write-sequence (ascii-string-to-octets (format nil "~A:~A"
                                                       (uri-host uri)
                                                       (uri-port uri)))
                       buffer)
  (fast-write-byte #.(char-code #\Space) buffer)
  (fast-write-sequence (ecase version
                         (1.1 (ascii-string-to-octets "HTTP/1.1"))
                         (1.0 (ascii-string-to-octets "HTTP/1.0")))
                       buffer)
  (fast-write-sequence +crlf+ buffer)
  (fast-write-sequence (ascii-string-to-octets "Host:") buffer)
  (fast-write-byte #.(char-code #\Space) buffer)
  (fast-write-sequence (ascii-string-to-octets (format nil "~A:~A"
                                                       (uri-host uri)
                                                       (uri-port uri)))
                       buffer)
  (when proxy-auth
    (fast-write-sequence +crlf+ buffer)
    (fast-write-sequence (ascii-string-to-octets "Proxy-Authorization:") buffer)
    (fast-write-byte #.(char-code #\Space) buffer)
    (fast-write-sequence (ascii-string-to-octets proxy-auth) buffer))
  (fast-write-sequence +crlf+ buffer)
  (fast-write-sequence +crlf+ buffer))

(defun-speedy make-random-string (&optional (length 12))
  (declare (type fixnum length))
  (let ((result (make-string length)))
    (declare (type simple-string result))
    (dotimes (i length result)
      (setf (aref result i)
            (ecase (random 5)
              ((0 1) (code-char (+ #.(char-code #\a) (random 26))))
              ((2 3) (code-char (+ #.(char-code #\A) (random 26))))
              ((4) (code-char (+ #.(char-code #\0) (random 10)))))))))
