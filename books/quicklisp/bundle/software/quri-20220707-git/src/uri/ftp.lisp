(in-package :cl-user)
(defpackage quri.uri.ftp
  (:use :cl)
  (:import-from :quri.uri
                :uri
                :scheme
                :port
                :uri-path)
  (:import-from :quri.port
                :scheme-default-port)
  (:export :uri-ftp
           :uri-ftp-p
           :uri-ftp-typecode
           :make-uri-ftp))
(in-package :quri.uri.ftp)

(defstruct (uri-ftp (:include uri (scheme "ftp") (port #.(scheme-default-port "ftp")))
                    (:constructor %make-uri-ftp))
  typecode)

(defun make-uri-ftp (&rest initargs)
  (let ((ftp (apply #'%make-uri-ftp initargs)))
    (multiple-value-bind (path typecode)
        (parse-ftp-typecode (uri-path ftp))
      (when path
        (setf (uri-path ftp) path
              (uri-ftp-typecode ftp) typecode)))
    ftp))

(defun parse-ftp-typecode (path)
  (let ((len (length path)))
    (when (and (< #.(length ";type=") len)
               (string= path ";type="
                        :start1 (- len 1 #.(length ";type="))
                        :end1 (1- len)))
      (let ((typecode (aref path (1- len))))
        (when (or (char= typecode #\a)
                  (char= typecode #\i)
                  (char= typecode #\d))
          (values (subseq path 0 (- len #.(1+ (length ";type="))))
                  typecode))))))
