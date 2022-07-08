(in-package :cl-user)
(defpackage quri.uri
  (:use :cl)
  (:import-from :quri.port
                :scheme-default-port)
  (:export :uri
           :make-basic-uri
           :uri-p
           :uri-scheme
           :uri-userinfo
           :uri-host
           :uri-port
           :uri-path
           :uri-query
           :uri-fragment
           :uri-authority

           :urn
           :make-urn
           :urn-p
           :urn-nid
           :urn-nss))
(in-package :quri.uri)

(defstruct (uri (:constructor %make-uri))
  (scheme nil :read-only t)
  userinfo
  host
  port
  path
  query
  fragment)

(defun make-basic-uri (&rest args &key scheme userinfo host port path query fragment)
  (declare (ignore scheme userinfo host port path query fragment))
  (let ((uri (apply #'%make-uri args)))
    (unless (uri-port uri)
      (setf (uri-port uri) (scheme-default-port (uri-scheme uri))))
    uri))

(defun uri-authority (uri)
  (when (uri-host uri)
    (let ((default-port (scheme-default-port (uri-scheme uri))))
      (with-standard-io-syntax
        (format nil "~:[~;~:*~A@~]~A~:[:~A~;~*~]"
                (uri-userinfo uri)
                (uri-host uri)
                (eql (uri-port uri) default-port)
                (uri-port uri))))))

(defstruct (urn (:include uri (scheme :urn))
                (:constructor %make-urn))
  nid
  nss)

(defun make-urn (&rest initargs)
  (let ((urn (apply #'%make-urn initargs)))
    (when (uri-path urn)
      (let ((colon-pos (position #\: (uri-path urn))))
        (if colon-pos
            (setf (urn-nid urn) (subseq (uri-path urn) 0 colon-pos)
                  (urn-nss urn) (subseq (uri-path urn) (1+ colon-pos)))
            (setf (urn-nid urn) (uri-path urn)))))
    urn))
