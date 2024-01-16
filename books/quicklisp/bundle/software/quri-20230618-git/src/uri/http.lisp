(in-package :cl-user)
(defpackage quri.uri.http
  (:use :cl)
  (:import-from :quri.uri
                :uri
                :scheme
                :port
                :uri-query)
  (:import-from :quri.port
                :scheme-default-port)
  (:import-from :quri.encode
                :url-encode-params)
  (:import-from :quri.decode
                :url-decode-params)
  (:import-from :alexandria
                :when-let)
  (:export :uri-http
           :make-uri-http
           :uri-http-p

           :uri-https
           :make-uri-https
           :uri-https-p

           :uri-query-params))
(in-package :quri.uri.http)

(defstruct (uri-http (:include uri (scheme "http") (port #.(scheme-default-port "http")))))

(defstruct (uri-https (:include uri-http (scheme "https") (port #.(scheme-default-port "https")))))

(defun uri-query-params (http &key (lenient t))
  (when-let (query (uri-query http))
    (url-decode-params query :lenient lenient)))

(defun (setf uri-query-params) (new http &key lenient)
  (declare (ignore lenient))
  (setf (uri-query http) (if new
                             (url-encode-params new)
                             nil)))
