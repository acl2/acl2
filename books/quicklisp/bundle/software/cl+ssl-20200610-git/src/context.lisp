;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl)

(define-condition verify-location-not-found-error (ssl-error)
  ((location :initarg :location))
  (:documentation "Unable to find verify locations")
  (:report (lambda (condition stream)
             (format stream "Unable to find verify location. Path: ~A" (slot-value condition 'location)))))

(defun validate-verify-location (location)
  (handler-case
      (cond
        ((uiop:file-exists-p location)
         (values location t))
        ((uiop:directory-exists-p location)
         (values location nil))
        (t
         (error 'verify-location-not-found-error :location location)))))

(defun add-verify-locations (ctx locations)
  (dolist (location locations)
    (multiple-value-bind (location isfile)
        (validate-verify-location location)
      (cffi:with-foreign-strings ((location-ptr location))
        (unless (= 1 (cl+ssl::ssl-ctx-load-verify-locations
                      ctx
                      (if isfile location-ptr (cffi:null-pointer))
                      (if isfile (cffi:null-pointer) location-ptr)))
          (error 'ssl-error :queue (read-ssl-error-queue) :message (format nil "Unable to load verify location ~A" location)))))))

(defun ssl-ctx-set-verify-location (ctx location)
  (cond
    ((eq :default location)
     (unless (= 1 (ssl-ctx-set-default-verify-paths ctx))
       (error 'ssl-error-call
              :queue (read-ssl-error-queue)
              :message (format nil "Unable to load default verify paths"))))
     ((eq :default-file location)
      ;; supported since openssl 1.1.0
      (unless (= 1 (ssl-ctx-set-default-verify-file ctx))
        (error 'ssl-error-call
               :queue (read-ssl-error-queue)
               :message (format nil "Unable to load default verify file"))))
     ((eq :default-dir location)
      ;; supported since openssl 1.1.0
      (unless (= 1 (ssl-ctx-set-default-verify-dir ctx))
        (error 'ssl-error-call
               :queue (read-ssl-error-queue)
               :message (format nil "Unable to load default verify dir"))))
    ((stringp location)
     (add-verify-locations ctx (list location)))
    ((pathnamep location)
     (add-verify-locations ctx (list location)))
    ((and location (listp location))
     (add-verify-locations ctx location))
    ;; silently allow NIL as location
    (location
     (error "Invalid location ~a" location))))

(alexandria:define-constant +default-cipher-list+
    (format nil
            "ECDHE-RSA-AES256-GCM-SHA384:~
            ECDHE-RSA-AES256-SHA384:~
            ECDHE-RSA-AES256-SHA:~
            ECDHE-RSA-AES128-GCM-SHA256:~
            ECDHE-RSA-AES128-SHA256:~
            ECDHE-RSA-AES128-SHA:~
            ECDHE-RSA-RC4-SHA:~
            DHE-RSA-AES256-GCM-SHA384:~
            DHE-RSA-AES256-SHA256:~
            DHE-RSA-AES256-SHA:~
            DHE-RSA-AES128-GCM-SHA256:~
            DHE-RSA-AES128-SHA256:~
            DHE-RSA-AES128-SHA:~
            AES256-GCM-SHA384:~
            AES256-SHA256:~
            AES256-SHA:~
            AES128-GCM-SHA256:~
            AES128-SHA256:~
            AES128-SHA") :test 'equal)

(cffi:defcallback verify-peer-callback :int ((ok :int) (ctx :pointer))
  (let ((error-code (x509-store-ctx-get-error ctx)))
    (unless (= error-code 0)
      (error 'ssl-error-verify  :error-code error-code))
    ok))

(defun make-context (&key (method nil method-supplied-p)
                          (disabled-protocols)
                          (options (list +SSL-OP-ALL+))
                          (session-cache-mode +ssl-sess-cache-server+)
                          (verify-location :default)
                          (verify-depth 100)
                          (verify-mode +ssl-verify-peer+)
                          (verify-callback nil verify-callback-supplied-p)
                          (cipher-list +default-cipher-list+)
                          (pem-password-callback 'pem-password-callback))
  (ensure-initialized)
  (let ((ctx (ssl-ctx-new (if method-supplied-p
                              method
                              (progn
                                (unless disabled-protocols
                                  (setf disabled-protocols
                                        (list +SSL-OP-NO-SSLv2+ +SSL-OP-NO-SSLv3+)))
                                (funcall (default-ssl-method)))))))
    (when (cffi:null-pointer-p ctx)
      (error 'ssl-error-initialize :reason "Can't create new SSL CTX" :queue (read-ssl-error-queue)))
    (handler-bind ((error (lambda (_)
                            (declare (ignore _))
                            (ssl-ctx-free ctx))))
      (ssl-ctx-set-options ctx (apply #'logior (append disabled-protocols options)))
      (ssl-ctx-set-session-cache-mode ctx session-cache-mode)
      (ssl-ctx-set-verify-location ctx verify-location)
      (ssl-ctx-set-verify-depth ctx verify-depth)
      (ssl-ctx-set-verify ctx verify-mode (if verify-callback
                                              (cffi:get-callback verify-callback)
                                              (if verify-callback-supplied-p
                                                  (cffi:null-pointer)
                                                  (if (= verify-mode +ssl-verify-peer+)
                                                      (cffi:callback verify-peer-callback)
                                                      (cffi:null-pointer)))))
      (ssl-ctx-set-cipher-list ctx cipher-list)
      (ssl-ctx-set-default-passwd-cb ctx (cffi:get-callback pem-password-callback))
      ctx)))

(defun call-with-global-context (context auto-free-p body-fn)
  (let* ((*ssl-global-context* context))
    (unwind-protect (funcall body-fn)
      (when auto-free-p
        (ssl-ctx-free context)))))

(defmacro with-global-context ((context &key auto-free-p) &body body)
  `(call-with-global-context ,context ,auto-free-p (lambda () ,@body)))
