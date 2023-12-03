;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

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

(defun add-verify-locations (ssl-ctx locations)
  (dolist (location locations)
    (multiple-value-bind (location isfile)
        (validate-verify-location location)
      (cffi:with-foreign-strings ((location-ptr location))
        (unless (= 1 (cl+ssl::ssl-ctx-load-verify-locations
                      ssl-ctx
                      (if isfile location-ptr (cffi:null-pointer))
                      (if isfile (cffi:null-pointer) location-ptr)))
          (error 'ssl-error :queue (read-ssl-error-queue) :message (format nil "Unable to load verify location ~A" location)))))))

(defun ssl-ctx-set-verify-location (ssl-ctx location)
  (cond
    ((eq :default location)
     (unless (= 1 (ssl-ctx-set-default-verify-paths ssl-ctx))
       (error 'ssl-error-call
              :queue (read-ssl-error-queue)
              :message (format nil "Unable to load default verify paths"))))
     ((eq :default-file location)
      ;; supported since openssl 1.1.0
      (unless (= 1 (ssl-ctx-set-default-verify-file ssl-ctx))
        (error 'ssl-error-call
               :queue (read-ssl-error-queue)
               :message (format nil "Unable to load default verify file"))))
     ((eq :default-dir location)
      ;; supported since openssl 1.1.0
      (unless (= 1 (ssl-ctx-set-default-verify-dir ssl-ctx))
        (error 'ssl-error-call
               :queue (read-ssl-error-queue)
               :message (format nil "Unable to load default verify dir"))))
    ((stringp location)
     (add-verify-locations ssl-ctx (list location)))
    ((pathnamep location)
     (add-verify-locations ssl-ctx (list location)))
    ((and location (listp location))
     (add-verify-locations ssl-ctx location))
    ;; silently allow NIL as location
    (location
     (error "Invalid location ~a" location))))

(defun make-context (&key (method nil method-supplied-p)
                          disabled-protocols
                          (options (list +SSL-OP-ALL+))
                          min-proto-version
                          (session-cache-mode +ssl-sess-cache-server+)
                          (verify-location :default)
                          (verify-depth 100)
                          (verify-mode +ssl-verify-peer+)
                          verify-callback
                          cipher-list
                          (pem-password-callback 'pem-password-callback)
                          certificate-chain-file
                          private-key-file
                          private-key-password
                          (private-key-file-type +ssl-filetype-pem+))
  "Creates a new SSL_CTX using SSL_CTX_new and initializes it according to
the specified parameters.

After you're done using the context, don't forget to free it using SSL-CTX-FREE.

Exceptions:

    SSL-ERROR-INITIALIZE. When underlying SSL_CTX_new fails.

Keyword arguments:

    METHOD. Specifies which supported SSL/TLS to use.
        If not specified then TLS_method is used on OpenSSL
        versions supporing it (on legacy versions SSLv23_method is used).

    DISABLED-PROTOCOLS. List of +SSL-OP-NO-* constants. Denotes
        disabled SSL/TLS versions. When METHOD not specified
        defaults to (LIST +SSL-OP-NO-SSLV2+ +SSL-OP-NO-SSLV3+)

    OPTIONS. SSL context options list. Defaults to (list +SSL-OP-ALL+)

    SESSION-CACHE-MODE. Enable/Disable session caching.
        Defaults to +SSL-SESS-CACHE-SERVER+

    VERIFY-LOCATION. Location(s) to load CA from.

        Possible values:
            :DEFAULT - SSL_CTX_set_default_verify_paths will be called.
            :DEFAULT-FILE - SSL_CTX_set_default_verify_file will be called. Requires OpenSSL >= 1.1.0.
            :DEFAULT-DIR - SSL_CTX_set_default_verify_dir will be called. Requires OpenSSL >= 1.1.0.
            A STRING or a PATHNAME - will be passed to SSL_CTX_load_verify_locations
                as file or dir argument depending on wether it's really
                a file or a dir. Must exist on the file system and be available.
            A LIST - each value assumed to be either a STRING or a PATHNAME and
                will be passed to SSL_CTX_load_verify_locations as described above.

    VERIFY-DEPTH. Sets the maximum depth for the certificate chain verification
        that shall be allowed for context. Defaults to 100.

    VERIFY-MODE. The mode parameter to SSL_CTX_set_verify.
        Defaults to +VERIFY-PEER+

    VERIFY-CALLBACK. The verify_callback parameter to SSL_CTX_set_verify.
        Please note: if specified, must be a CFFI callback i.e. defined as
        (DEFCALLBACK :INT ((OK :INT) (SSL-CTX :POINTER)) .. ).

    CIPHER-LIST. If specified, must be a string to pass to SSL_CTX_set_cipher_list.
        An ERROR is signalled if SSL_CTX_set_cipher_list fails.

    PEM-PASSWORD-CALLBACK. Sets the default password callback called when
        loading/storing a PEM certificate with encryption.
        Please note: this must be CFFI callback i.e. defined as
        (CFFI:DEFCALLBACK :INT ((BUF :POINTER) (SIZE :INT) (RWFLAG :INT) (UNUSED :POINTER)) .. ).
        Defaults to PEM-PASSWORD-CALLBACK which simply uses password
        provided by WITH-PEM-PASSWORD.
"
  (ensure-initialized)
  (let ((ssl-ctx (ssl-ctx-new (if method-supplied-p
                                  method
                                  (progn
                                    (unless disabled-protocols
                                      (setf disabled-protocols
                                            (list +SSL-OP-NO-SSLv2+
                                                  +SSL-OP-NO-SSLv3+)))
                                    (funcall (default-ssl-method)))))))
    (when (cffi:null-pointer-p ssl-ctx)
      (error 'ssl-error-initialize :reason "Can't create new SSL-CTX"
                                   :queue (read-ssl-error-queue)))
    (handler-bind ((error (lambda (_)
                            (declare (ignore _))
                            (ssl-ctx-free ssl-ctx))))
      (ssl-ctx-set-options ssl-ctx
                           (apply #'logior
                                  (append disabled-protocols options)))
      ;; Older OpenSSL versions might not have this SSL_ctrl call.
      ;; Having them error out is a sane default - it's better than to keep
      ;; on running with insecure values.
      ;; People that _have_ to use much too old OpenSSL versions will
      ;; have to call MAKE-CONTEXT with :MIN-PROTO-VERSION nil.
      ;;
      ;; As an aside: OpenSSL had the "SSL_OP_NO_TLSv1_2" constant since
      ;;   7409d7ad517    2011-04-29 22:56:51 +0000
      ;; so requiring a "new"er OpenSSL to match CL+SSL's defauls shouldn't be a problem.
      (if min-proto-version
        (if (zerop (ssl-ctx-set-min-proto-version ssl-ctx min-proto-version))
          (error "Couldn't set minimum SSL protocol version!")))
      (ssl-ctx-set-session-cache-mode ssl-ctx session-cache-mode)
      (ssl-ctx-set-verify-location ssl-ctx verify-location)
      (ssl-ctx-set-verify-depth ssl-ctx verify-depth)
      (ssl-ctx-set-verify ssl-ctx verify-mode (if verify-callback
                                                  (cffi:get-callback verify-callback)
                                                  (cffi:null-pointer)))

      (when (and cipher-list
                 (zerop (ssl-ctx-set-cipher-list ssl-ctx cipher-list)))
        (error 'ssl-error-initialize
               :reason
               "Can't set SSL cipher list: SSL_CTX_set_cipher_list returned 0"
               :queue (read-ssl-error-queue)))
      (ssl-ctx-set-default-passwd-cb ssl-ctx (cffi:get-callback pem-password-callback))
      (when certificate-chain-file
        (ssl-ctx-use-certificate-chain-file ssl-ctx certificate-chain-file))
      (when private-key-file
        (with-pem-password (private-key-password)
          (ssl-ctx-use-privatekey-file ssl-ctx private-key-file private-key-file-type)))
      ssl-ctx)))

(defun call-with-global-context (ssl-ctx auto-free-p body-fn)
  (let* ((*ssl-global-context* ssl-ctx))
    (unwind-protect (funcall body-fn)
      (when auto-free-p
        (ssl-ctx-free ssl-ctx)))))

(defmacro with-global-context ((ssl-ctx &key auto-free-p) &body body)
  "Executes the BODY with *SSL-GLOBAL-CONTEXT* bound to the SSL-CTX.
If AUTO-FREE-P is true the context is freed using SSL-CTX-FREE before exit. "
  `(call-with-global-context ,ssl-ctx ,auto-free-p (lambda () ,@body)))
