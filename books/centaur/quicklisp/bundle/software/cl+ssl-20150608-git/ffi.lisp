;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

#+xcvb (module (:depends-on ("package" "conditions")))

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

;;; Global state
;;;
(defvar *ssl-global-context* nil)
(defvar *ssl-global-method* nil)
(defvar *bio-lisp-method* nil)

(defparameter *blockp* t)
(defparameter *partial-read-p* nil)

(defun ssl-initialized-p ()
  (and *ssl-global-context* *ssl-global-method*))


;;; Constants
;;;
(defconstant +ssl-filetype-pem+ 1)
(defconstant +ssl-filetype-asn1+ 2)
(defconstant +ssl-filetype-default+ 3)

(defconstant +SSL_CTRL_SET_SESS_CACHE_MODE+ 44)
(defconstant +SSL_CTRL_MODE+ 33)

(defconstant +SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER+ 2)

(defconstant +RSA_F4+ #x10001)

(defvar *tmp-rsa-key-512* nil)
(defvar *tmp-rsa-key-1024* nil)
(defvar *tmp-rsa-key-2048* nil)

;;; Misc
;;;
(defmacro while (cond &body body)
  `(do () ((not ,cond)) ,@body))


;;; Function definitions
;;;
(declaim (inline ssl-write ssl-read ssl-connect ssl-accept))

(cffi:defctype ssl-method :pointer)
(cffi:defctype ssl-ctx :pointer)
(cffi:defctype ssl-pointer :pointer)

(cffi:defcfun ("SSL_get_version" ssl-get-version)
    :string
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_load_error_strings" ssl-load-error-strings)
    :void)
(cffi:defcfun ("SSL_library_init" ssl-library-init)
    :int)
;;
;; We don't refer SSLv2_client_method as the default
;; builds of OpenSSL do not have it, due to insecurity
;; of the SSL v2 protocol (see https://www.openssl.org/docs/ssl/SSL_CTX_new.html
;; and https://github.com/cl-plus-ssl/cl-plus-ssl/issues/6)
;;
;; (cffi:defcfun ("SSLv2_client_method" ssl-v2-client-method)
;;     ssl-method)
(cffi:defcfun ("SSLv23_client_method" ssl-v23-client-method)
    ssl-method)
(cffi:defcfun ("SSLv23_server_method" ssl-v23-server-method)
    ssl-method)
(cffi:defcfun ("SSLv23_method" ssl-v23-method)
    ssl-method)
(cffi:defcfun ("SSLv3_client_method" ssl-v3-client-method)
    ssl-method)
(cffi:defcfun ("SSLv3_server_method" ssl-v3-server-method)
    ssl-method)
(cffi:defcfun ("SSLv3_method" ssl-v3-method)
    ssl-method)
(cffi:defcfun ("TLSv1_client_method" ssl-TLSv1-client-method)
    ssl-method)
(cffi:defcfun ("TLSv1_server_method" ssl-TLSv1-server-method)
    ssl-method)
(cffi:defcfun ("TLSv1_method" ssl-TLSv1-method)
    ssl-method)

(cffi:defcfun ("SSL_CTX_new" ssl-ctx-new)
    ssl-ctx
  (method ssl-method))
(cffi:defcfun ("SSL_new" ssl-new)
    ssl-pointer
  (ctx ssl-ctx))
(cffi:defcfun ("SSL_get_fd" ssl-get-fd)
    :int
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_set_fd" ssl-set-fd)
    :int
  (ssl ssl-pointer)
  (fd :int))
(cffi:defcfun ("SSL_set_bio" ssl-set-bio)
    :void
  (ssl ssl-pointer)
  (rbio :pointer)
  (wbio :pointer))
(cffi:defcfun ("SSL_get_error" ssl-get-error)
    :int
  (ssl ssl-pointer)
  (ret :int))
(cffi:defcfun ("SSL_set_connect_state" ssl-set-connect-state)
    :void
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_set_accept_state" ssl-set-accept-state)
    :void
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_connect" ssl-connect)
    :int
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_accept" ssl-accept)
    :int
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_write" ssl-write)
    :int
  (ssl ssl-pointer)
  (buf :pointer)
  (num :int))
(cffi:defcfun ("SSL_read" ssl-read)
    :int
  (ssl ssl-pointer)
  (buf :pointer)
  (num :int))
(cffi:defcfun ("SSL_shutdown" ssh-shutdown)
    :void
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_free" ssl-free)
    :void
  (ssl ssl-pointer))
(cffi:defcfun ("SSL_CTX_free" ssl-ctx-free)
    :void
  (ctx ssl-ctx))
(cffi:defcfun ("BIO_ctrl" bio-set-fd)
    :long
  (bio :pointer)
  (cmd :int)
  (larg :long)
  (parg :pointer))
(cffi:defcfun ("BIO_new_socket" bio-new-socket)
    :pointer
  (fd :int)
  (close-flag :int))
(cffi:defcfun ("BIO_new" bio-new)
    :pointer
  (method :pointer))

(cffi:defcfun ("ERR_get_error" err-get-error)
    :unsigned-long)
(cffi:defcfun ("ERR_error_string" err-error-string)
    :string
  (e :unsigned-long)
  (buf :pointer))

(cffi:defcfun ("SSL_set_cipher_list" ssl-set-cipher-list)
    :int
  (ssl ssl-pointer)
  (str :string))
(cffi:defcfun ("SSL_use_RSAPrivateKey_file" ssl-use-rsa-privatekey-file)
    :int
  (ssl ssl-pointer)
  (str :string)
  ;; either +ssl-filetype-pem+ or +ssl-filetype-asn1+
  (type :int))
(cffi:defcfun
    ("SSL_CTX_use_RSAPrivateKey_file" ssl-ctx-use-rsa-privatekey-file)
    :int
  (ctx ssl-ctx)
  (type :int))
(cffi:defcfun ("SSL_use_certificate_file" ssl-use-certificate-file)
    :int
  (ssl ssl-pointer)
  (str :string)
  (type :int))
(cffi:defcfun ("SSL_CTX_use_certificate_chain_file" ssl-ctx-use-certificate-chain-file)
    :int
  (ctx ssl-ctx)
  (str :string))
(cffi:defcfun ("SSL_CTX_load_verify_locations" ssl-ctx-load-verify-locations)
    :int
  (ctx ssl-ctx)
  (CAfile :string)
  (CApath :string))
(cffi:defcfun ("SSL_CTX_set_client_CA_list" ssl-ctx-set-client-ca-list)
    :void
  (ctx ssl-ctx)
  (list ssl-pointer))
(cffi:defcfun ("SSL_load_client_CA_file" ssl-load-client-ca-file)
    ssl-pointer
  (file :string))

(cffi:defcfun ("SSL_CTX_ctrl" ssl-ctx-ctrl)
    :long
  (ctx ssl-ctx)
  (cmd :int)
  (larg :long)
  (parg :pointer))

(cffi:defcfun ("SSL_ctrl" ssl-ctrl)
    :long
  (ssl :pointer)
  (cmd :int)
  (larg :long)
  (parg :pointer))

(cffi:defcfun ("SSL_CTX_set_default_passwd_cb" ssl-ctx-set-default-passwd-cb)
    :void
  (ctx ssl-ctx)
  (pem_passwd_cb :pointer))

(cffi:defcfun ("CRYPTO_num_locks" crypto-num-locks) :int)
(cffi:defcfun ("CRYPTO_set_locking_callback" crypto-set-locking-callback)
    :void
  (fun :pointer))
(cffi:defcfun ("CRYPTO_set_id_callback" crypto-set-id-callback)
    :void
  (fun :pointer))

(cffi:defcfun ("RAND_seed" rand-seed)
    :void
  (buf :pointer)
  (num :int))
(cffi:defcfun ("RAND_bytes" rand-bytes)
    :int
  (buf :pointer)
  (num :int))

(cffi:defcfun ("SSL_CTX_set_verify_depth" ssl-ctx-set-verify-depth)
    :void
  (ctx :pointer)
  (depth :int))

(cffi:defcfun ("SSL_get_verify_result" ssl-get-verify-result)
    :long
  (ssl ssl-pointer))

(cffi:defcfun ("SSL_get_peer_certificate" ssl-get-peer-certificate)
    :pointer
  (ssl ssl-pointer))

(cffi:defcfun ("X509_free" x509-free)
    :void
  (x509 :pointer))

(cffi:defcfun ("X509_NAME_oneline" x509-name-oneline)
    :pointer
  (x509-name :pointer)
  (buf :pointer)
  (size :int))

(cffi:defcfun ("X509_get_issuer_name" x509-get-issuer-name)
    :pointer                            ; *X509_NAME
  (x509 :pointer))

(cffi:defcfun ("X509_get_subject_name" x509-get-subject-name)
    :pointer                            ; *X509_NAME
  (x509 :pointer))

(cffi:defcfun ("SSL_CTX_set_default_verify_paths" ssl-ctx-set-default-verify-paths)
    :int
  (ctx :pointer))

(cffi:defcfun ("RSA_generate_key" rsa-generate-key)
    :pointer
  (num :int)
  (e :unsigned-long)
  (callback :pointer)
  (opt :pointer))

(cffi:defcfun ("RSA_free" rsa-free)
    :void
  (rsa :pointer))

(cffi:defcfun ("SSL_CTX_set_tmp_rsa_callback" ssl-ctx-set-tmp-rsa-callback)
    :pointer
  (ctx :pointer)
  (callback :pointer))

(cffi:defcallback need-tmp-rsa-callback :pointer ((ssl :pointer) (export-p :int) (key-length :int))
  (declare (ignore ssl export-p))
  (flet ((rsa-key (length)
           (rsa-generate-key length
                             +RSA_F4+
                             (cffi:null-pointer)
                             (cffi:null-pointer))))
    (cond ((= key-length 512)
           (unless *tmp-rsa-key-512*
             (setf *tmp-rsa-key-512* (rsa-key key-length)))
           *tmp-rsa-key-512*)
          ((= key-length 1024)
           (unless *tmp-rsa-key-1024*
             (setf *tmp-rsa-key-1024* (rsa-key key-length)))
           *tmp-rsa-key-1024*)
          (t
           (unless *tmp-rsa-key-2048*
             (setf *tmp-rsa-key-2048* (rsa-key key-length)))
           *tmp-rsa-key-2048*))))

;;; Funcall wrapper
;;;
(defvar *socket*)

(declaim (inline ensure-ssl-funcall))
(defun ensure-ssl-funcall (stream handle func &rest args)
  (loop
     (let ((nbytes
	    (let ((*socket* (ssl-stream-socket stream))) ;for Lisp-BIO callbacks
	      (apply func args))))
       (when (plusp nbytes)
	 (return nbytes))
       (let ((error (ssl-get-error handle nbytes)))
	 (case error
	   (#.+ssl-error-want-read+
	    (input-wait stream
			(ssl-get-fd handle)
			(ssl-stream-deadline stream)))
	   (#.+ssl-error-want-write+
	    (output-wait stream
			 (ssl-get-fd handle)
			 (ssl-stream-deadline stream)))
	   (t
	    (ssl-signal-error handle func error nbytes)))))))

(declaim (inline nonblocking-ssl-funcall))
(defun nonblocking-ssl-funcall (stream handle func &rest args)
  (loop
     (let ((nbytes
	    (let ((*socket* (ssl-stream-socket stream))) ;for Lisp-BIO callbacks
	      (apply func args))))
       (when (plusp nbytes)
	 (return nbytes))
       (let ((error (ssl-get-error handle nbytes)))
	 (case error
	   ((#.+ssl-error-want-read+ #.+ssl-error-want-write+)
	    (return nbytes))
	   (t
	    (ssl-signal-error handle func error nbytes)))))))


;;; Waiting for output to be possible

#+clozure-common-lisp
(defun milliseconds-until-deadline (deadline stream)
  (let* ((now (get-internal-real-time)))
    (if (> now deadline)
	(error 'ccl::communication-deadline-expired :stream stream)
	(values
	 (round (- deadline now) (/ internal-time-units-per-second 1000))))))

#+clozure-common-lisp
(defun output-wait (stream fd deadline)
  (unless deadline
    (setf deadline (stream-deadline (ssl-stream-socket stream))))
  (let* ((timeout
	  (if deadline
	      (milliseconds-until-deadline deadline stream)
	      nil)))
    (multiple-value-bind (win timedout error)
	(ccl::process-output-wait fd timeout)
      (unless win
	(if timedout
	    (error 'ccl::communication-deadline-expired :stream stream)
	    (ccl::stream-io-error stream (- error) "write"))))))

#+sbcl
(defun output-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
	 ;; *deadline* is handled by wait-until-fd-usable automatically,
	 ;; but we need to turn a user-specified deadline into a timeout
	 (when deadline
	   (/ (- deadline (get-internal-real-time))
	      internal-time-units-per-second))))
    (sb-sys:wait-until-fd-usable fd :output timeout)))

#-(or clozure-common-lisp sbcl)
(defun output-wait (stream fd deadline)
  (declare (ignore stream fd deadline))
  ;; This situation means that the lisp set our fd to non-blocking mode,
  ;; and streams.lisp didn't know how to undo that.
  (warn "non-blocking stream encountered unexpectedly"))


;;; Waiting for input to be possible

#+clozure-common-lisp
(defun input-wait (stream fd deadline)
  (unless deadline
    (setf deadline (stream-deadline (ssl-stream-socket stream))))
  (let* ((timeout
	  (if deadline
	      (milliseconds-until-deadline deadline stream)
	      nil)))
    (multiple-value-bind (win timedout error)
	(ccl::process-input-wait fd timeout)
      (unless win
	(if timedout
	    (error 'ccl::communication-deadline-expired :stream stream)
	    (ccl::stream-io-error stream (- error) "read"))))))

#+sbcl
(defun input-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
	 ;; *deadline* is handled by wait-until-fd-usable automatically,
	 ;; but we need to turn a user-specified deadline into a timeout
	 (when deadline
	   (/ (- deadline (get-internal-real-time))
	      internal-time-units-per-second))))
    (sb-sys:wait-until-fd-usable fd :input timeout)))

#-(or clozure-common-lisp sbcl)
(defun input-wait (stream fd deadline)
  (declare (ignore stream fd deadline))
  ;; This situation means that the lisp set our fd to non-blocking mode,
  ;; and streams.lisp didn't know how to undo that.
  (warn "non-blocking stream encountered unexpectedly"))


;;; Encrypted PEM files support
;;;

;; based on http://www.openssl.org/docs/ssl/SSL_CTX_set_default_passwd_cb.html

(defvar *pem-password* ""
  "The callback registered with SSL_CTX_set_default_passwd_cb
will use this value.")

;; The callback itself
(cffi:defcallback pem-password-callback :int
    ((buf :pointer) (size :int) (rwflag :int) (unused :pointer))
  (declare (ignore rwflag unused))
  (let* ((password-str (coerce *pem-password* 'base-string))
         (tmp (cffi:foreign-string-alloc password-str)))
    (cffi:foreign-funcall "strncpy"
                          :pointer buf
                          :pointer tmp
                          :int size)
    (cffi:foreign-string-free tmp)
    (setf (cffi:mem-ref buf :char (1- size)) 0)
    (cffi:foreign-funcall "strlen" :pointer buf :int)))

;; The macro to be used by other code to provide password
;; when loading PEM file.
(defmacro with-pem-password ((password) &body body)
  `(let ((*pem-password* (or ,password "")))
         ,@body))


;;; Initialization
;;;

(defun init-prng (seed-byte-sequence)
  (let* ((length (length seed-byte-sequence))
         (buf (cffi-sys::make-shareable-byte-vector length)))
    (dotimes (i length)
      (setf (elt buf i) (elt seed-byte-sequence i)))
    (cffi-sys::with-pointer-to-vector-data (ptr buf)
      (rand-seed ptr length))))

(defun ssl-ctx-set-session-cache-mode (ctx mode)
  (ssl-ctx-ctrl ctx +SSL_CTRL_SET_SESS_CACHE_MODE+ mode (cffi:null-pointer)))

(defun SSL-set-tlsext-host-name (ctx hostname)
  (ssl-ctrl ctx 55 #|SSL_CTRL_SET_TLSEXT_HOSTNAME|# 0 #|TLSEXT_NAMETYPE_host_name|# hostname))

(defvar *locks*)
(defconstant +CRYPTO-LOCK+ 1)
(defconstant +CRYPTO-UNLOCK+ 2)
(defconstant +CRYPTO-READ+ 4)
(defconstant +CRYPTO-WRITE+ 8)

;; zzz as of early 2011, bxthreads is totally broken on SBCL wrt. explicit
;; locking of recursive locks.  with-recursive-lock works, but acquire/release
;; don't.  Hence we use non-recursize locks here (but can use a recursive
;; lock for the global lock).

(cffi:defcallback locking-callback :void
    ((mode :int)
     (n :int)
     (file :string)
     (line :int))
  (declare (ignore file line))
  ;; (assert (logtest mode (logior +CRYPTO-READ+ +CRYPTO-WRITE+)))
  (let ((lock (elt *locks* n)))
    (cond
      ((logtest mode +CRYPTO-LOCK+)
       (bt:acquire-lock lock))
      ((logtest mode +CRYPTO-UNLOCK+)
       (bt:release-lock lock))
      (t
       (error "fell through")))))

(defvar *threads* (trivial-garbage:make-weak-hash-table :weakness :key))
(defvar *thread-counter* 0)

(defparameter *global-lock*
  (bordeaux-threads:make-recursive-lock "SSL initialization"))

;; zzz BUG: On a 32-bit system and under non-trivial load, this counter
;; is likely to wrap in less than a year.
(cffi:defcallback threadid-callback :unsigned-long ()
  (bordeaux-threads:with-recursive-lock-held (*global-lock*)
    (let ((self (bt:current-thread)))
      (or (gethash self *threads*)
	  (setf (gethash self *threads*)
		(incf *thread-counter*))))))

(defvar *ssl-check-verify-p* :unspecified)

(defun initialize (&key (method 'ssl-v23-method) rand-seed)
  (setf *locks* (loop
		   repeat (crypto-num-locks)
		   collect (bt:make-lock)))
  (crypto-set-locking-callback (cffi:callback locking-callback))
  (crypto-set-id-callback (cffi:callback threadid-callback))
  (setf *bio-lisp-method* (make-bio-lisp-method))
  (ssl-load-error-strings)
  (ssl-library-init)
  (when rand-seed
    (init-prng rand-seed))
  (setf *ssl-check-verify-p* :unspecified)
  (setf *ssl-global-method* (funcall method))
  (setf *ssl-global-context* (ssl-ctx-new *ssl-global-method*))
  (ssl-ctx-set-session-cache-mode *ssl-global-context* 3)
  (ssl-ctx-set-default-passwd-cb *ssl-global-context* 
                                 (cffi:callback pem-password-callback))
  (ssl-ctx-set-tmp-rsa-callback *ssl-global-context*
                                (cffi:callback need-tmp-rsa-callback)))

(defun ensure-initialized (&key (method 'ssl-v23-method) (rand-seed nil))
  "In most cases you do *not* need to call this function, because it 
is called automatically by all other functions. The only reason to 
call it explicitly is to supply the RAND-SEED parameter. In this case
do it before calling any other functions.

Just leave the default value for the METHOD parameter.

RAND-SEED is an octet sequence to initialize OpenSSL random number generator. 
On many platforms, including Linux and Windows, it may be leaved NIL (default), 
because OpenSSL initializes the random number generator from OS specific service. 
But for example on Solaris it may be necessary to supply this value.
The minimum length required by OpenSSL is 128 bits.
See ttp://www.openssl.org/support/faq.html#USER1 for details.

Hint: do not use Common Lisp RANDOM function to generate the RAND-SEED, 
because the function usually returns predictable values."
  (bordeaux-threads:with-recursive-lock-held (*global-lock*)
    (unless (ssl-initialized-p)
      (initialize :method method :rand-seed rand-seed))
    (unless *bio-lisp-method*
      (setf *bio-lisp-method* (make-bio-lisp-method)))))

(defun use-certificate-chain-file (certificate-chain-file)
  "Loads a PEM encoded certificate chain file CERTIFICATE-CHAIN-FILE
and adds the chain to global context. The certificates must be sorted 
starting with the subject's certificate (actual client or server certificate),
followed by intermediate CA certificates if applicable, and ending at 
the highest level (root) CA. Note: the RELOAD function clears the global 
context and in particular the loaded certificate chain."
  (ensure-initialized)
  (ssl-ctx-use-certificate-chain-file *ssl-global-context* certificate-chain-file))

(defun reload ()
  (cffi:load-foreign-library 'libssl)
  (cffi:load-foreign-library 'libeay32)
  (setf *ssl-global-context* nil)
  (setf *ssl-global-method* nil)
  (setf *tmp-rsa-key-512* nil)
  (setf *tmp-rsa-key-1024* nil))
