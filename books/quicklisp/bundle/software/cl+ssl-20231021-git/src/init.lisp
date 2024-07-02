;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

;;; Global state
;;;
(defvar *ssl-global-context* nil)
(defvar *ssl-global-method* nil)

(defun ssl-initialized-p ()
  (and *ssl-global-context* *ssl-global-method*))

(defvar *tmp-rsa-key-512* nil)
(defvar *tmp-rsa-key-1024* nil)
(defvar *tmp-rsa-key-2048* nil)

(cffi:defcallback tmp-rsa-callback :pointer ((ssl :pointer) (export-p :int) (key-length :int))
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
         (buf (cffi:make-shareable-byte-vector length)))
    (dotimes (i length)
      (setf (elt buf i) (elt seed-byte-sequence i)))
    (cffi:with-pointer-to-vector-data (ptr buf)
      (rand-seed ptr length))))

(defvar *locks*)

;; zzz as of early 2011, bxthreads is totally broken on SBCL wrt. explicit
;; locking of recursive locks.  with-recursive-lock works, but acquire/release
;; don't.  Hence we use non-recursize locks here (but can use a recursive
;; lock for the global lock).

(cffi:defcallback locking-callback :void
    ((mode :int)
     (n :int)
     (file :pointer) ;; could be (file :string), but we don't use FILE, so avoid the conversion
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

(defvar *ssl-check-verify-p* :unspecified
  "DEPRECATED.
Use the (MAKE-SSL-CLIENT-STREAM .. :VERIFY ?) to enable/disable verification.
MAKE-CONTEXT also allows to enab/disable verification.")

(defun default-ssl-method ()
  (if (openssl-is-at-least 1 1)
      'tls-method
      'ssl-v23-method))

(defun initialize (&key method rand-seed)
  (when (or (openssl-is-not-even 1 1)
            ;; Old versions of LibreSSL
            ;; require this initialization
            ;; (https://github.com/cl-plus-ssl/cl-plus-ssl/pull/91),
            ;; new versions keep this API backwards
            ;; compatible so we can call it too.
            (libresslp))
    (setf *locks* (loop
                     repeat (crypto-num-locks)
                     collect (bt:make-lock)))
    (crypto-set-locking-callback (cffi:callback locking-callback))
    (crypto-set-id-callback (cffi:callback threadid-callback))
    (ssl-load-error-strings)
    (ssl-library-init)
    ;; However, for OpenSSL_add_all_digests the LibreSSL breaks
    ;; the backward compatibility by removing the function.
    ;; https://github.com/cl-plus-ssl/cl-plus-ssl/pull/134
    (unless (libresslp)
      (openssl-add-all-digests)))

  (bio-init)

  (when rand-seed
    (init-prng rand-seed))
  (setf *ssl-check-verify-p* :unspecified)
  (setf *ssl-global-method* (funcall (or method (default-ssl-method))))
  (setf *ssl-global-context* (ssl-ctx-new *ssl-global-method*))
  (unless (eql 1 (ssl-ctx-set-default-verify-paths *ssl-global-context*))
    (error "ssl-ctx-set-default-verify-paths failed."))
  (ssl-ctx-set-session-cache-mode *ssl-global-context* 3)
  (ssl-ctx-set-default-passwd-cb *ssl-global-context*
                                 (cffi:callback pem-password-callback))
  (when (or (openssl-is-not-even 1 1)
            ;; Again, even if newer LibreSSL
            ;; don't need this call, they keep
            ;; the API compatibility so we can continue
            ;; making this call.
            (libresslp))
    (ssl-ctx-set-tmp-rsa-callback *ssl-global-context*
                                  (cffi:callback tmp-rsa-callback))))

(defun ensure-initialized (&key method (rand-seed nil))
  "In most cases you do *not* need to call this function, because it
is called automatically by all other functions. The only reason to
call it explicitly is to supply the RAND-SEED parameter. In this case
do it before calling any other functions.

Keyword arguments:

    METHOD - just leave the default value.

    RAND-SEED - an octet sequence to initialize OpenSSL random
        number generator. On many platforms, including Linux and
        Windows, it may be left NIL (default), because OpenSSL
        initializes the random number generator from OS specific
        service. But, for example, on Solaris it may be necessary
        to supply this value. The minimum length required by OpenSSL
        is 128 bits.
        See http://www.openssl.org/support/faq.html#USER1 for details.

        Hint: do not use Common Lisp RANDOM function to generate
        the RAND-SEED, because the function usually returns
        predictable values.
"
  #+lispworks
  (check-cl+ssl-symbols)
  (bordeaux-threads:with-recursive-lock-held (*global-lock*)
    (unless (ssl-initialized-p)
      (initialize :method method :rand-seed rand-seed))))

(defun use-certificate-chain-file (certificate-chain-file)
  "Applies OpenSSL function SSL_CTX_use_certificate_chain_file
to the cl+ssl's global SSL_CTX object and the specified
CERTIFICATE-CHAIN-FILE.

OpenSSL requires the certificates in the file to be sorted
starting with the subject's certificate (actual client or
server certificate), followed by intermediate CA certificates
if applicable, and ending at the highest level (root) CA.

Note: the RELOAD function clears the global context and in particular
the loaded certificate chain."
  (ensure-initialized)
  (ssl-ctx-use-certificate-chain-file *ssl-global-context* certificate-chain-file))

(defun reload ()
  "If you save your application as a Lisp image,
call this function when that image is loaded,
to perform the necessary CL+SSL re-initialization
(unless your lisp implementation automatically
re-loads foreign libraries and preserves their
memory accross image reloads).

This should work fine if the location and version of the
OpenSSL shared libraries have not changed.
If they have changed, you may get errors, as users report:
https://github.com/cl-plus-ssl/cl-plus-ssl/issues/167
"
  (detect-custom-openssl-installations-if-macos)
  (unless (member :cl+ssl-foreign-libs-already-loaded
                  *features*)
    (cffi:use-foreign-library libcrypto)
    (cffi:load-foreign-library 'libssl))
  (setf *ssl-global-context* nil)
  (setf *ssl-global-method* nil)
  (setf *tmp-rsa-key-512* nil)
  (setf *tmp-rsa-key-1024* nil))
