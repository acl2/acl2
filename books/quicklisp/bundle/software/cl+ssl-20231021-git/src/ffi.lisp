;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

;;; Some lisps (CMUCL) fail when we try to define
;;; a foreign function which is absent in the loaded
;;; foreign library. CMUCL fails when the compiled .fasl
;;; file is loaded, and the failure can not be
;;; captured even by CL condition handlers, i.e.
;;; wrapping (defcfun "removed-function" ...)
;;; into (ignore-errors ...) doesn't help.
;;;
;;; See https://gitlab.common-lisp.net/cmucl/cmucl/issues/74
;;;
;;; As OpenSSL often changs API (removes / adds functions)
;;; we need to solve this problem for CMUCL.
;;;
;;; We do this on CMUCL by calling functions which exists
;;; not in all OpenSSL versions through a pointer
;;; received with cffi:foreign-symbol-pointer.
;;; So a lisp wrapper function for such foreign function
;;; looks up a pointer to the required foreign function
;;; in a hash table.

(defparameter *late-bound-foreign-function-pointers*
  (make-hash-table :test 'equal))

(defmacro defcfun-late-bound (name-and-options &body body)
  (assert (not (eq (alexandria:lastcar body)
                   '&rest))
          (body)
          "The BODY format is implemented in a limited way
comparing to CFFI:DEFCFUN - we don't support the &REST which specifies vararg
functions. Feel free to implement the support if you have a use case.")
  (assert (and (>= (length name-and-options) 2)
               (stringp (first name-and-options))
               (symbolp (second name-and-options)))
          (name-and-options)
          "Unsupported NAME-AND-OPTIONS format: ~S.
\(Of all the NAME-AND-OPTIONS variants allowed by CFFI:DEFCFUN we have only
implemented support for (FOREIGN-NAME LISP-NAME ...) where FOREIGN-NAME is a
STRING and LISP-NAME is a SYMBOL. Fell free to implement support the remaining
variants if you have use cases for them.)"
          name-and-options)

  (let ((foreign-name-str (first name-and-options))
        (lisp-name (second name-and-options))
        (docstring (when (stringp (car body)) (pop body)))
        (return-type (first body))
        (arg-names (mapcar #'first (rest body)))
        (arg-types (mapcar #'second (rest body)))
        (library (getf (cddr name-and-options) :library))
        (convention (getf (cddr name-and-options) :convention))
        (ptr-var (gensym (string 'ptr))))
    `(progn
       (setf (gethash ,foreign-name-str *late-bound-foreign-function-pointers*)
             (or (cffi:foreign-symbol-pointer ,foreign-name-str
                                              ,@(when library `(:library ',library)))
                 'foreign-symbol-not-found))
       (defun ,lisp-name (,@arg-names)
         ,@(when docstring (list docstring))
         (let ((,ptr-var (gethash ,foreign-name-str *late-bound-foreign-function-pointers*)))
           (when (null ,ptr-var)
             (error "Unexpacted state, no value in *late-bound-foreign-function-pointers* for ~A"
                    ,foreign-name-str))
           (when (eq ,ptr-var 'foreign-symbol-not-found)
             (error "The current version of OpenSSL libcrypto doesn't provide ~A"
                    ,foreign-name-str))
           (cffi:foreign-funcall-pointer ,ptr-var
                                         ,(when convention (list convention))
                                         ,@(mapcan #'list arg-types arg-names)
                                         ,return-type))))))

(defmacro defcfun-versioned ((&key since vanished) name-and-options &body body)
  (if (and (or since vanished)
           (member :cmucl *features*))
      `(defcfun-late-bound ,name-and-options ,@body)
      `(cffi:defcfun ,name-and-options ,@body)))


;;; Code for checking that we got the correct foreign symbols right.
;;; Implemented only for LispWorks for now.
(defvar *cl+ssl-ssl-foreign-function-names* nil)
(defvar *cl+ssl-crypto-foreign-function-names* nil)

#+lispworks
(defun check-cl+ssl-symbols ()
  (dolist (ssl-symbol *cl+ssl-ssl-foreign-function-names*)
    (when (fli:null-pointer-p (fli:make-pointer :symbol-name ssl-symbol :module 'libssl :errorp nil))
      (format *error-output* "cl+ssl can not locate symbol ~s in the module 'libssl~%" ssl-symbol)))
  (dolist (crypto-symbol *cl+ssl-crypto-foreign-function-names*)
    (when (fli:null-pointer-p (fli:make-pointer :symbol-name crypto-symbol :module 'libcrypto :errorp nil))
      (format *error-output* "cl+ssl can not locate symbol ~s in the module 'libcrypto~%" crypto-symbol))))

(defmacro define-ssl-function-ex ((&key since vanished) name-and-options &body body)
  `(progn
     ;; debugging
     ,@(unless (or since vanished)
         `((pushnew ,(car name-and-options)
                    *cl+ssl-ssl-foreign-function-names*
                    :test 'equal)))
     (defcfun-versioned (:since ,since :vanished ,vanished)
         ,(append name-and-options '(:library libssl))
       ,@body)))

(defmacro define-ssl-function (name-and-options &body body)
  `(define-ssl-function-ex () ,name-and-options ,@body))

(defmacro define-crypto-function-ex ((&key since vanished) name-and-options &body body)
  `(progn
     ;; debugging
     ,@(unless (or since vanished)
         `(( pushnew ,(car name-and-options)
                     *cl+ssl-crypto-foreign-function-names*
                     :test 'equal)))
     (defcfun-versioned (:since ,since :vanished ,vanished)
         ,(append name-and-options
                  #-cl+ssl-foreign-libs-already-loaded '(:library libcrypto))
       ,@body)))

(defmacro define-crypto-function (name-and-options &body body)
  `(define-crypto-function-ex () ,name-and-options ,@body))


;;; Constants
;;;
(defconstant +ssl-filetype-pem+ 1)
(defconstant +ssl-filetype-asn1+ 2)
(defconstant +ssl-filetype-default+ 3)

(defconstant +SSL-CTRL-OPTIONS+ 32)
(defconstant +SSL_CTRL_SET_SESS_CACHE_MODE+ 44)
(defconstant +SSL_CTRL_MODE+ 33)

(defconstant +SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER+ 2)

(defconstant +RSA_F4+ #x10001)

(defconstant +SSL-SESS-CACHE-OFF+ #x0000
  "No session caching for client or server takes place.")
(defconstant +SSL-SESS-CACHE-CLIENT+ #x0001
  "Client sessions are added to the session cache.
As there is no reliable way for the OpenSSL library to know whether a session should be reused
or which session to choose (due to the abstract BIO layer the SSL engine does not have details
about the connection), the application must select the session to be reused by using the
SSL-SET-SESSION function. This option is not activated by default.")
(defconstant +SSL-SESS-CACHE-SERVER+ #x0002
  "Server sessions are added to the session cache.
When a client proposes a session to be reused, the server looks for the corresponding session
in (first) the internal session cache (unless +SSL-SESS-CACHE-NO-INTERNAL-LOOKUP+ is set), then
(second) in the external cache if available. If the session is found, the server will try to
reuse the session. This is the default.")
(defconstant +SSL-SESS-CACHE-BOTH+ (logior +SSL-SESS-CACHE-CLIENT+ +SSL-SESS-CACHE-SERVER+)
  "Enable both +SSL-SESS-CACHE-CLIENT+ and +SSL-SESS-CACHE-SERVER+ at the same time.")
(defconstant +SSL-SESS-CACHE-NO-AUTO-CLEAR+ #x0080
  "Normally the session cache is checked for expired sessions every 255 connections using the
SSL-CTX-FLUSH-SESSIONS function. Since this may lead to a delay which cannot be controlled,
the automatic flushing may be disabled and SSL-CTX-FLUSH-SESSIONS can be called explicitly
by the application.")
(defconstant +SSL-SESS-CACHE-NO-INTERNAL-LOOKUP+ #x0100
  "By setting this flag, session-resume operations in an SSL/TLS server will not automatically
look up sessions in the internal cache, even if sessions are automatically stored there.
If external session caching callbacks are in use, this flag guarantees that all lookups are
directed to the external cache. As automatic lookup only applies for SSL/TLS servers, the flag
has no effect on clients.")
(defconstant +SSL-SESS-CACHE-NO-INTERNAL-STORE+ #x0200
  "Depending on the presence of +SSL-SESS-CACHE-CLIENT+ and/or +SSL-SESS-CACHE-SERVER+, sessions
negotiated in an SSL/TLS handshake may be cached for possible reuse. Normally a new session is
added to the internal cache as well as any external session caching (callback) that is configured
for the SSL_CTX. This flag will prevent sessions being stored in the internal cache (though the
application can add them manually using SSL-CTX-ADD-SESSION). Note: in any SSL/TLS servers where
external caching is configured, any successful session lookups in the external cache (ie. for
session-resume requests) would normally be copied into the local cache before processing continues
- this flag prevents these additions to the internal cache as well.")
(defconstant +SSL-SESS-CACHE-NO-INTERNAL+ (logior +SSL-SESS-CACHE-NO-INTERNAL-LOOKUP+ +SSL-SESS-CACHE-NO-INTERNAL-STORE+)
  "Enable both +SSL-SESS-CACHE-NO-INTERNAL-LOOKUP+ and +SSL-SESS-CACHE-NO-INTERNAL-STORE+ at the same time.")

(defconstant +SSL-VERIFY-NONE+ #x00)
(defconstant +SSL-VERIFY-PEER+ #x01)
(defconstant +SSL-VERIFY-FAIL-IF-NO-PEER-CERT+ #x02)
(defconstant +SSL-VERIFY-CLIENT-ONCE+ #x04)

(defconstant +x509-v-ok+ 0)

(defconstant +SSL-OP-ALL+ #x80000BFF)

(defconstant +SSL-OP-IGNORE-UNEXPECTED-EOF+ #b10000000)

(defconstant +SSL-OP-NO-SSLv2+   #x01000000)
(defconstant +SSL-OP-NO-SSLv3+   #x02000000)
(defconstant +SSL-OP-NO-TLSv1+   #x04000000)
(defconstant +SSL-OP-NO-TLSv1-2+ #x08000000)
(defconstant +SSL-OP-NO-TLSv1-1+ #x10000000)

(defconstant +SSL-CTRL-SET-MIN-PROTO-VERSION+ 123)
(defconstant +SSL-CTRL-SET-MAX-PROTO-VERSION+ 124)

(defconstant +SSL3-VERSION+ #x0300)
(defconstant +TLS1-VERSION+ #x0301)
(defconstant +TLS1-1-VERSION+ #x0302)
(defconstant +TLS1-2-VERSION+ #x0303)
(defconstant +TLS1-3-VERSION+ #x0304)
(defconstant +DTLS1-VERSION+ #xFEFF)
(defconstant +DTLS1-2-VERSION+ #xFEFD)

;;; Function definitions
;;;

(cffi:defcfun (#-windows "close" #+windows "closesocket" close-socket)
    :int
  (socket :int))

(declaim (inline ssl-write ssl-read ssl-connect ssl-accept))

(cffi:defctype ssl-method :pointer)
(cffi:defctype ssl-ctx :pointer)
(cffi:defctype ssl-pointer :pointer)


(define-crypto-function-ex (:vanished "1.1.0") ("SSLeay" ssl-eay)
        :long)

(define-crypto-function-ex (:since "1.1.0") ("OpenSSL_version_num" openssl-version-num)
        :long)

(defun compat-openssl-version ()
  (or (ignore-errors (openssl-version-num))
      (ignore-errors (ssl-eay))
      (error "No OpenSSL version number could be determined, both SSLeay and OpenSSL_version_num failed.")))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter +openssl-version-status-strings+
    '("dev"
      "beta 1" "beta 2" "beta 3" "beta 4" "beta 5" "beta 6" "beta 7"
      "beta 8" "beta 9" "beta 10" "beta 11" "beta 12" "beta 13" "beta 14"
      "release")))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter +openssl-version-patch-characters+
    '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z)))

(deftype openssl-version-patch ()
  `(or (integer 0 #xff)
       (member ,@+openssl-version-patch-characters+)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun openssl-version-status-p (status)
    (or (typep status '(integer 0 #xf))
        (member status +openssl-version-status-strings+ :test #'string=))))

(deftype openssl-version-status ()
  '(satisfies openssl-version-status-p))

(defun encode-openssl-version-impl (major minor &optional (fix 0) (patch 0) (status "release"))
  (check-type major (integer 0 3))
  (check-type minor (integer 0 #xff))
  (check-type fix (integer 0 #xff))
  (check-type patch openssl-version-patch)
  (check-type status openssl-version-status)
  (let ((patch-int (if (integerp patch)
                       patch
                       ;; a = 1, b = 2, and so on:
                       (1+ (position patch +openssl-version-patch-characters+))))
        (status-int (if (integerp status)
                        status
                        ;; dev = 0, beta 1 = 1, beta 2 = 2, ..., beta 14 = 14, release = 15
                        (position status +openssl-version-status-strings+ :test #'string=))))
    (logior (ash major 28)
            (ash minor 20)
            (ash fix 12)
            (ash patch-int 4)
            status-int)))

(assert (= (encode-openssl-version-impl 0 9 6 0 "dev")
           #x00906000))
(assert (= (encode-openssl-version-impl 0 9 6 #\b "beta 3")
           #x00906023))
(assert (= (encode-openssl-version-impl 0 9 6 #\e "release")
           #x0090605f))
(assert (= (encode-openssl-version-impl 0 9 6 #\e)
           #x0090605f))
(assert (= (encode-openssl-version-impl 1 0 0 #\s)
           #x1000013f))

(defun encode-openssl-version (major minor &optional (patch-or-fix 0))
  "Builds a version number to compare with the version returned by OpenSSL.

The integer representation of OpenSSL version has bit fields
for major, minor, fix, patch and status varlues.

Versions before OpenSSL 3 have user readable representations
for all those fields. For example, 0.9.6b beta 3. Here
0 - major, 9 - minor, 6 - fix, b - patch, beta 3 - status.
https://www.openssl.org/docs/man1.1.1/man3/OPENSSL_VERSION_NUMBER.html

Since OpenSSL 3, the third number in user readable repersentation
is patch. The fix and status are not used and have 0 in the corresponding
bit fields.
https://www.openssl.org/docs/man3.0/man3/OPENSSL_VERSION_NUMBER.html
https://www.openssl.org/policies/general/versioning-policy.html

As usually with OpenSSL docs, if the above links disappear becuase
those OpenSSL versions are out of maintenance, use the Wayback Machine.

Note: the _really_ old formats (<= 0.9.4) are not supported."
  (if (>= major 3)
      (encode-openssl-version-impl major minor 0 patch-or-fix)
      (encode-openssl-version-impl major minor patch-or-fix)))

(defun openssl-is-at-least (major minor &optional (patch-or-fix 0))
  (>= (compat-openssl-version)
      (encode-openssl-version major minor patch-or-fix)))

(defun openssl-is-not-even (major minor &optional (patch-or-fix 0))
  (< (compat-openssl-version)
     (encode-openssl-version major minor patch-or-fix)))

(defun libresslp ()
  ;; LibreSSL can be distinguished by
  ;; OpenSSL_version_num() always returning 0x020000000,
  ;; where 2 is the major version number.
  ;; http://man.openbsd.org/OPENSSL_VERSION_NUMBER.3
  ;; And OpenSSL will never use the major version 2:
  ;; "This document outlines the design of OpenSSL 3.0, the next version of OpenSSL after 1.1.1"
  ;; https://www.openssl.org/docs/OpenSSL300Design.html
  (= #x20000000 (compat-openssl-version)))

(define-ssl-function ("SSL_get_version" ssl-get-version)
    :string
  (ssl ssl-pointer))
(define-ssl-function-ex (:vanished "1.1.0") ("SSL_load_error_strings" ssl-load-error-strings)
    :void)
(define-ssl-function-ex (:vanished "1.1.0") ("SSL_library_init" ssl-library-init)
    :int)

(define-ssl-function-ex (:vanished "1.1.0")
    ("OpenSSL_add_all_digests" openssl-add-all-digests)
  :void)

;;
;; We don't refer SSLv2_client_method as the default
;; builds of OpenSSL do not have it, due to insecurity
;; of the SSL v2 protocol (see https://www.openssl.org/docs/ssl/SSL_CTX_new.html
;; and https://github.com/cl-plus-ssl/cl-plus-ssl/issues/6)
;;
;; (define-ssl-function ("SSLv2_client_method" ssl-v2-client-method)
;;     ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv23_client_method" ssl-v23-client-method)
    ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv23_server_method" ssl-v23-server-method)
    ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv23_method" ssl-v23-method)
    ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv3_client_method" ssl-v3-client-method)
    ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv3_server_method" ssl-v3-server-method)
    ssl-method)
(define-ssl-function-ex (:vanished "1.1.0") ("SSLv3_method" ssl-v3-method)
    ssl-method)
(define-ssl-function ("TLSv1_client_method" ssl-TLSv1-client-method)
    ssl-method)
(define-ssl-function ("TLSv1_server_method" ssl-TLSv1-server-method)
    ssl-method)
(define-ssl-function ("TLSv1_method" ssl-TLSv1-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_1_client_method" ssl-TLSv1-1-client-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_1_server_method" ssl-TLSv1-1-server-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_1_method" ssl-TLSv1-1-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_2_client_method" ssl-TLSv1-2-client-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_2_server_method" ssl-TLSv1-2-server-method)
    ssl-method)
(define-ssl-function-ex (:since "1.0.2") ("TLSv1_2_method" ssl-TLSv1-2-method)
    ssl-method)
(define-ssl-function-ex (:since "1.1.0") ("TLS_method" tls-method)
    ssl-method)

(define-ssl-function ("SSL_CTX_new" ssl-ctx-new)
    ssl-ctx
  (method ssl-method))
(define-ssl-function ("SSL_new" ssl-new)
    ssl-pointer
  (ctx ssl-ctx))
(define-ssl-function ("SSL_get_fd" ssl-get-fd)
    :int
  (ssl ssl-pointer))
(define-ssl-function ("SSL_set_fd" ssl-set-fd)
    :int
  (ssl ssl-pointer)
  (fd :int))
(define-ssl-function ("SSL_set_bio" ssl-set-bio)
    :void
  (ssl ssl-pointer)
  (rbio :pointer)
  (wbio :pointer))
(define-ssl-function ("SSL_get_error" ssl-get-error)
    :int
  (ssl ssl-pointer)
  (ret :int))
(define-ssl-function ("SSL_set_connect_state" ssl-set-connect-state)
    :void
  (ssl ssl-pointer))
(define-ssl-function ("SSL_set_accept_state" ssl-set-accept-state)
    :void
  (ssl ssl-pointer))
(define-ssl-function ("SSL_connect" ssl-connect)
    :int
  (ssl ssl-pointer))
(define-ssl-function ("SSL_accept" ssl-accept)
    :int
  (ssl ssl-pointer))
(define-ssl-function ("SSL_write" ssl-write)
    :int
  (ssl ssl-pointer)
  (buf :pointer)
  (num :int))
(define-ssl-function ("SSL_read" ssl-read)
    :int
  (ssl ssl-pointer)
  (buf :pointer)
  (num :int))
(define-ssl-function ("SSL_shutdown" ssl-shutdown)
    :int
  (ssl ssl-pointer))
(define-ssl-function ("SSL_free" ssl-free)
    :void
  (ssl ssl-pointer))
(define-ssl-function ("SSL_CTX_free" ssl-ctx-free)
    :void
  (ctx ssl-ctx))
(define-ssl-function-ex (:since "1.0")  ("SSL_set_alpn_protos" ssl-set-alpn-protos)
    :int
  (SSL :pointer)
  (text :string)
  (len :int))
(define-ssl-function-ex (:since "1.0") ("SSL_get0_alpn_selected" ssl-get0-alpn-selected)
    :void
  (SSL :pointer)
  (text (:pointer :string))
  (len (:pointer :int)))
(define-crypto-function ("BIO_ctrl" bio-set-fd)
    :long
  (bio :pointer)
  (cmd :int)
  (larg :long)
  (parg :pointer))
(define-crypto-function ("BIO_new_socket" bio-new-socket)
    :pointer
  (fd :int)
  (close-flag :int))
(define-crypto-function ("BIO_new" bio-new)
    :pointer
  (method :pointer))
(define-crypto-function ("BIO_free" bio-free)
    :pointer
  (method :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_get_new_index" bio-new-index)
  :int)

(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_new" bio-meth-new)
    :pointer
  (type :int)
  (name :string))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_puts" bio-set-puts)
  :int
  (meth :pointer)
  (puts :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_write" bio-set-write)
  :int
  (meth :pointer)
  (puts :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_read" bio-set-read)
  :int
  (meth :pointer)
  (read :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_gets" bio-set-gets)
  :int
  (meth :pointer)
  (read :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_create" bio-set-create)
  :int
  (meth :pointer)
  (read :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_destroy" bio-set-destroy)
  :int
  (meth :pointer)
  (read :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_meth_set_ctrl" bio-set-ctrl)
  :int
  (meth :pointer)
  (read :pointer))
(define-crypto-function-ex (:since "1.1.0") ("BIO_set_init" bio-set-init)
  :int
  (meth :pointer)
  (value :int))
(define-crypto-function-ex (:since "1.1.0") ("BIO_set_flags" bio-set-flags)
  :int
  (meth :pointer)
  (value :int))
(define-crypto-function-ex (:since "1.1.0") ("BIO_clear_flags" bio-clear-flags)
  :int
  (meth :pointer)
  (value :int))
(define-crypto-function-ex (:since "1.1.0") ("BIO_test_flags" bio-test-flags)
  :int
  (meth :pointer)
  (value :int))

(define-crypto-function ("ERR_get_error" err-get-error)
    :unsigned-long)
(define-crypto-function ("ERR_error_string" err-error-string)
    :string
  (e :unsigned-long)
  (buf :pointer))
(define-crypto-function-ex (:vanished "3.0.0") ("ERR_put_error" err-put-error)
  :void
  (lib :int)
  (func :int)
  (reason :int)
  ;; The file is :pointer instead of :string, becasue the file
  ;; name should not be dalocated after the function call
  ;; returns - that must be a long living char array.
  (file :pointer)
  (line :int))

(defconstant +err_lib_none+ 1)
(defconstant +err_r_fatal+ 64)
(defconstant +err_r_internal_error+ (logior 4 +err_r_fatal+))

(define-crypto-function-ex (:since "3.0.0") ("ERR_new" err-new)
  :void)

(define-crypto-function-ex (:since "3.0.0") ("ERR_set_debug" err-set-debug)
  :void
  (file :string)
  (line :int)
  (func :string))

#-cffi-sys::no-foreign-funcall ; vararg functions require foreign-funcall
(define-crypto-function-ex (:since "3.0.0") ("ERR_set_error" err-set-error)
  :void
  (lib :int)
  (reason :int)
  (fmt :string)
  &rest)

;; Is that a new function in 1.0.2 or existed forever?
(define-crypto-function-ex (:since "1.0.2")
    ("ERR_get_next_error_library" err-get-next-error-library)
  :int)

#-cffi-sys::no-foreign-funcall ; vararg functions require foreign-funcall
(define-crypto-function ("ERR_add_error_data" err-add-error-data)
  :void
  (num :int)
  &rest)

;; Is that a new function in 3.0.0 or existed before?
(define-crypto-function-ex (:since "3.0.0") ("ERR_add_error_txt" err-add-error-txt)
  :void
  (sep :string)
  (txt :string))

(define-crypto-function ("ERR_print_errors" err-print-errors)
  :void
  (bio :pointer))

(define-ssl-function ("SSL_set_cipher_list" ssl-set-cipher-list)
    :int
  (ssl ssl-pointer)
  (str :string))
(define-ssl-function-ex (:since "1.1.1") ("SSL_set_ciphersuites" ssl-set-ciphersuites)
    :int
  (ssl ssl-pointer)
  (str :string))

(define-ssl-function ("SSL_use_RSAPrivateKey_file" ssl-use-rsa-privatekey-file)
    :int
  (ssl ssl-pointer)
  (str :string)
  ;; either +ssl-filetype-pem+ or +ssl-filetype-asn1+
  (type :int))
(define-ssl-function
    ("SSL_CTX_use_RSAPrivateKey_file" ssl-ctx-use-rsa-privatekey-file)
    :int
  (ctx ssl-ctx)
  (type :int))
(define-ssl-function ("SSL_use_PrivateKey_file" ssl-use-privatekey-file)
  :int
  (ssl ssl-pointer)
  (str :string)
  ;; either +ssl-filetype-pem+ or +ssl-filetype-asn1+
  (type :int))
(define-ssl-function
    ("SSL_CTX_use_PrivateKey_file" ssl-ctx-use-privatekey-file)
  :int
  (ctx ssl-ctx)
  (file :string)
  (type :int))
(define-ssl-function ("SSL_use_certificate_file" ssl-use-certificate-file)
    :int
  (ssl ssl-pointer)
  (str :string)
  (type :int))

(define-ssl-function ("SSL_CTX_ctrl" ssl-ctx-ctrl)
    :long
  (ctx ssl-ctx)
  (cmd :int)
  ;; Despite declared as long in the original OpenSSL headers,
  ;; passing to larg for example 2181041151 which is the result of
  ;;     (logior cl+ssl::+SSL-OP-ALL+
  ;;             cl+ssl::+SSL-OP-NO-SSLv2+
  ;;             cl+ssl::+SSL-OP-NO-SSLv3+)
  ;; causes CFFI on 32 bit platforms to signal an error
  ;; "The value 2181041151 is not of the expected type (SIGNED-BYTE 32)"
  ;; The problem is that 2181041151 requires 32 bits by itself and
  ;; there is no place left for the sign bit.
  ;; In C the compiler silently coerces unsigned to signed,
  ;; but CFFI raises this error.
  ;; Therefore we use :UNSIGNED-LONG for LARG.
  (larg :unsigned-long)
  (parg :pointer))

(define-ssl-function ("SSL_ctrl" ssl-ctrl)
    :long
  (ssl :pointer)
  (cmd :int)
  (larg :long)
  (parg :pointer))

#+new-openssl
(define-ssl-function ("SSL_CTX_set_options" ssl-ctx-set-options)
                 :long
               (ctx :pointer)
               (options :long))
#-new-openssl
(defun ssl-ctx-set-options (ctx options)
  (ssl-ctx-ctrl ctx +SSL-CTRL-OPTIONS+ options (cffi:null-pointer)))
(defun ssl-ctx-set-min-proto-version (ctx version)
  (ssl-ctx-ctrl ctx +SSL-CTRL-SET-MIN-PROTO-VERSION+ version (cffi:null-pointer)))
(defun ssl-ctx-set-max-proto-version (ctx version)
  (ssl-ctx-ctrl ctx +SSL-CTRL-SET-MAX-PROTO-VERSION+ version (cffi:null-pointer)))
(define-ssl-function ("SSL_CTX_set_cipher_list" ssl-ctx-set-cipher-list)
    :int
  (ctx :pointer)
  (ciphers :string))
(define-ssl-function-ex (:since "1.1.1") ("SSL_CTX_set_ciphersuites" ssl-ctx-set-ciphersuites)
    :int
  (ctx :pointer)
  (ciphersuites :string))
(define-ssl-function ("SSL_CTX_use_certificate_chain_file" ssl-ctx-use-certificate-chain-file)
    :int
  (ctx ssl-ctx)
  (str :string))
(define-ssl-function ("SSL_CTX_load_verify_locations" ssl-ctx-load-verify-locations)
    :int
  (ctx ssl-ctx)
  (CAfile :string)
  (CApath :string))
(define-ssl-function ("SSL_CTX_set_client_CA_list" ssl-ctx-set-client-ca-list)
    :void
  (ctx ssl-ctx)
  (list ssl-pointer))
(define-ssl-function ("SSL_load_client_CA_file" ssl-load-client-ca-file)
    ssl-pointer
  (file :string))

(define-ssl-function ("SSL_CTX_set_default_passwd_cb" ssl-ctx-set-default-passwd-cb)
    :void
  (ctx ssl-ctx)
  (pem_passwd_cb :pointer))

(define-crypto-function-ex (:vanished "1.1.0") ("CRYPTO_num_locks" crypto-num-locks) :int)
(define-crypto-function-ex (:vanished "1.1.0") ("CRYPTO_set_locking_callback" crypto-set-locking-callback)
    :void
  (fun :pointer))
(define-crypto-function-ex (:vanished "1.1.0") ("CRYPTO_set_id_callback" crypto-set-id-callback)
    :void
  (fun :pointer))

(define-crypto-function ("RAND_seed" rand-seed)
    :void
  (buf :pointer)
  (num :int))
(define-crypto-function ("RAND_bytes" rand-bytes)
    :int
  (buf :pointer)
  (num :int))

(define-ssl-function ("SSL_CTX_set_verify_depth" ssl-ctx-set-verify-depth)
    :void
  (ctx :pointer)
  (depth :int))

(define-ssl-function ("SSL_CTX_set_verify" ssl-ctx-set-verify)
    :void
  (ctx :pointer)
  (mode :int)
  (verify-callback :pointer))

(define-ssl-function ("SSL_get_verify_result" ssl-get-verify-result)
    :long
  (ssl ssl-pointer))

(define-ssl-function-ex (:vanished "3.0.0") ("SSL_get_peer_certificate" ssl-get-peer-certificate)
    :pointer
  (ssl ssl-pointer))

(define-ssl-function-ex (:since "3.0.0") ("SSL_get1_peer_certificate" ssl-get1-peer-certificate)
    :pointer
  (ssl ssl-pointer))

(defun compat-ssl-get1-peer-certificate (handle)
  (funcall (if (openssl-is-at-least 3 0 0)
               'ssl-get1-peer-certificate
               'ssl-get-peer-certificate)
           handle))

;;; X509 & ASN1
(define-crypto-function ("X509_free" x509-free)
    :void
  (x509 :pointer))

(define-crypto-function ("X509_NAME_oneline" x509-name-oneline)
    :pointer
  (x509-name :pointer)
  (buf :pointer)
  (size :int))

(define-crypto-function ("X509_NAME_get_index_by_NID" x509-name-get-index-by-nid)
    :int
  (name :pointer)
  (nid :int)
  (lastpos :int))

(define-crypto-function ("X509_NAME_get_entry" x509-name-get-entry)
    :pointer
  (name :pointer)
  (log :int))

(define-crypto-function ("X509_NAME_ENTRY_get_data" x509-name-entry-get-data)
    :pointer
  (name-entry :pointer))

(define-crypto-function ("X509_get_issuer_name" x509-get-issuer-name)
    :pointer                            ; *X509_NAME
  (x509 :pointer))

(define-crypto-function ("X509_get_subject_name" x509-get-subject-name)
    :pointer                            ; *X509_NAME
  (x509 :pointer))

(define-crypto-function-ex (:since "1.1.0") ("X509_get0_notBefore" x509-get0-not-before)
    :pointer                            ; *ASN1_TIME
  (x509 :pointer))

(define-crypto-function-ex (:since "1.1.0") ("X509_get0_notAfter" x509-get0-not-after)
    :pointer                            ; *ASN1_TIME
  (x509 :pointer))

(define-crypto-function ("X509_get_ext_d2i" x509-get-ext-d2i)
    :pointer
  (cert :pointer)
  (nid :int)
  (crit :pointer)
  (idx :pointer))

(define-crypto-function ("X509_STORE_CTX_get_error" x509-store-ctx-get-error)
    :int
  (ctx :pointer))

(define-crypto-function ("d2i_X509" d2i-x509)
    :pointer
  (*px :pointer)
  (in :pointer)
  (len :int))

(define-crypto-function ("X509_digest" x509-digest)
    :int
  (cert :pointer)
  (type :pointer)
  (buf :pointer)
  (*len :pointer))

(define-crypto-function ("PEM_write_bio_X509" pem-write-x509)
  :int
  (bio :pointer)
  (x509 :pointer))

(define-crypto-function ("PEM_read_bio_X509" pem-read-x509)
  :pointer
  ;; all args are :pointers in fact, but they are NULL anyway
  (bio :pointer)
  (x509 :int)
  (callback :int)
  (passphrase :int))

;;; EVP

(define-crypto-function ("EVP_get_digestbyname" evp-get-digest-by-name)
    :pointer
  (name :string))

(define-crypto-function-ex (:vanished "3.0.0") ("EVP_MD_size" evp-md-size)
    :int
  (evp :pointer))

(define-crypto-function-ex (:since "3.0.0") ("EVP_MD_get_size" evp-md-get-size)
    :int
  (evp :pointer))


;; GENERAL-NAME types
(defconstant +GEN-OTHERNAME+  0)
(defconstant +GEN-EMAIL+  1)
(defconstant +GEN-DNS+    2)
(defconstant +GEN-X400+ 3)
(defconstant +GEN-DIRNAME+  4)
(defconstant +GEN-EDIPARTY+ 5)
(defconstant +GEN-URI+    6)
(defconstant +GEN-IPADD+  7)
(defconstant +GEN-RID+    8)

(defconstant +v-asn1-octet-string+ 4)
(defconstant +v-asn1-utf8string+ 12)
(defconstant +v-asn1-printablestring+ 19)
(defconstant +v-asn1-teletexstring+ 20)
(defconstant +v-asn1-iastring+ 22)
(defconstant +v-asn1-universalstring+ 28)
(defconstant +v-asn1-bmpstring+ 30)


(defconstant +NID-subject-alt-name+ 85)
(defconstant +NID-commonName+   13)

(cffi:defcstruct general-name
  (type :int)
  (data :pointer))

(define-crypto-function-ex (:vanished "1.1.0") ("sk_value" sk-value)
    :pointer
  (stack :pointer)
  (index :int))

(define-crypto-function-ex (:vanished "1.1.0") ("sk_num" sk-num)
    :int
  (stack :pointer))

(define-crypto-function-ex (:since "1.1.0") ("OPENSSL_sk_value" openssl-sk-value)
    :pointer
  (stack :pointer)
  (index :int))

(define-crypto-function-ex (:since "1.1.0") ("OPENSSL_sk_num" openssl-sk-num)
    :int
  (stack :pointer))

(declaim (ftype (function (cffi:foreign-pointer fixnum) cffi:foreign-pointer) sk-general-name-value))
(defun sk-general-name-value (names index)
  (if (and (not (libresslp))
           (openssl-is-at-least 1 1))
      (openssl-sk-value names index)
      (sk-value names index)))

(declaim (ftype (function (cffi:foreign-pointer) fixnum) sk-general-name-num))
(defun sk-general-name-num (names)
  (if (and (not (libresslp))
           (openssl-is-at-least 1 1))
      (openssl-sk-num names)
      (sk-num names)))

(define-crypto-function ("GENERAL_NAMES_free" general-names-free)
    :void
  (general-names :pointer))

(define-crypto-function ("ASN1_STRING_data" asn1-string-data)
    :pointer
  (asn1-string :pointer))

(define-crypto-function ("ASN1_STRING_length" asn1-string-length)
    :int
  (asn1-string :pointer))

(define-crypto-function ("ASN1_STRING_type" asn1-string-type)
    :int
  (asn1-string :pointer))

(cffi:defcstruct asn1_string_st
  (length :int)
  (type :int)
  (data :pointer)
  (flags :long))

(define-crypto-function ("ASN1_TIME_check" asn1-time-check)
    :int
  (asn1-string :pointer))

(define-crypto-function ("ASN1_UTCTIME_check" asn1-utctime-check)
    :int
  (asn1-string :pointer))

;; X509 & ASN1 - end

(define-ssl-function ("SSL_CTX_set_default_verify_paths" ssl-ctx-set-default-verify-paths)
    :int
  (ctx :pointer))

(define-ssl-function-ex (:since "1.1.0") ("SSL_CTX_set_default_verify_dir" ssl-ctx-set-default-verify-dir)
    :int
  (ctx :pointer))

(define-ssl-function-ex (:since "1.1.0") ("SSL_CTX_set_default_verify_file" ssl-ctx-set-default-verify-file)
    :int
  (ctx :pointer))

(define-crypto-function ("RSA_generate_key" rsa-generate-key)
    :pointer
  (num :int)
  (e :unsigned-long)
  (callback :pointer)
  (opt :pointer))

(define-crypto-function ("RSA_free" rsa-free)
    :void
  (rsa :pointer))

(define-ssl-function-ex (:vanished "1.1.0") ("SSL_CTX_set_tmp_rsa_callback" ssl-ctx-set-tmp-rsa-callback)
    :pointer
  (ctx :pointer)
  (callback :pointer))

(defun ssl-ctx-set-session-cache-mode (ctx mode)
  (ssl-ctx-ctrl ctx +SSL_CTRL_SET_SESS_CACHE_MODE+ mode (cffi:null-pointer)))

(defun ssl-set-tlsext-host-name (ctx hostname)
  (ssl-ctrl ctx 55 #|SSL_CTRL_SET_TLSEXT_HOSTNAME|# 0 #|TLSEXT_NAMETYPE_host_name|# hostname))

(defconstant +CRYPTO-LOCK+ 1)
(defconstant +CRYPTO-UNLOCK+ 2)
(defconstant +CRYPTO-READ+ 4)
(defconstant +CRYPTO-WRITE+ 8)

