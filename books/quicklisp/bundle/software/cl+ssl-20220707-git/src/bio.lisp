;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2005  David Lichteblau
;;; Copyright (C) 2021  Tomas Zellerin (zellerin@gmail.com, https://github.com/zellerin)
;;; Copyright (C) 2021  Anton Vodonosov (avodonosov@yandex.ru, https://github.com/avodonosov)
;;;
;;; See LICENSE for details.

#+xcvb (module (:depends-on ("package")))

(in-package cl+ssl)

(defconstant +BIO_TYPE_SOURCE_SINK+ #x0400)
(defconstant +BIO_TYPE_DESCRIPTOR+ #x0100)

(defconstant +bio-type-socket+ (logior 5
                                       +BIO_TYPE_SOURCE_SINK+
                                       +BIO_TYPE_DESCRIPTOR+))
(defconstant +BIO_FLAGS_READ+ 1)
(defconstant +BIO_FLAGS_WRITE+ 2)
(defconstant +BIO_FLAGS_IO_SPECIAL+ 4)
(defconstant +BIO_FLAGS_RWS+ (logior +BIO_FLAGS_READ+
                                     +BIO_FLAGS_WRITE+
                                     +BIO_FLAGS_IO_SPECIAL+))
(defconstant +BIO_FLAGS_SHOULD_RETRY+ 8)
(defconstant +BIO_CTRL_FLUSH+ 11)

(cffi:defcstruct bio-method
  (type :int)
  (name :pointer)
  (bwrite :pointer)
  (bread :pointer)
  (bputs :pointer)
  (bgets :pointer)
  (ctrl :pointer)
  (create :pointer)
  (destroy :pointer)
  (callback-ctrl :pointer))

(cffi:defcstruct bio
  (method :pointer)
  (callback :pointer)
  (cb-arg :pointer)
  (init :int)
  (shutdown :int)
  (flags :int)
  (retry-reason :int)
  (num :int)
  (ptr :pointer)
  (next-bio :pointer)
  (prev-bio :pointer)
  (references :int)
  (num-read :unsigned-long)
  (num-write :unsigned-long)
  (crypto-ex-data-stack :pointer)
  (crypto-ex-data-dummy :int))

(defun lisp-bio-type ()
  (or (ignore-errors
        (logior (bio-new-index) +BIO_TYPE_SOURCE_SINK+))
      ;; Old OpenSSL and LibreSSL do not nave BIO_get_new_index,
      ;; in this case fallback to BIO_TYPE_SOCKET.
      ;; fixmy: Maybe that's wrong, but presumably still better than some
      ;; random value here.
      +bio-type-socket+))

(defun make-bio-lisp-method-slots ()
  (let ((m (cffi:foreign-alloc '(:struct bio-method))))
    (setf (cffi:foreign-slot-value m '(:struct bio-method) 'type)
          *lisp-bio-type*)
    (macrolet ((slot (name)
                 `(cffi:foreign-slot-value m '(:struct bio-method) ,name)))
      (setf (slot 'name) (cffi:foreign-string-alloc "lisp"))
      (setf (slot 'bwrite) (cffi:callback lisp-write))
      (setf (slot 'bread) (cffi:callback lisp-read))
      (setf (slot 'bputs) (cffi:callback lisp-puts))
      (setf (slot 'bgets) (cffi:callback lisp-gets))
      (setf (slot 'ctrl) (cffi:callback lisp-ctrl))
      (setf (slot 'create) (cffi:callback lisp-create-slots))
      (setf (slot 'destroy) (cffi:callback lisp-destroy-slots))
      (setf (slot 'callback-ctrl) (cffi:null-pointer)))
    m))

(defun make-bio-lisp-method-opaque ()
  (let ((m (bio-meth-new *lisp-bio-type* "lisp")))
    (bio-set-puts m (cffi:callback lisp-puts))
    (bio-set-write m (cffi:callback lisp-write))
    (bio-set-read m (cffi:callback lisp-read))
    (bio-set-gets m (cffi:callback lisp-gets))
    (bio-set-create m (cffi:callback lisp-create-opaque))
    (bio-set-destroy m (cffi:callback lisp-destroy-opaque))
    (bio-set-ctrl m (cffi:callback lisp-ctrl))
    m))

(defun make-bio-lisp-method ()
  (if *bio-is-opaque*
      (make-bio-lisp-method-opaque)
      (make-bio-lisp-method-slots)))

(defun bio-new-lisp ()
  (unless *bio-lisp-method* (initialize))
  (let ((new (bio-new *bio-lisp-method*)))
    (if (or (null new) (cffi:null-pointer-p new))
        (error "Cannot create bio method: ~a"
               (cl+ssl::err-error-string (cl+ssl::err-get-error) (cffi:null-pointer)))
        new)))

(defun clear-retry-flags-slots (bio)
  (setf (cffi:foreign-slot-value bio '(:struct bio) 'flags)
        (logandc2 (cffi:foreign-slot-value bio '(:struct bio) 'flags)
                  (logior +BIO_FLAGS_RWS+
                          +BIO_FLAGS_SHOULD_RETRY+))))

(defun clear-retry-flags-opaque (bio)
  (bio-clear-flags bio
                   (logior +BIO_FLAGS_RWS+
                           +BIO_FLAGS_SHOULD_RETRY+)))

(defun clear-retry-flags (bio)
  (if *bio-is-opaque*
      (clear-retry-flags-opaque bio)
      (clear-retry-flags-slots bio)))

(defun set-retry-read-opaque (bio)
  (setf (cffi:foreign-slot-value bio '(:struct bio) 'flags)
        (logior (cffi:foreign-slot-value bio '(:struct bio) 'flags)
                +BIO_FLAGS_READ+
                +BIO_FLAGS_SHOULD_RETRY+)))

(defun set-retry-read-slots (bio)
  (bio-set-flags bio
                 (logior +BIO_FLAGS_READ+
                         +BIO_FLAGS_SHOULD_RETRY+)))

(defun set-retry-read (bio)
  (if *bio-is-opaque*
      (set-retry-read-opaque bio)
      (set-retry-read-slots bio)))

;;; Error handling for all the defcallback's:
;;;
;;; We want to avoid non-local exits across C stack,
;;; as CFFI tutorial recommends:
;;; https://common-lisp.net/project/cffi/manual/html_node/Tutorial_002dCallbacks.html.
;;;
;;; In cl+ssl this means the following nested calls:
;;;
;;;   1) Lisp: cl+ssl stream user code ->
;;;   2) C: OpenSSL C functions ->
;;;   3) Lisp: BIO implementation function
;;;        signals error and the controls is passed
;;;        to (1), without proper C cleanup.
;;;
;;; Therefore our BIO implementation functions catch all unexpected
;;; serious-conditions, arrange for BIO_should_retry
;;; to say "do not retry", and return error status (most often -1).
;;;
;;; We could try to return the real number of bytes read / written -
;;; the documentation of BIO_read and friends just says return byte
;;; number without making any special case for error:
;;;
;;; >    (...) return either the amount of data successfully read or
;;; >    written (if the return value is positive) or that no data was
;;; >    successfully read or written if the result is 0 or -1. If the
;;; >    return value is -2 then the operation is not implemented in the
;;; >    specific BIO type. The trailing NUL is not included in the length
;;; >    returned by BIO_gets().
;;;
;;; But let's not complicate the implementation, especially taking into
;;; account that we don't know how many bytes the low level
;;; Lisp function has really written before signalling
;;; the condition. Our main goal is to avoid crossing C stack,
;;; and we only consider unexpected errors here.

(defparameter *file-name* (cffi:foreign-string-alloc "cl+ssl/src/bio.lisp"))

(defun put-to-openssl-error-queue (condition)
  (ignore-errors

    ;; TODO: starting from OpenSSL 3.0.0 use ERR_raise_data instead
    ;; of the ERR_put_error / ERR_add_error_data combination.


    (err-put-error +err_lib_none+ 0 +err_r_internal_error+ *file-name* 0)

    #-cffi-sys::no-foreign-funcall ; because err-add-error-data is a vararg function
    (let ((err-msg (format nil
                           "Unexpected SERIOUS-CONDITION in the Lisp BIO: ~A"
                           condition)))
      (err-add-error-data 1 :string err-msg))))

(cffi:defcallback lisp-write :int ((bio :pointer) (buf :pointer) (n :int))
  (handler-case
      (progn (dotimes (i n)
               (write-byte (cffi:mem-ref buf :unsigned-char i) *socket*))
             (finish-output *socket*)
             n)
    (serious-condition (c)
      (clear-retry-flags bio)
      (put-to-openssl-error-queue c)
      -1)))

(cffi:defcallback lisp-read :int ((bio :pointer) (buf :pointer) (n :int))
  (handler-case
      (let ((i 0))
        (handler-case
            (progn
              (clear-retry-flags bio)
              (when (or *blockp* (listen *socket*))
                (setf (cffi:mem-ref buf :unsigned-char i) (read-byte *socket*))
                (incf i))
              (loop
                 while (and (< i n)
                            (or (null *partial-read-p*) (listen *socket*)))
                 do
                   (setf (cffi:mem-ref buf :unsigned-char i) (read-byte *socket*))
                   (incf i))
              (when (zerop i) (set-retry-read bio)))
          (end-of-file ()
            ;; do nothing,  will just return the number of bytes read so far
            ))
        i)
    (serious-condition (c)
      (clear-retry-flags bio)
      (put-to-openssl-error-queue c)
      -1)))

(cffi:defcallback lisp-gets :int ((bio :pointer) (buf :pointer) (n :int))
  (handler-case
      (let ((i 0)
            (max-chars (1- n)))
        (clear-retry-flags bio)
        (handler-case
            (when (> max-chars 0)
              (when (or *blockp* (listen *socket*))
                (setf (cffi:mem-ref buf :unsigned-char i) (read-byte *socket*))
                (incf i))
              (loop
                 with char
                 and exit = nil
                 while (and (< i max-chars)
                            (null exit)
                            (or (null *partial-read-p*) (listen *socket*)))
                 do
                   (setf char (read-byte *socket*)
                         exit (= char 10))
                   (setf (cffi:mem-ref buf :unsigned-char i) char)
                   (incf i)))
          (end-of-file ()
            ;; do nothing - this just aborts the lookp
            ))
        (setf (cffi:mem-ref buf :unsigned-char i) 0)
        i)
    (serious-condition (c)
      (clear-retry-flags bio)
      (put-to-openssl-error-queue c)
      -1)))

(cffi:defcallback lisp-puts :int ((bio :pointer) (buf :string))
  (handler-case
      (progn
        (write-line buf (flex:make-flexi-stream *socket* :external-format :ascii))
        ;; puts is not specified to return length, but BIO expects it :(
        (1+ (length buf)))
    (serious-condition (c)
      (clear-retry-flags bio)
      (put-to-openssl-error-queue c)
      -1)))

(cffi:defcallback lisp-ctrl :int
    ((bio :pointer) (cmd :int) (larg :long) (parg :pointer))
  (declare (ignore bio larg parg))
  (cond
    ((eql cmd +BIO_CTRL_FLUSH+) 1)
    (t
     ;; (warn "lisp-ctrl(~A,~A,~A)" cmd larg parg)
     0)))

;;; The create and destroy handlers mostly consist
;;; of setting zero values to some BIO fields,
;;; which seem redundant, because OpenSSl most likely
;;; does this itself. But we follow example of the
;;; standard OpenSSL BIO types implementation.
;;; Like the file_new / file_free here:
;;; https://github.com/openssl/openssl/blob/4ccad35756dfa9df657f3853810101fa9d6ca525/crypto/bio/bss_file.c#L109

(cffi:defcallback lisp-create-slots :int ((bio :pointer))
  (handler-case
      (progn
        (setf (cffi:foreign-slot-value bio '(:struct bio) 'init) 1) ; the only useful thing?
        (setf (cffi:foreign-slot-value bio '(:struct bio) 'num) 0)
        (setf (cffi:foreign-slot-value bio '(:struct bio) 'ptr) (cffi:null-pointer))
        (setf (cffi:foreign-slot-value bio '(:struct bio) 'flags) 0)
        1)
    (serious-condition (c)
      (put-to-openssl-error-queue c)
      0)))

(cffi:defcallback lisp-create-opaque :int ((bio :pointer))
  (handler-case
      (progn
        (bio-set-init bio 1) ; the only useful thing?
        (clear-retry-flags bio)
        1)
    (serious-condition (c)
      (put-to-openssl-error-queue c)
      0)))

(cffi:defcallback lisp-destroy-slots :int ((bio :pointer))
  (handler-case
      (cond
        ((cffi:null-pointer-p bio) 0)
        (t
         (setf (cffi:foreign-slot-value bio '(:struct bio) 'init) 0)
         (setf (cffi:foreign-slot-value bio '(:struct bio) 'flags) 0)
         1))
    (serious-condition (c)
      (put-to-openssl-error-queue c)
      0)))

(cffi:defcallback lisp-destroy-opaque :int ((bio :pointer))
  (handler-case
      (cond
        ((cffi:null-pointer-p bio) 0)
        (t
         (bio-set-init bio 0)
         (clear-retry-flags bio)
         1))
    (serious-condition (c)
      (put-to-openssl-error-queue c)
      0)))

;;; Convenience macros
(defmacro with-bio-output-to-string ((bio &key (element-type ''character) (transformer '#'code-char)) &body body)
  "Evaluate BODY with BIO bound to a SSL BIO structure that writes to a
Common Lisp string.  The string is returned."
  `(let ((*socket* (flex:make-in-memory-output-stream :element-type ,element-type :transformer ,transformer))
	 (,bio (bio-new-lisp)))
     (unwind-protect
          (progn ,@body)
       (bio-free ,bio))
     (flex:get-output-stream-sequence *socket*)))

(defmacro with-bio-input-from-string ((bio string &key (transformer '#'char-code))
				      &body body)
  "Evaluate BODY with BIO bound to a SSL BIO structure that reads from
a Common Lisp STRING."
  `(let ((*socket* (flex:make-in-memory-input-stream ,string :transformer ,transformer))
	 (,bio (bio-new-lisp)))
     (unwind-protect
          (progn ,@body)
       (bio-free ,bio))))

;; TODO: Refactor dependendies, err-print-error-to-sting is used
;;       in conditions.lisp, earlier than it is defined in the bio.lisp.
;;       Becuase we can only define it after BIO functionality is implemented.
;;       And bio.lisp depends on ffi.lisp, and ffi.lisp depends on conditions.lisp.
(defun err-print-errors-to-string ()
  (with-bio-output-to-string (bio)
    (err-print-errors bio)))

(setf *bio-lisp-method* nil)    ;force reinit if anything changed here
