(in-package #:org.shirakumo.zippy)

(define-condition zippy-condition () ())

(define-condition decoding-error (error zippy-condition) ())
(define-condition encoding-error (error zippy-condition) ())

(define-condition unknown-block-signature (decoding-error)
  ((signature :initarg :signature :reader signature))
  (:report (lambda (c s) (format s "Don't know how to process block with signature~%  ~x"
                                 (signature c)))))

(define-condition unknown-structure-type (encoding-error)
  ((object :initarg :object :reader object))
  (:report (lambda (c s) (format s "Don't know how to process a structure with type~%  ~a"
                                 (type-of (object c))))))

(define-condition mismatched-type-signature (decoding-error)
  ((signature :initarg :signature :reader signature))
  (:report (lambda (c s) (format s "Record does not match signature~%  ~x"
                                 (signature c)))))

(define-condition zip64-required (encoding-error)
  ((parameter :initarg :parameter :reader parameter))
  (:report (lambda (c s) (format s "ZIP64 extension is required to encode the given archive contents but ~
                       its use has been disallowed via ~S ~S." :zip64 (parameter c)))))

(define-condition out-of-bounds-seek (decoding-error)
  ((target :initarg :target :reader target))
  (:report (lambda (c s) (format s "Cannot seek outside allowed vector range to~%  ~a"
                                 (target c)))))

(define-condition stream-closed (decoding-error)
  ()
  (:report (lambda (c s) (format s "The ZIP disk streams have already been closed."))))

(define-condition malformed-file (decoding-error)
  ((message :initarg :message :initform NIL :reader message))
  (:report (lambda (c s) (format s "The zip file appears corrupted and cannot be read~@[:~%  ~a~]"
                                 (message c)))))

(define-condition required-version-mismatched (decoding-error)
  ((specified-version :initarg :specified-version :reader specified-version) 
   (required-version :initarg :required-version :reader required-version))
  (:report (lambda (c s) (format s "~@<The specified version needed for extracting the archive is ~S which ~
                       is less than the actually needed version which is ~S.~@:>"
                                 (specified-version c) (required-version c)))))

(define-condition integer-too-large (encoding-error)
  ((object :initarg :object :reader object))
  (:report (lambda (c s) (format s "The integer is too large~%  ~a"
                                 (object c)))))

(define-condition unsupported-compression-method (error zippy-condition)
  ((compression-method :initarg :compression-method :reader compression-method))
  (:report (lambda (c s) (format s "The compression method is not supported:~%  ~a"
                                 (compression-method c)))))

(define-condition unsupported-encryption-method (error zippy-condition)
  ((encryption-method :initarg :encryption-method :reader encryption-method))
  (:report (lambda (c s) (format s "The encryption method is not supported:~%  ~a"
                                 (encryption-method c)))))

(define-condition unknown-enum-value (error zippy-condition)
  ((value :initarg :value :reader value))
  (:report (lambda (c s) (format s "The value was specified but is unknown:~%  ~a"
                                 (value c)))))

(define-condition password-required (decoding-error)
  ()
  (:report (lambda (c s) (format s "A password is required to decode this ZIP archive."))))
