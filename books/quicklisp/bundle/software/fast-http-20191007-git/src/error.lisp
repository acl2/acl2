(in-package :cl-user)
(defpackage fast-http.error
  (:use :cl)
  (:export :fast-http-error

           :callback-error
           :cb-message-begin
           :cb-url
           :cb-first-line
           :cb-header-field
           :cb-header-value
           :cb-headers-complete
           :cb-body
           :cb-message-complete
           :cb-status

           :parsing-error
           :invalid-eof-state
           :header-overflow
           :closed-connection
           :invalid-version
           :invalid-status
           :invalid-method
           :invalid-url
           :invalid-host
           :invalid-port
           :invalid-path
           :invalid-query-string
           :invalid-fragment
           :lf-expected
           :invalid-header-token
           :invalid-content-length
           :invalid-chunk-size
           :invalid-constant
           :invalid-internal-state
           :strict-error
           :paused-error
           :unknown-error

           :multipart-parsing-error
           :invalid-multipart-body
           :invalid-boundary

           :header-value-parsing-error
           :invalid-header-value
           :invalid-parameter-key
           :invalid-parameter-value))
(in-package :fast-http.error)

(define-condition fast-http-error (simple-error)
  (description)
  (:report
   (lambda (condition stream)
     (format stream "~A: ~A" (type-of condition) (slot-value condition 'description)))))


;;
;; Callback-related errors

(define-condition callback-error (fast-http-error)
  ((error :initarg :error
          :initform nil))
  (:report (lambda (condition stream)
             (with-slots (description error) condition
               (format stream "Callback Error: ~A~:[~;~:*~%  ~A~]"
                       description
                       error)))))

(define-condition cb-message-begin (callback-error)
  ((description :initform "the message-begin callback failed")))
(define-condition cb-url (callback-error)
  ((description :initform "the url callback failed")))
(define-condition cb-first-line (callback-error)
  ((description :initform "the first line callback failed")))
(define-condition cb-header-field (callback-error)
  ((description :initform "the header-field callback failed")))
(define-condition cb-header-value (callback-error)
  ((description :initform "the header-value callback failed")))
(define-condition cb-headers-complete (callback-error)
  ((description :initform "the headers-complete callback failed")))
(define-condition cb-body (callback-error)
  ((description :initform "the body callback failed")))
(define-condition cb-message-complete (callback-error)
  ((description :initform "the message-complete callback failed")))
(define-condition cb-status (callback-error)
  ((description :initform "the status callback failed")))


;;
;; Parsing-related errors

(define-condition parsing-error (fast-http-error) ())

(define-condition invalid-eof-state (parsing-error)
  ((description :initform "stream ended at an unexpected time")))
(define-condition header-overflow (parsing-error)
  ((description :initform "too many header bytes seen; overflow detected")))
(define-condition closed-connection (parsing-error)
  ((description :initform "data received after completed connection: close message")))
(define-condition invalid-version (parsing-error)
  ((description :initform "invalid HTTP version")))
(define-condition invalid-status (parsing-error)
  ((description :initform "invalid HTTP status code")
   (status-code :initarg :status-code
                :initform nil))
  (:report (lambda (condition stream)
             (with-slots (description status-code) condition
               (format stream "~A: ~A~:[~;~:* (Code=~A)~]"
                       (type-of condition)
                       description
                       status-code)))))
(define-condition invalid-method (parsing-error)
  ((description :initform "invalid HTTP method")))
(define-condition invalid-url (parsing-error)
  ((description :initform "invalid URL")))
(define-condition invalid-host (parsing-error)
  ((description :initform "invalid host")))
(define-condition invalid-port (parsing-error)
  ((description :initform "invalid port")))
(define-condition invalid-path (parsing-error)
  ((description :initform "invalid path")))
(define-condition invalid-query-string (parsing-error)
  ((description :initform "invalid query string")))
(define-condition invalid-fragment (parsing-error)
  ((description :initform "invalid fragment")))
(define-condition lf-expected (parsing-error)
  ((description :initform "LF character expected")))
(define-condition invalid-header-token (parsing-error)
  ((description :initform "invalid character in header")))
(define-condition invalid-content-length (parsing-error)
  ((description :initform "invalid character in content-length header")))
(define-condition invalid-chunk-size (parsing-error)
  ((description :initform "invalid character in chunk size header")))
(define-condition invalid-constant (parsing-error)
  ((description :initform "invalid constant string")))

(define-condition invalid-internal-state (parsing-error)
  ((description :initform "encountered unexpected internal state")
   (code :initarg :code))
  (:report
   (lambda (condition stream)
     (format stream "~A: ~A (Code=~A)"
             (type-of condition)
             (slot-value condition 'description)
             (slot-value condition 'code)))))
(define-condition strict-error (parsing-error)
  ((description :initform "strict mode assertion failed")
   (form :initarg :form))
  (:report
   (lambda (condition stream)
     (format stream "~A: ~A~%  ~A"
             (type-of condition)
             (slot-value condition 'description)
             (slot-value condition 'form)))))
(define-condition paused-error (parsing-error)
  ((description :initform "parser is paused")))
(define-condition unknown-error (parsing-error)
  ((description :initform "an unknown error occured")))


;;
;; Multipart parsing

(define-condition multipart-parsing-error (fast-http-error) ())

(define-condition invalid-multipart-body (multipart-parsing-error)
  ((description :initform "invalid multipart body")))
(define-condition invalid-boundary (multipart-parsing-error)
  ((description :initform "invalid boundary")))


;;
;; Header value parsing

(define-condition header-value-parsing-error (multipart-parsing-error) ())

(define-condition invalid-header-value (header-value-parsing-error)
  ((description :initform "invalid header value")))
(define-condition invalid-parameter-key (header-value-parsing-error)
  ((description :initform "invalid parameter key")))
(define-condition invalid-parameter-value (header-value-parsing-error)
  ((description :initform "invalid parameter value")))
