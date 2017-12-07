;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; early.lisp --- Early definitions used throughout OSICAT-POSIX.
;;;
;;; Copyright (C) 2005-2006, Matthew Backes  <lucca@accela.net>
;;; Copyright (C) 2005-2006, Dan Knapp  <dankna@accela.net>
;;; Copyright (C) 2006-2007, Stelian Ionescu  <stelian.ionescu-zeus@poste.it>
;;; Copyright (C) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(in-package #:osicat-posix)

;;; Subtypes of POSIX-ERROR correspond to errors detected through the
;;; ERRNO mechanism.  These are defined below.
;;;
;;; There is a PRINT-OBJECT method specialized on POSIX-ERROR defined
;;; in basic-unix.lisp because it needs %STRERROR-R defined later in
;;; wrappers.lisp.
(define-condition posix-error (system-error)
  ((object :initform nil :initarg :object :reader posix-error-object)
   (syscall :initform nil :initarg :syscall :reader posix-error-syscall))
  (:documentation
   "POSIX-ERRORs are signalled whenever ERRNO is set by a POSIX call or
where the POSIX call signals an error via the return value."))

;;; HASH TABLE mapping keywords (such as :EAGAIN) to symbols denoting
;;; subtypes of POSIX-ERROR.
(defparameter *posix-error-map* (make-hash-table :test #'eq))

(defun get-posix-error-condition (keyword)
  (gethash keyword *posix-error-map*))

;;; Define an error condition for each ERRNO value defined in the
;;; ERRNO-VALUES enum type and populate *POSIX-ERROR-MAP*.
(macrolet
    ((define-posix-errors (keywords)
       `(progn
          ,@(loop for kw in keywords collect
                  (let ((cond-name (intern (symbol-name kw)))
                        (code (foreign-enum-value 'errno-values kw)))
                    `(progn
                       (define-condition ,cond-name (posix-error) ()
                         (:default-initargs :code ,code :identifier ,kw))
                       (setf (gethash ,kw *posix-error-map*) ',cond-name)))))))
  (define-posix-errors
      #.(foreign-enum-keyword-list 'errno-values)))

;;; Instantiates a subclass of POSIX-ERROR matching ERR or a plain
;;; POSIX-ERROR if no matching subclass is found.  ERR can be either a
;;; keyword or an integer both denoting an ERRNO value.
(defun make-posix-error (err object syscall)
  (let (error-keyword error-code)
    (etypecase err
      (keyword (setf error-keyword err)
               (setf error-code (foreign-enum-value 'errno-values err :errorp nil)))
      (integer (setf error-keyword (or (foreign-enum-keyword 'errno-values err :errorp nil)
                                       :unknown))
               (setf error-code err)))
    (if-let (condition-class (get-posix-error-condition error-keyword))
            (make-condition condition-class
                            :object object
                            :syscall syscall)
            (make-condition 'posix-error
                            :object object
                            :code error-code
                            :identifier error-keyword
                            :syscall syscall))))

;;; This might be a silly question but, who resets ERRNO?  Should we?
;;; I ask because we have some function bindings with DEFSYSCALL that
;;; have no documented ERRNO behaviour and we're checking ERRNO when
;;; they fail anyway.  --luis

(defun posix-error (&optional (errno (get-errno)) object syscall)
  (error (make-posix-error errno object syscall)))

;;; Default ERROR-GENERATOR for ERRNO-WRAPPER.
(defun syscall-signal-posix-error (return-value object syscall)
  (declare (ignore return-value))
  (posix-error (get-errno) object syscall))

(defun syscall-signal-posix-error-via-return-value (return-value object syscall)
  (posix-error return-value object syscall))

;;; Error predicate that always returns NIL.  Not actually used
;;; because the ERRNO-WRAPPER optimizes this call away.
(defun never-fails (&rest args)
  (declare (ignore args))
  nil)

;;; NOTE: This is a pretty neat type that probably deserves to be
;;; included in CFFI. --luis
;;;
;;; This type is used by DEFSYSCALL to automatically check for errors
;;; using the ERROR-PREDICATE function which is passed the foreign
;;; function's return value (after going through RETURN-FILTER).  If
;;; ERROR-PREDICATE returns true, ERROR-GENERATOR is invoked.  See the
;;; ERRNO-WRAPPER parse method and type translation.
(define-foreign-type errno-wrapper ()
  ((error-predicate :initarg :error-predicate :reader error-predicate)
   (return-filter :initarg :return-filter :reader return-filter)
   (error-generator :initarg :error-generator :reader error-generator)
   (base-type :initarg :base-type :reader base-type)
   (object :initarg :object :reader errno-object)
   (function-name :initarg :function-name :reader function-name)))

;; NOTE: this is an ugly type-punning. An alternative is to compute
;; this value from (cffi:foreign-type-size :uintptr), but it requires
;; also knowing how many bits are in a byte.
(defconstant +most-positive-uintptr+ (with-foreign-object (p :intptr)
                                       (setf (mem-ref p :intptr) -1)
                                       (mem-ref p :uintptr)))

;; on some systems, map-failed is groveled as -1 :(
#-windows
(defvar *map-failed-pointer* (make-pointer (logand map-failed +most-positive-uintptr+)))


;;; FIXME: undocumented in cffi-grovel.
(defun make-from-pointer-function-name (type-name)
  (format-symbol t "~A-~A-~A-~A" '#:make type-name '#:from '#:pointer))

(define-parse-method errno-wrapper
    (base-type &key object error-predicate (return-filter 'identity)
               (error-generator 'syscall-signal-posix-error)
               function-name)
  ;; pick a default error-predicate
  (unless error-predicate
    (case base-type
      (:pointer
       (setf error-predicate 'null-pointer-p))
      (:string
       (setf error-predicate '(lambda (s) (not (stringp s)))))
      ((:int :long time ssize pid off)
       (setf error-predicate 'minusp))
      ;; FIXME: go here if the canonical type is unsigned.
      ((:void :unsigned-int mode uid gid)
       (setf error-predicate 'never-fails))
      (t
       (if (eq (cffi::canonicalize-foreign-type base-type) :pointer)
           ;; MAKE-FROM-POINTER-FUNCTION-NAME is used in cffi-grovel's
           ;; CSTRUCT-AND-CLASS but we don't actually use it anywhere
           ;; that I know of so this fallback RETURN-FILTER is
           ;; probably bogus.
           (setf error-predicate 'null-pointer-p
                 return-filter (make-from-pointer-function-name base-type))
           (error "Could not choose a error-predicate function.")))))
  (make-instance 'errno-wrapper
                 :object object
                 :actual-type base-type
                 :base-type base-type
                 :error-predicate error-predicate
                 :return-filter return-filter
                 :error-generator error-generator
                 :function-name function-name))

;;; This type translator sets up the appropriate calls to
;;; RETURN-FILTER, ERROR-PREDICATE and ERROR-GENERATOR around the
;;; foreign function call.
(defmethod expand-from-foreign (value (type errno-wrapper))
  (if (and (eq (return-filter type) 'identity)
           (eq (error-predicate type) 'never-fails))
      value
      `(let ((r (convert-from-foreign ,value ',(base-type type))))
         ,(let ((return-exp (if (eq (return-filter type) 'identity)
                               'r
                               `(,(return-filter type) r))))
            (if (eq (error-predicate type) 'never-fails)
                return-exp
                `(if (,(error-predicate type) r)
                     (,(error-generator type) r ,(errno-object type)
                       ',(function-name type))
                     ,return-exp))))))

(defmacro defsyscall (name-and-opts return-type &body args)
  "Simple wrapper around DEFCFUN that changes the RETURN-TYPE
to (ERRNO-WRAPPER RETURN-TYPE).  On windows, prepends #\_ to
the C function name."
  (multiple-value-bind (lisp-name c-name options)
      (cffi::parse-name-and-options name-and-opts)
    #+windows (setf c-name (concatenate 'string "_" c-name))
    `(defcfun (,c-name ,lisp-name ,@options)
         (errno-wrapper ,return-type :function-name ,lisp-name)
       ,@args)))

;;; This workaround for windows sucks. --luis
(defmacro defcsyscall (name-and-opts return-type &body args)
  "Like DEFSYSCALL but doesn't prepend #\_ to the C function name on
windows (or any other platform)."
  (let ((lisp-name (cffi::parse-name-and-options name-and-opts)))
    `(defcfun ,name-and-opts
         (errno-wrapper ,return-type :function-name ,lisp-name)
       ,@args)))
