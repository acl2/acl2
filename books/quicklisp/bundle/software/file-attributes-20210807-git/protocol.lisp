#|
 This file is a part of file-attributes
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.file-attributes)

(defmacro define-implementable (name args)
  `(setf (fdefinition ',name)
         (lambda ,args
           (declare (ignore ,@args))
           (error "Not implemented"))))

(defmacro define-implementation (name args &body body)
  `(progn
     (fmakunbound ',name)
     (defun ,name ,args ,@body)))

(define-implementable access-time (file))
(define-implementable (setf access-time) (value file))
(define-implementable modification-time (file))
(define-implementable (setf modification-time) (value file))
(define-implementable creation-time (file))
(define-implementable (setf creation-time) (value file))
(define-implementable group (file))
(define-implementable (setf group) (value file))
(define-implementable owner (file))
(define-implementable (setf owner) (value file))
(define-implementable attributes (file))
(define-implementable (setf attributes) (value file))

(defun enbitfield (list &rest bits)
  (let ((int 0))
    (loop for i from 0
          for bit in bits
          do (when (find bit list) (setf (ldb (cl:byte 1 i) int) 1)))
    int))

(defun debitfield (int &rest bits)
  (loop for i from 0
        for bit in bits
        when (logbitp i int)
        collect bit))

(defvar *system*
  #+unix :unix
  #+windows :windows
  #+mezzano :mezzano
  #-(or unix windows) :unknown)

(defvar *windows-attributes*
  '(:read-only :hidden :system-file NIL :directory :archived :device :normal :temporary :sparse :link :compressed :offline :not-indexed :encrypted :integrity :virtual :no-scrub :recall))

(defvar *unix-attributes*
  '(:other-execute :other-write :other-read :group-execute :group-write :group-read :owner-execute :owner-write :owner-read :sticky :set-group :set-user :fifo :device :directory :normal :link :socket))

(defun decode-bitfield (int bits)
  (loop for i from 0
        for bit in bits
        when bit collect bit
        when bit collect (logbitp i int)))

(defun encode-bitfield (field bits)
  (loop with int = 0
        for i from 0
        for bit in bits
        do (when (getf field bit)
             (setf (ldb (cl:byte 1 i) int) 1))
        finally (return int)))

(defun decode-attributes (attributes &optional (system *system*))
  (case system
    (:unix
     (decode-bitfield attributes *unix-attributes*))
    (:windows
     (decode-bitfield attributes *windows-attributes*))
    (:mezzano
     (append (decode-attributes (ldb (byte 16  0) attributes) :unix)
             (decode-attributes (ldb (byte 16 16) attributes) :windows)))))

(defun encode-attributes (attributes &optional (system *system*))
  (case system
    (:unix
     (encode-bitfield attributes *unix-attributes*))
    (:windows
     (encode-bitfield attributes *windows-attributes*))
    (:mezzano
     (let ((i 0))
       (setf (ldb (byte 16  0) i) (encode-attributes attributes :unix))
       (setf (ldb (byte 16 16) i) (encode-attributes attributes :windows))
       i))
    (T
     0)))

(defun enpath (path)
  (etypecase path
    (string (namestring (truename path)))
    (stream (namestring (truename (pathname path))))
    (pathname (namestring (truename path)))))
