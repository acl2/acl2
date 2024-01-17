;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

(defstruct (atomic-integer
            (:constructor %make-atomic-integer (cell)))
  "Wrapper for java.util.concurrent.AtomicLong."
  cell)

(defmethod print-object ((aint atomic-integer) stream)
  (print-unreadable-object (aint stream :type t :identity t)
    (format stream "~S" (atomic-integer-value aint))))

(deftype %atomic-integer-value ()
  '(unsigned-byte 63))

(defun make-atomic-integer (&key (value 0))
  (check-type value %atomic-integer-value)
  (%make-atomic-integer
   (jnew "java.util.concurrent.atomic.AtomicLong" value)))

(defconstant +atomic-long-cas+
  (jmethod "java.util.concurrent.atomic.AtomicLong" "compareAndSet"
           (jclass "long") (jclass "long")))

(defun atomic-integer-compare-and-swap (atomic-integer old new)
  (declare (type atomic-integer atomic-integer)
           (type %atomic-integer-value old new)
           (optimize (safety 0) (speed 3)))
  (jcall +atomic-long-cas+ (atomic-integer-cell atomic-integer)
         old new))

(defconstant +atomic-long-incf+
  (jmethod "java.util.concurrent.atomic.AtomicLong" "getAndAdd"
           (jclass "long")))

(defun atomic-integer-decf (atomic-integer &optional (delta 1))
  (declare (type atomic-integer atomic-integer)
           (type %atomic-integer-value delta)
           (optimize (safety 0) (speed 3)))
  (let ((increment (- delta)))
    (+ (jcall +atomic-long-incf+ (atomic-integer-cell atomic-integer)
              increment)
       increment)))

(defun atomic-integer-incf (atomic-integer &optional (delta 1))
  (declare (type atomic-integer atomic-integer)
           (type %atomic-integer-value delta)
           (optimize (safety 0) (speed 3)))
  (+ (jcall +atomic-long-incf+ (atomic-integer-cell atomic-integer)
            delta)
     delta))

(defconstant +atomic-long-get+
  (jmethod "java.util.concurrent.atomic.AtomicLong" "get"))

(defun atomic-integer-value (atomic-integer)
  (declare (type atomic-integer atomic-integer)
           (optimize (safety 0) (speed 3)))
  (jcall +atomic-long-get+ (atomic-integer-cell atomic-integer)))

(defconstant +atomic-long-set+
  (jmethod "java.util.concurrent.atomic.AtomicLong" "set"
           (jclass "long")))

(defun (setf atomic-integer-value) (newval atomic-integer)
  (declare (type atomic-integer atomic-integer)
           (type %atomic-integer-value newval)
           (optimize (safety 0) (speed 3)))
  (jcall +atomic-long-set+ (atomic-integer-cell atomic-integer)
         newval)
  newval)
