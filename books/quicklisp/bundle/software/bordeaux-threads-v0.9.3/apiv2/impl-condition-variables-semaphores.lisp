;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Portable condition variables using semaphores.
;;;
;;; The implementation is meant to be correct and readable,
;;; without trying too hard to be very fast.
;;;

(defstruct queue
  (vector (make-array 7 :adjustable t :fill-pointer 0) :type vector)
  (lock (%make-lock nil) :type native-lock))

(defun queue-drain (queue)
  (%with-lock ((queue-lock queue) nil)
    (shiftf (queue-vector queue)
            (make-array 7 :adjustable t :fill-pointer 0))))

(defun queue-dequeue (queue)
  (%with-lock ((queue-lock queue) nil)
    (let ((vector (queue-vector queue)))
      (if (zerop (length vector))
          nil
          (vector-pop vector)))))

(defun queue-enqueue (queue value)
  (%with-lock ((queue-lock queue) nil)
    (vector-push-extend value (queue-vector queue))))

(defstruct (condition-variable
            (:constructor %make-condition-variable (name))
            ;; CONDITION-VARIABLE-P is defined in API-CONDITION-VARIABLES.LISP
            (:predicate nil))
  name
  (queue (make-queue)))

(defmethod print-object ((cv condition-variable) stream)
  (print-unreadable-object (cv stream :type t :identity t)
    (format stream "~S" (condition-variable-name cv))))

(defun %condition-wait (cv lock timeout)
  (with-slots (queue) cv
    (let* ((thread (current-thread))
           (semaphore (%thread-semaphore thread)))
      (queue-enqueue queue thread)
      (%release-lock lock)
      (unwind-protect
           (%wait-on-semaphore semaphore timeout)
        (%acquire-lock lock t nil)))))

(defun %condition-notify (cv)
  (with-slots (queue) cv
    (when-let ((next-thread (queue-dequeue queue)))
      (%signal-semaphore (%thread-semaphore next-thread) 1))))

(defun %condition-broadcast (cv)
  (with-slots (queue) cv
    (let ((queued-threads (queue-drain queue)))
      (map nil (lambda (thr)
                 (%signal-semaphore (%thread-semaphore thr) 1))
           queued-threads))))
