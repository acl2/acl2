;;;; -*- Mode: LISP; Syntax: Ansi-Common-Lisp; Package: BORDEAUX-THREADS; Base: 10; -*-

#|
Distributed under the MIT license (see LICENSE file)
|#

(in-package #:bordeaux-threads)

(deftype thread ()
  'process:process)

;;; Thread Creation

(defun %make-thread (function name)
  (process:process-run-function name function))

(defun current-thread ()
  scl:*current-process*)

(defun threadp (object)
  (process:process-p object))

(defun thread-name (thread)
  (process:process-name thread))

;;; Resource contention: locks and recursive locks

(defstruct (lock (:constructor make-lock-internal))
  lock
  lock-argument)

(defun make-lock (&optional name)
  (let ((lock (process:make-lock (or name "Anonymous lock"))))
    (make-lock-internal :lock lock
			:lock-argument nil)))

(defun acquire-lock (lock &optional (wait-p t))
  (check-type lock lock)
  (setf (lock-lock-argument lock) (process:make-lock-argument (lock-lock lock)))
  (if wait-p
      (process:lock (lock-lock lock) (lock-lock-argument lock))
      (process:with-no-other-processes
	(when (process:lock-lockable-p (lock-lock lock))
	  (process:lock (lock-lock lock) (lock-lock-argument lock))))))

(defun release-lock (lock)
  (check-type lock lock)
  (process:unlock (lock-lock lock) (scl:shiftf (lock-lock-argument lock) nil)))

(defmacro with-lock-held ((place) &body body)
  `(process:with-lock ((lock-lock ,place))
     ,@body))

(defstruct (recursive-lock (:constructor make-recursive-lock-internal))
  lock
  lock-arguments)

(defun make-recursive-lock (&optional name)
  (make-recursive-lock-internal :lock (process:make-lock (or name "Anonymous recursive lock")
							 :recursive t)
				:lock-arguments nil))

(defun acquire-recursive-lock (lock)
  (check-type lock recursive-lock)
  (process:lock (recursive-lock-lock lock)
		(car (push (process:make-lock-argument (recursive-lock-lock lock))
			   (recursive-lock-lock-arguments lock)))))

(defun release-recursive-lock (lock)
  (check-type lock recursive-lock)
  (process:unlock (recursive-lock-lock lock) (pop (recursive-lock-lock-arguments lock))))

(defmacro with-recursive-lock-held ((place) &body body)
  `(process:with-lock ((recursive-lock-lock ,place))
     ,@body))

;;; Resource contention: condition variables

(eval-when (:compile-toplevel :load-toplevel :execute)
(defstruct (condition-variable (:constructor %make-condition-variable))
  name
  (waiters nil))
)

(defun make-condition-variable (&key name)
  (%make-condition-variable :name name))

(defun condition-wait (condition-variable lock)
  (check-type condition-variable condition-variable)
  (check-type lock lock)
  (process:with-no-other-processes
    (let ((waiter (cons scl:*current-process* nil)))
      (process:atomic-updatef (condition-variable-waiters condition-variable)
			      #'(lambda (waiters)
				  (append waiters (scl:ncons waiter))))
      (process:without-lock ((lock-lock lock))
	  (process:process-block (format nil "Waiting~@[ on ~A~]"
					 (condition-variable-name condition-variable))
				 #'(lambda (waiter)
				     (not (null (cdr waiter))))
				 waiter)))))

(defun condition-notify (condition-variable)
  (check-type condition-variable condition-variable)
  (let ((waiter (process:atomic-pop (condition-variable-waiters condition-variable))))
    (when waiter
      (setf (cdr waiter) t)
      (process:wakeup (car waiter))))
  (values))

(defun thread-yield ()
  (scl:process-allow-schedule))

;;; Introspection/debugging

(defun all-threads ()
  process:*all-processes*)

(defun interrupt-thread (thread function &rest args)
  (declare (dynamic-extent args))
  (apply #'process:process-interrupt thread function args))

(defun destroy-thread (thread)
  (signal-error-if-current-thread thread)
  (process:process-kill thread :without-aborts :force))

(defun thread-alive-p (thread)
  (process:process-active-p thread))

(defun join-thread (thread)
  (process:process-wait (format nil "Join ~S" thread)
			#'(lambda (thread)
			    (not (process:process-active-p thread)))
			thread))

(mark-supported)
