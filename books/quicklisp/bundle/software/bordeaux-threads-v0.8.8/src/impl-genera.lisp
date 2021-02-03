;;;; -*- Mode: LISP; Syntax: Ansi-Common-Lisp; Package: BORDEAUX-THREADS; Base: 10; -*-

#|
Distributed under the MIT license (see LICENSE file)
|#

(in-package #:bordeaux-threads)

(deftype thread ()
  'process:process)

(defvar *thread-recursive-lock-key* 0)

;;; Thread Creation

(defun %make-thread (function name)
  (flet ((top-level ()
           (let* ((*thread-recursive-lock-key* 0)
                  (return-values
                    (multiple-value-list (funcall function))))
             (setf (si:process-spare-slot-4 scl:*current-process*) return-values)
             (values-list return-values))))
    (declare (dynamic-extent #'top-level))
    (process:process-run-function name #'top-level)))

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
  (let ((lock-argument (process:make-lock-argument (lock-lock lock))))
    (cond (wait-p
           (process:lock (lock-lock lock) lock-argument)
           (setf (lock-lock-argument lock) lock-argument)
           t)
          (t
           (process:with-no-other-processes
             (when (process:lock-lockable-p (lock-lock lock))
               (process:lock (lock-lock lock) lock-argument)
               (setf (lock-lock-argument lock) lock-argument)
               t))))))

(defun release-lock (lock)
  (check-type lock lock)
  (process:unlock (lock-lock lock) (scl:shiftf (lock-lock-argument lock) nil)))

(defstruct (recursive-lock (:constructor make-recursive-lock-internal))
  lock
  lock-arguments)

(defun make-recursive-lock (&optional name)
  (make-recursive-lock-internal :lock (process:make-lock (or name "Anonymous recursive lock")
                                                         :recursive t)
                                :lock-arguments (make-hash-table :test #'equal)))

(defun acquire-recursive-lock (lock)
  (check-type lock recursive-lock)
  (acquire-recursive-lock-internal lock))

(defun acquire-recursive-lock-internal (lock &optional timeout)
  (let ((key (cons (incf *thread-recursive-lock-key*) scl:*current-process*))
        (lock-argument (process:make-lock-argument (recursive-lock-lock lock))))
    (cond (timeout
           (process:with-no-other-processes
             (when (process:lock-lockable-p (recursive-lock-lock lock))
               (process:lock (recursive-lock-lock lock) lock-argument)
               (setf (gethash key (recursive-lock-lock-arguments lock)) lock-argument)
               t)))
          (t
           (process:lock (recursive-lock-lock lock) lock-argument)
           (setf (gethash key (recursive-lock-lock-arguments lock)) lock-argument)
           t))))

(defun release-recursive-lock (lock)
  (check-type lock recursive-lock)
  (let* ((key (cons *thread-recursive-lock-key* scl:*current-process*))
         (lock-argument (gethash key (recursive-lock-lock-arguments lock))))
    (prog1
        (process:unlock (recursive-lock-lock lock) lock-argument)
      (decf *thread-recursive-lock-key*)
      (remhash key (recursive-lock-lock-arguments lock)))))

(defmacro with-recursive-lock-held ((place &key timeout) &body body)
  `(with-recursive-lock-held-internal ,place ,timeout #'(lambda () ,@body)))

(defun with-recursive-lock-held-internal (lock timeout function)
  (check-type lock recursive-lock)
  (assert (typep timeout '(or null (satisfies zerop))) (timeout)
          'bordeaux-mp-condition :message ":TIMEOUT value must be either NIL or 0")
  (when (acquire-recursive-lock-internal lock timeout)
    (unwind-protect
        (funcall function)
      (release-recursive-lock lock))))

;;; Resource contention: condition variables

(eval-when (:compile-toplevel :load-toplevel :execute)
(defstruct (condition-variable (:constructor %make-condition-variable))
  name
  (waiters nil))
)

(defun make-condition-variable (&key name)
  (%make-condition-variable :name name))

(defun condition-wait (condition-variable lock &key timeout)
  (check-type condition-variable condition-variable)
  (check-type lock lock)
  (process:with-no-other-processes
    (let ((waiter (cons scl:*current-process* nil)))
      (process:atomic-updatef (condition-variable-waiters condition-variable)
                              #'(lambda (waiters)
                                  (append waiters (scl:ncons waiter))))
      (let ((expired? t))
        (unwind-protect
            (progn
              (release-lock lock)
              (process:block-with-timeout timeout
                                          (format nil "Waiting~@[ on ~A~]"
                                                  (condition-variable-name condition-variable))
                                          #'(lambda (waiter expired?-loc)
                                              (when (not (null (cdr waiter)))
                                                (setf (sys:location-contents expired?-loc) nil)
                                                t))
                                          waiter (sys:value-cell-location 'expired?))
              expired?)
          (unless expired?
            (acquire-lock lock)))))))

(defun condition-notify (condition-variable)
  (check-type condition-variable condition-variable)
  (let ((waiter (process:atomic-pop (condition-variable-waiters condition-variable))))
    (when waiter
      (setf (cdr waiter) t)
      (process:wakeup (car waiter))))
  (values))

(defun thread-yield ()
  (scl:process-allow-schedule))

;;; Timeouts

(defmacro with-timeout ((timeout) &body body)
  "Execute `BODY' and signal a condition of type TIMEOUT if the execution of
BODY does not complete within `TIMEOUT' seconds."
  `(with-timeout-internal ,timeout #'(lambda () ,@body)))

(defun with-timeout-internal (timeout function)
  ;; PROCESS:WITH-TIMEOUT either returns NIL on timeout or signals an error which,
  ;; unforutnately, does not have a distinguished type (i.e., it's a SYS:FATAL-ERROR).
  ;; So, rather than try to catch the error and signal our condition, we instead
  ;; ensure the return value from the PROCESS:WITH-TIMEOUT is never NIL if there is
  ;; no timeout. (Sigh)
  (let ((result (process:with-timeout (timeout)
                  (cons 'success (multiple-value-list (funcall function))))))
    (if result
        (values-list (cdr result))
        (error 'timeout :length timeout))))

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
                        thread)
  (values-list (si:process-spare-slot-4 thread)))

(mark-supported)
