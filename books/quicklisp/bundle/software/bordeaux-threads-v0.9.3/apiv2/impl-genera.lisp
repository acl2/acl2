;;;; -*- Mode: LISP; Syntax: Ansi-Common-Lisp; Package: BORDEAUX-THREADS-2; Base: 10; -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'process:process)

(defvar *thread-recursive-lock-key* 0)

(defun %make-thread (function name)
  (flet ((top-level ()
           (let ((*thread-recursive-lock-key* 0))
             (funcall function))))
    (declare (dynamic-extent #'top-level))
    (process:process-run-function name #'top-level)))

(defun %current-thread ()
  scl:*current-process*)

(defun %thread-name (thread)
  (process:process-name thread))

(defun %join-thread (thread)
  (process:process-wait (format nil "Join ~S" thread)
                        #'(lambda (thread)
                            (not (process:process-active-p thread)))
                        thread))

(defun %thread-yield ()
  (scl:process-allow-schedule))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  process:*all-processes*)

(defun %interrupt-thread (thread function)
  (process:process-interrupt thread function))

(defun %destroy-thread (thread)
  (process:process-kill thread :force))

(defun %thread-alive-p (thread)
  (process:process-active-p thread))


;;;
;;; Non-recursive locks
;;;

(defstruct (%lock (:constructor make-%lock-internal))
  lock
  lock-argument)

(deftype native-lock () '%lock)

(defun %make-lock (name)
  (let ((lock (process:make-lock name)))
    (make-%lock-internal :lock lock
                         :lock-argument nil)))

(defun %acquire-lock (lock waitp timeout)
  (check-type lock %lock)
  (let ((lock-argument (process:make-lock-argument (%lock-lock lock))))
    (cond (waitp
           (if timeout
               (process:with-timeout (timeout)
                 (process:with-no-other-processes 
                   (process:lock (%lock-lock lock) lock-argument)
                   (setf (%lock-lock-argument lock) lock-argument)
                   t))
               (process:with-no-other-processes 
                 (process:lock (%lock-lock lock) lock-argument)
                 (setf (%lock-lock-argument lock) lock-argument)
                 t)))
          (t
           (process:with-no-other-processes
               (when (process:lock-lockable-p (%lock-lock lock))
                 (process:lock (%lock-lock lock) lock-argument)
                 (setf (%lock-lock-argument lock) lock-argument)
                 t))))))

(defun %release-lock (lock)
  (check-type lock %lock)
  (process:with-no-other-processes
    (process:unlock (%lock-lock lock) (scl:shiftf (%lock-lock-argument lock) nil))))

;;;
;;; Recursive locks
;;;

(defstruct (%recursive-lock (:constructor make-%recursive-lock-internal))
  lock
  lock-arguments)

(deftype native-recursive-lock () '%recursive-lock)

(defun %make-recursive-lock (name)
  (make-%recursive-lock-internal
   :lock (process:make-lock name :recursive t)
   :lock-arguments (make-hash-table :test #'equal)))

(defun %acquire-recursive-lock (lock waitp timeout)
  (check-type lock %recursive-lock)
  (let ((key (cons (incf *thread-recursive-lock-key*) scl:*current-process*))
        (lock-argument (process:make-lock-argument (%recursive-lock-lock lock))))
    (cond (waitp
           (if timeout
               (process:with-timeout (timeout)
                 (process:with-no-other-processes
                   (process:lock (%recursive-lock-lock lock) lock-argument)
                   (setf (gethash key (%recursive-lock-lock-arguments lock)) lock-argument)
                   t))
               (process:with-no-other-processes
                 (process:lock (%recursive-lock-lock lock) lock-argument)
                 (setf (gethash key (%recursive-lock-lock-arguments lock)) lock-argument)
                 t)))
          (t
           (process:with-no-other-processes
             (when (process:lock-lockable-p (%recursive-lock-lock lock))
               (process:lock (%recursive-lock-lock lock) lock-argument)
               (setf (gethash key (%recursive-lock-lock-arguments lock)) lock-argument)
               t))))))

(defun %release-recursive-lock (lock)
  (check-type lock %recursive-lock)
  (let* ((key (cons *thread-recursive-lock-key* scl:*current-process*))
         (lock-argument (gethash key (%recursive-lock-lock-arguments lock))))
    (process:with-no-other-processes
      (prog1
          (process:unlock (%recursive-lock-lock lock) lock-argument)
        (decf *thread-recursive-lock-key*)
        (remhash key (%recursive-lock-lock-arguments lock))))))


;;;
;;; Condition variables
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defstruct (condition-variable
              (:constructor %make-condition-variable (name))
              ;; CONDITION-VARIABLE-P is defined in API-CONDITION-VARIABLES.LISP
              (:predicate nil))
    "Bordeaux-threads implementation of condition variables."
    name
    (waiters nil)))

(defmethod print-object ((cv condition-variable) stream)
  (print-unreadable-object (cv stream :type t :identity t)
    (format stream "~S" (condition-variable-name cv))))

(defun %condition-wait (cv lock timeout)
  (check-type cv condition-variable)
  (check-type lock %lock)
  (process:with-no-other-processes
    (let ((waiter (cons scl:*current-process* nil)))
      (process:atomic-updatef (condition-variable-waiters cv)
                              #'(lambda (waiters)
                                  (append waiters (scl:ncons waiter))))
      (let ((expired? t))
        (unwind-protect
            (progn
              (%release-lock lock)
              (process:block-with-timeout timeout
                                          (format nil "Waiting~@[ on ~A~]"
                                                  (condition-variable-name cv))
                                          #'(lambda (waiter expired?-loc)
                                              (when (not (null (cdr waiter)))
                                                (setf (sys:location-contents expired?-loc) nil)
                                                t))
                                          waiter (sys:value-cell-location 'expired?))
              expired?)
          (unless expired?
            (%acquire-lock lock t nil)))))))

(defun %condition-notify (cv)
  (check-type cv condition-variable)
  (let ((waiter (process:atomic-pop (condition-variable-waiters cv))))
    (when waiter
      (setf (cdr waiter) t)
      (process:wakeup (car waiter)))))

(defun %condition-broadcast (cv)
  (check-type cv condition-variable)
  (loop for waiter in (process:atomic-replacef (condition-variable-waiters cv) nil)
        do
    (setf (cdr waiter) t)
    (process:wakeup (car waiter))))



;;;
;;; Timeouts
;;;

(defmacro with-timeout ((timeout) &body body)
  "Execute `BODY' and signal a condition of type TIMEOUT if the execution of
BODY does not complete within `TIMEOUT' seconds."
  `(with-timeout-internal ,timeout #'(lambda () ,@body)))

(defun with-timeout-internal (timeout function)
  ;; PROCESS:WITH-TIMEOUT either returns NIL on timeout or signals an error which,
  ;; unfortunately, does not have a distinguished type (i.e., it's a SYS:FATAL-ERROR).
  ;; So, rather than try to catch the error and signal our condition, we instead
  ;; ensure the return value from the PROCESS:WITH-TIMEOUT is never NIL if there is
  ;; no timeout. (Sigh)
  (let ((result (process:with-timeout (timeout)
                  (cons 'success (multiple-value-list (funcall function))))))
    (if result
        (values-list (cdr result))
        (error 'timeout :length timeout))))
