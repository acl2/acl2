;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'thread:thread)

(defun %make-thread (function name)
  (thread:thread-create function :name name))

(defun %current-thread ()
  thread:*thread*)

(defun %thread-name (thread)
  (thread:thread-name thread))

(defun %join-thread (thread)
  (mp:process-wait (format nil "Waiting for thread ~A to complete" thread)
                   (named-lambda %thread-completed-p ()
                     (not (mp:process-alive-p thread)))))

(defun %thread-yield ()
  (mp:process-yield))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (mp:all-processes))

(defun %interrupt-thread (thread function)
  (thread:thread-interrupt thread function))

(defun %destroy-thread (thread)
  (thread:destroy-thread thread))

(defun %thread-alive-p (thread)
  (mp:process-alive-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'thread:lock)

(defun %make-lock (name)
  (thread:make-lock name))

(mark-not-implemented 'acquire-lock :timeout)
(defun %acquire-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-lock :timeout))
  (thread::acquire-lock lock nil wait-p))

(defun %release-lock (lock)
  (thread::release-lock lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(thread:with-lock-held (,place) ,@body)))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock () 'thread:recursive-lock)

(defun %make-recursive-lock (name)
  (thread:make-lock name :type :recursive))

(mark-not-implemented 'acquire-recursive-lock)
(defun %acquire-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'acquire-recursive-lock))

(mark-not-implemented 'release-recursive-lock)
(defun %release-recursive-lock (lock)
  (declare (ignore lock))
  (signal-not-implemented 'release-recursive-lock))

(mark-not-implemented 'with-recursive-lock-held :timeout)
(defmacro %with-recursive-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-recursive-lock-held :timeout)
      `(thread:with-lock-held (,place)
         ,@body)))


;;; 
;;; Condition variables
;;;

(deftype condition-variable ()
  'thread:cond-var)

(defun %make-condition-variable (name)
  (thread:make-cond-var name))

(defun %condition-wait (cv lock timeout)
  (if timeout
      (thread:cond-var-timedwait cv lock timeout)
      (thread:cond-var-wait cv lock)))

(defun %condition-notify (cv)
  (thread:cond-var-signal cv))

(defun %condition-broadcast (cv)
  (thread:cond-var-broadcast v))
