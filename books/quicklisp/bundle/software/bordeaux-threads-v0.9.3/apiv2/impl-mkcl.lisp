;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mt:thread)

(defun %make-thread (function name)
  (mt:thread-run-function name function))

(defun %current-thread ()
  mt::*thread*)

(defun %thread-name (thread)
  (mt:thread-name thread))

(defun %join-thread (thread)
  (mt:thread-join thread))

(defun %thread-yield ()
  (mt:thread-yield))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (mt:all-threads))

(defun %interrupt-thread (thread function)
  (mt:interrupt-thread thread function))

(defun %destroy-thread (thread)
  (mt:thread-kill thread))

(defun %thread-alive-p (thread)
  (mt:thread-active-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mp:lock)

(defun %make-lock (name)
  (mp:make-lock :name name))

(mark-not-implemented 'acquire-lock :timeout)
(defun %acquire-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-lock :timeout))
  (mp:get-lock lock waitp))

(defun %release-lock (lock)
  (mp:giveup-lock lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(mp:with-lock (,place) ,@body)))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock ()
  '(and mp:lock (satisfies mp:recursive-lock-p)))

(defun %make-recursive-lock (name)
  (mp:make-lock :name name :recursive t))

(mark-not-implemented 'acquire-recursive-lock :timeout)
(defun %acquire-recursive-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-recursive-lock :timeout))
  (mp:get-lock lock waitp))

(defun %release-recursive-lock (lock)
  (mp:giveup-lock lock))

(mark-not-implemented 'with-recursive-lock-held :timeout)
(defmacro %with-recursive-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-recursive-lock-held :timeout)
      `(mp:with-lock (,place) ,@body)))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'mt:condition-variable)

(defun %make-condition-variable (name)
  (declare (ignore name))
  (mt:make-condition-variable))

(mark-not-implemented 'condition-wait :timeout)
(defun %condition-wait (cv lock timeout)
  (when timeout
    (signal-not-implemented 'condition-wait :timeout))
  (mt:condition-wait cv lock)
  t)

(defun %condition-notify (cv)
  (mt:condition-signal cv))

(defun %condition-broadcast (cv)
  (mt:condition-broadcast cv))
