;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mt:thread)

(defun %make-thread (function name)
  (mt:make-thread function :name name))

(defun %current-thread ()
  (mt:current-thread))

(defun %thread-name (thread)
  (mt:thread-name thread))

(defun %join-thread (thread)
  (mt:thread-join thread))

(defun %thread-yield ()
  (mt:thread-yield))

;;;
;;; Introspection/debugging
;;;

;;; VTZ: mt:list-threads returns all threads that are not garbage collected.
(defun %all-threads ()
  (delete-if-not #'mt:thread-active-p (mt:list-threads)))

(defun %interrupt-thread (thread function)
  (mt:thread-interrupt thread :function function))

(defun %destroy-thread (thread)
  (mt:thread-interrupt thread :function t))

(defun %thread-alive-p (thread)
  (mt:thread-active-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock ()
  'mt:mutex)

(defun %make-lock (name)
  (mt:make-mutex :name name))

(mark-not-implemented 'acquire-lock :timeout)
(defun %acquire-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-lock :timeout))
  (mt:mutex-lock lock :timeout (if waitp nil 0)))

(defun %release-lock (lock)
  (mt:mutex-unlock lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(mt:with-mutex-lock (,place) ,@body)))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock ()
  '(and mt:mutex (satisfies mt:mutex-recursive-p)))

(defun %make-recursive-lock (name)
  (mt:make-mutex :name name :recursive-p t))

(mark-not-implemented 'acquire-recursive-lock :timeout)
(defun %acquire-recursive-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-recursive-lock :timeout))
  (%acquire-lock lock waitp nil))

(defun %release-recursive-lock (lock)
  (%release-lock lock))

(mark-not-implemented 'with-recursive-lock-held :timeout)
(defmacro %with-recursive-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-recursive-lock-held :timeout)
      `(mt:with-mutex-lock (,place) ,@body)))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'mt:exemption)

(defun %make-condition-variable (name)
  (mt:make-exemption :name name))

(defun %condition-wait (cv lock timeout)
  (mt:exemption-wait cv lock :timeout timeout))

(defun %condition-notify (cv)
  (mt:exemption-signal cv))

(defun %condition-broadcast (cv)
  (mt:exemption-broadcast cv))


;;;
;;; Timeouts
;;;

(defmacro with-timeout ((timeout) &body body)
  (once-only (timeout)
    `(mt:with-timeout (,timeout (error 'timeout :length ,timeout))
       ,@body)))
