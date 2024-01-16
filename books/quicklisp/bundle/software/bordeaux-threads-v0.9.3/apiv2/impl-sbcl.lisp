;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'sb-thread:thread)

(defun %make-thread (function name)
  (sb-thread:make-thread function :name name))

(defun %current-thread ()
  sb-thread:*current-thread*)

(defun %thread-name (thread)
  (sb-thread:thread-name thread))

(defun %join-thread (thread)
  (ignore-some-conditions (sb-thread:join-thread-error)
    (sb-thread:join-thread thread)))

(defun %thread-yield ()
  (sb-thread:thread-yield))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (sb-thread:list-all-threads))

(defun %interrupt-thread (thread function)
  (sb-thread:interrupt-thread thread function))

(defun %destroy-thread (thread)
  (sb-thread:terminate-thread thread))

(defun %thread-alive-p (thread)
  (sb-thread:thread-alive-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock ()
  'sb-thread:mutex)

(defun %make-lock (name)
  (sb-thread:make-mutex :name name))

(defun %acquire-lock (lock waitp timeout)
  (sb-thread:grab-mutex lock :waitp waitp :timeout timeout))

(defun %release-lock (lock)
  (sb-thread:release-mutex lock))

(defmacro %with-lock ((place timeout) &body body)
  `(sb-thread:with-mutex (,place :timeout ,timeout) ,@body))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock ()
  'sb-thread:mutex)

(defun %make-recursive-lock (name)
  (sb-thread:make-mutex :name name))

(mark-not-implemented 'acquire-recursive-lock)
(defun %acquire-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'acquire-recursive-lock))

(mark-not-implemented 'release-recursive-lock)
(defun %release-recursive-lock (lock)
  (declare (ignore lock))
  (signal-not-implemented 'release-recursive-lock))

(defmacro %with-recursive-lock ((place timeout) &body body)
  `(sb-thread:with-recursive-lock (,place :timeout ,timeout)
     ,@body))


;;;
;;; Semaphores
;;;

(deftype semaphore ()
  'sb-thread:semaphore)

(defun %make-semaphore (name count)
  (sb-thread:make-semaphore :name name :count count))

(defun %signal-semaphore (semaphore count)
  (sb-thread:signal-semaphore semaphore count))

(defun %wait-on-semaphore (semaphore timeout)
  (cond
    ((and timeout (zerop timeout))
     (sb-thread:try-semaphore semaphore))
    (t
     (if (sb-thread:wait-on-semaphore semaphore :timeout timeout)
         t nil))))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'sb-thread:waitqueue)

(defun %make-condition-variable (name)
  (sb-thread:make-waitqueue :name name))

(defun %condition-wait (cv lock timeout)
  (let ((success
          (sb-thread:condition-wait cv lock :timeout timeout)))
    (when (not success)
      (%acquire-lock lock t nil))
    success))

(defun %condition-notify (cv)
  (sb-thread:condition-notify cv))

(defun %condition-broadcast (cv)
  (sb-thread:condition-broadcast cv))


;;;
;;; Timeouts
;;;

(defmacro with-timeout ((timeout) &body body)
  `(sb-ext:with-timeout ,timeout
     ,@body))
