;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

#+(or lispworks4 lispworks5)
(error 'bordeaux-threads-error
       :message "Threading not supported")

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mp:process)

(defun %start-multiprocessing ()
  (mp:initialize-multiprocessing))

(defun %make-thread (function name)
  (mp:process-run-function name nil function))

(defun %current-thread ()
  (mp:get-current-process))

(defun %thread-name (thread)
  (mp:process-name thread))

(defun %join-thread (thread)
  (mp:process-join thread))

(defun %thread-yield ()
  (mp:process-allow-scheduling))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (mp:list-all-processes))

(defun %interrupt-thread (thread function)
  (mp:process-interrupt thread function))

(defun %destroy-thread (thread)
  (mp:process-kill thread))

(defun %thread-alive-p (thread)
  (mp:process-alive-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mp:lock)

(defun %make-lock (name)
  (mp:make-lock :name name :recursivep nil))

(defun %acquire-lock (lock waitp timeout)
  (mp:process-lock lock "Lock" (if waitp timeout 0)))

(defun %release-lock (lock)
  (mp:process-unlock lock))

(defmacro %with-lock ((place timeout) &body body)
  `(mp:with-lock (,place nil ,timeout) ,@body))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock ()
  '(and mp:lock (satisfies mp:lock-recursive-p)))

(defun %make-recursive-lock (name)
  (mp:make-lock :name name :recursivep t))

(defun %acquire-recursive-lock (lock waitp timeout)
  (%acquire-lock lock waitp timeout))

(defun %release-recursive-lock (lock)
  (%release-lock lock))

(defmacro %with-recursive-lock ((place timeout) &body body)
  `(mp:with-lock (,place nil ,timeout) ,@body))


;;;
;;; Semaphores
;;;

(deftype semaphore ()
  'mp:semaphore)

(defun %make-semaphore (name count)
  (mp:make-semaphore :name name :count count))

(defun %signal-semaphore (semaphore count)
  (mp:semaphore-release semaphore :count count))

(defun %wait-on-semaphore (semaphore timeout)
  (if (mp:semaphore-acquire semaphore :timeout timeout :count 1)
      t nil))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'mp:condition-variable)

(defun %make-condition-variable (name)
  (mp:make-condition-variable :name name))

(defun %condition-wait (cv lock timeout)
  (mp:condition-variable-wait cv lock :timeout timeout))

(defun %condition-notify (cv)
  (mp:condition-variable-signal cv))

(defun %condition-broadcast (cv)
  (mp:condition-variable-broadcast cv))
