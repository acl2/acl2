;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'ccl:process)

(defun %make-thread (function name)
  (ccl:process-run-function name function))

(defun %current-thread ()
  ccl:*current-process*)

(defun %thread-name (thread)
  (ccl:process-name thread))

(defun %join-thread (thread)
  (ccl:join-process thread))

(defun %thread-yield ()
  (ccl:process-allow-schedule))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (ccl:all-processes))

(defun %interrupt-thread (thread function)
  (ccl:process-interrupt thread function))

(defun %destroy-thread (thread)
  (ccl:process-kill thread))

(defun %thread-alive-p (thread)
  (not (ccl:process-exhausted-p thread)))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'ccl:lock)

(defun %make-lock (name)
  (ccl:make-lock name))

(mark-not-implemented 'acquire-lock :timeout)
(defun %acquire-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-lock :timeout))
  ;; This is not guaranteed to work all the times, but that's OK.
  (when (eql (ccl::%%lock-owner lock) (%current-thread))
    (bt-error "Attempted recursive acquisition of lock: ~A" lock))
  (if waitp
      (ccl:grab-lock lock)
      (ccl:try-lock lock)))

(defun %release-lock (lock)
  (ccl:release-lock lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (declare (ignorable place timeout))
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(ccl:with-lock-grabbed (,place)
         ,@body)))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock () 'ccl:lock)

(defun %make-recursive-lock (name)
  (ccl:make-lock name))

(mark-not-implemented 'acquire-recursive-lock :timeout)
(defun %acquire-recursive-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-recursive-lock :timeout))
  (if waitp
      (ccl:grab-lock lock)
      (ccl:try-lock lock)))

(defun %release-recursive-lock (lock)
  (ccl:release-lock lock))

(mark-not-implemented 'with-recursive-lock-held :timeout)
(defmacro %with-recursive-lock ((place timeout) &body body)
  (declare (ignorable place timeout))
  (if timeout
      `(signal-not-implemented 'with-recursive-lock-held :timeout)
      `(ccl:with-lock-grabbed (,place)
         ,@body)))


;;;
;;; Semaphores
;;;

(deftype semaphore () 'ccl:semaphore)

(defun %make-semaphore (name count)
  (declare (ignore name))
  (ccl:make-semaphore :count count))

(defun %signal-semaphore (semaphore count)
  (dotimes (c count) (ccl:signal-semaphore semaphore)))

(defun %wait-on-semaphore (semaphore timeout)
  (if timeout
      (ccl:timed-wait-on-semaphore semaphore timeout)
      (ccl:wait-on-semaphore semaphore)))


;;;
;;; Condition variables
;;;

;;; Clozure doesn't have native condition variables.
;;; We'll use the implementation in
;;; impl-condition-variables-semaphores.lisp
