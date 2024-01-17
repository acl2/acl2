;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'ccl::process)

(defun %make-thread (function name)
  (ccl:process-run-function name function))

(defun %current-thread ()
  ccl:*current-process*)

(defun %thread-name (thread)
  (ccl:process-name thread))

(mark-not-implemented 'join-thread)
(defun %thread-join (thread)
  (declare (ignore thread))
  (signal-not-implemented 'join-thread))

(defun %thread-yield ()
  (ccl:process-allow-schedule))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  ccl:*all-processes*)

(defun %interrupt-thread (thread function)
  (ccl:process-interrupt thread function))

(defun %destroy-thread (thread)
  (ccl:process-kill thread))

(mark-not-implemented 'thread-alive-p)
(defun %thread-alive-p (thread)
  (declare (ignore thread))
  (signal-not-implemented 'thread-alive-p))


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
  (if waitp
      (ccl:process-lock lock ccl:*current-process*)
      ;; this is broken, but it's better than a no-op
      (ccl:without-interrupts
        (when (null (ccl::lock.value lock))
          (ccl:process-lock lock ccl:*current-process*)))))

(defun %release-lock (lock)
  (ccl:process-unlock lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(ccl:with-lock-grabbed (,place) ,@body)))

;;;
;;; Recursive locks
;;;

(mark-not-implemented 'acquire-recursive-lock)
(defun %acquire-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'acquire-recursive-lock))


;;;
;;; Condition variables
;;;

(mark-not-implemented make-condition-variable)
(defun %make-condition-variable (name)
  (declare (ignore name))
  (signal-not-implemented make-condition-variable))
