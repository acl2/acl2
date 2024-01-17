;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

#-(version>= 9)
(error 'bordeaux-threads-error
       :message "Threading not supported")

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mp:process)

(defun %start-multiprocessing ()
  (mp:start-scheduler))

(defun %make-thread (function name)
  (mp:process-run-function name function))

(defun %current-thread ()
  mp:*current-process*)

(defun %thread-name (thread)
  (mp:process-name thread))

(defun %join-thread (thread)
  #+smp
  (mp:process-join thread)
  #-smp
  (mp:process-wait (format nil "Waiting for thread ~A to complete" thread)
                   (complement #'mp:process-alive-p)
                   thread))

(defun %thread-yield ()
  (mp:process-allow-schedule))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  mp:*all-processes*)

(defun %interrupt-thread (thread function)
  (mp:process-interrupt thread function))

(defun %destroy-thread (thread)
  (mp:process-kill thread))

(defun %thread-alive-p (thread)
  (mp:process-alive-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mp:process-lock)

(defun %make-lock (name)
  (mp:make-process-lock :name name))

(defun %acquire-lock (lock waitp timeout)
  (mp:process-lock lock mp:*current-process* "Lock"
                   (if waitp timeout 0)))

(defun %release-lock (lock)
  (mp:process-unlock lock))

(defmacro %with-lock ((place timeout) &body body)
  `(mp:with-process-lock (,place :timeout ,timeout :norecursive t)
     ,@body))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock () 'mp:process-lock)

(defun %make-recursive-lock (name)
  (mp:make-process-lock :name name))

(mark-not-implemented 'acquire-recursive-lock)
(defun %acquire-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'acquire-recursive-lock))

(mark-not-implemented 'release-recursive-lock)
(defun %release-recursive-lock (lock)
  (declare (ignore lock))
  (signal-not-implemented 'release-recursive-lock))

(defmacro %with-recursive-lock ((place timeout) &body body)
  `(mp:with-process-lock (,place :timeout ,timeout)
     ,@body))


;;;
;;; Timeouts
;;;

(defmacro with-timeout ((timeout) &body body)
  (once-only (timeout)
    `(mp:with-timeout (,timeout (error 'timeout :length ,timeout))
       ,@body)))


;;;
;;; Semaphores
;;;

(defstruct (semaphore
            (:constructor %%make-semaphore (name)))
  "Bordeaux-threads implementation of semaphores."
  name
  (gate (mp:make-gate nil)))

(defmethod print-object ((sem semaphore) stream)
  (print-unreadable-object (sem stream :type t :identity t)
    (format stream "~S" (semaphore-name sem))))

(defun %make-semaphore (name count)
  (let ((sem (%%make-semaphore name)))
    (%signal-semaphore sem count)
    sem))

(defun %signal-semaphore (semaphore count)
  (dotimes (i count)
    (mp:put-semaphore (semaphore-gate semaphore))))

(defun %wait-on-semaphore (semaphore timeout)
  (cond
    (timeout
     ;; Timeouts that are too small expire immediately.
     ;; 100ms should suffice.
     (when (< timeout 0.1)
       (setf timeout 0.1))
     (handler-case
         (with-timeout (timeout)
           (mp:get-semaphore (semaphore-gate semaphore))
           t)
       (timeout () nil)))
    (t
     (mp:get-semaphore (semaphore-gate semaphore))
     t)))


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
