;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mezzano.supervisor:thread)

(defun %make-thread (function name)
  (mezzano.supervisor:make-thread function :name name))

(defun %current-thread ()
  (mezzano.supervisor:current-thread))

(defun %thread-name (thread)
  (mezzano.supervisor:thread-name thread))

(defun %join-thread (thread)
  ;; THREAD-JOIN can return non-lists if the thread was destroyed.
  (let ((values (mezzano.supervisor:thread-join thread)))
    (if (listp values)
        (values-list values)
        nil)))

(defun %thread-yield ()
  (mezzano.supervisor:thread-yield))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (mezzano.supervisor:all-threads))

(defun %interrupt-thread (thread function)
  (mezzano.supervisor:establish-thread-foothold thread function))

(defun %destroy-thread (thread)
  (mezzano.supervisor:terminate-thread thread))

(defun %thread-alive-p (thread)
  (not (eql (mezzano.supervisor:thread-state thread) :dead)))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mezzano.supervisor:mutex)

(defun %make-lock (name)
  (mezzano.supervisor:make-mutex name))

(mark-not-implemented 'acquire-lock :timeout)
(defun %acquire-lock (lock waitp timeout)
  (when timeout
    (signal-not-implemented 'acquire-lock :timeout))
  (mezzano.supervisor:acquire-mutex lock waitp))

(defun %release-lock (lock)
  (mezzano.supervisor:release-mutex lock))

(mark-not-implemented 'with-lock-held :timeout)
(defmacro %with-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-lock-held :timeout)
      `(mezzano.supervisor:with-mutex (,place) ,@body)))

;;;
;;; Recursive locks
;;;

(defstruct (%recursive-lock
             (:constructor %make-recursive-lock-internal (mutex)))
  mutex
  (depth 0))

(deftype native-recursive-lock () '%recursive-lock)

(defun %make-recursive-lock (name)
  (%make-recursive-lock-internal (%make-lock name)))

(mark-not-implemented 'acquire-recursive-lock)
(defun %acquire-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'acquire-recursive-lock))

(release-not-implemented 'release-recursive-lock)
(defun %release-recursive-lock (lock)
  (declare (ignore lock))
  (signal-not-implemented 'release-recursive-lock))

(defun call-with-recursive-lock-held (lock function)
  (cond ((mezzano.supervisor:mutex-held-p
          (%recursive-lock-mutex lock))
         (unwind-protect
              (progn (incf (%recursive-lock-depth lock))
                     (funcall function))
           (decf (%recursive-lock-depth lock))))
        (t
         (mezzano.supervisor:with-mutex ((%recursive-lock-mutex lock))
           (multiple-value-prog1
               (funcall function)
             (assert (zerop (%recursive-lock-depth lock))))))))

(mark-not-implemented 'with-recursive-lock-held :timeout)
(defmacro %with-recursive-lock ((place timeout) &body body)
  (if timeout
      `(signal-not-implemented 'with-recursive-lock-held :timeout)
      `(call-with-recursive-lock-held ,place (lambda () ,@body))))


;;;
;;; Semaphores
;;;

(deftype semaphore ()
  'mezzano.sync:semaphore)

(defun %make-semaphore (name count)
  (mezzano.sync:make-semaphore :name name :value count))

(defun %signal-semaphore (semaphore count)
  (dotimes (c count) (mezzano.sync:semaphore-up semaphore)))

(defun %wait-on-semaphore (semaphore timeout)
  (mezzano.supervisor:event-wait-for (semaphore :timeout timeout)
    (mezzano.sync:semaphore-down semaphore :wait-p nil)))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'mezzano.supervisor:condition-variable)

(defun %make-condition-variable (name)
  (mezzano.supervisor:make-condition-variable name))

(defun %condition-wait (cv lock timeout)
  (mezzano.supervisor:condition-wait cv lock timeout))

(defun %condition-notify (cv)
  (mezzano.supervisor:condition-notify cv))

(mark-not-implemented 'condition-broadcast)
(defun %condition-broadcast (cv)
  (declare (ignore cv))
  (signal-not-implemented 'condition-broadcast))
