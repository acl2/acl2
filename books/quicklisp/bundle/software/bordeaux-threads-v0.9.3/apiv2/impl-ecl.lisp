;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

(eval-when (:compile-toplevel :execute)
  (when (>= ext:+ecl-version-number+ 230909)
    (pushnew :has-timeouts *features*)))

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mp:process)

(defun %make-thread (function name)
  (mp:process-run-function name function))

(defun %current-thread ()
  mp:*current-process*)

(defun %thread-name (thread)
  ;; Some system threads have symbols for a name.
  (string (mp:process-name thread)))

(defun %join-thread (thread)
  (mp:process-join thread))

(defun %thread-yield ()
  (mp:process-yield))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (mp:all-processes))

(defun %interrupt-thread (thread function)
  (mp:interrupt-process thread function))

(defun %destroy-thread (thread)
  (mp:process-kill thread))

(defun %thread-alive-p (thread)
  (mp:process-active-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mp:lock)

(defun %make-lock (name)
  (mp:make-lock :name name))

#-has-timeouts
(progn
  (mark-not-implemented 'acquire-lock :timeout)
  (defun %acquire-lock (lock waitp timeout)
    (when timeout
      (signal-not-implemented 'acquire-lock :timeout))
    (mp:get-lock lock waitp)))

#+has-timeouts
(defun %acquire-lock (lock waitp timeout)
  (mp:get-lock lock (cond ((not waitp) nil)
                          (timeout timeout)
                          (t t))))

(defun %release-lock (lock)
  (mp:giveup-lock lock))

#-has-timeouts
(progn
  (mark-not-implemented 'with-lock-held :timeout)
  (defmacro %with-lock ((place timeout) &body body)
    (if timeout
        `(signal-not-implemented 'with-lock-held :timeout)
        `(mp:with-lock (,place) ,@body))))

#+has-timeouts
(defmacro %with-lock ((place timeout) &body body)
  `(mp:with-lock (,place :wait-form (or ,timeout t))
     ,@body))

;;;
;;; Recursive locks
;;;

(deftype native-recursive-lock ()
  '(and mp:lock (satisfies mp:recursive-lock-p)))

(defun %make-recursive-lock (name)
  (mp:make-lock :name name :recursive t))

#-has-timeouts
(progn
  (mark-not-implemented 'acquire-recursive-lock :timeout)
  (defun %acquire-recursive-lock (lock waitp timeout)
    (when timeout
      (signal-not-implemented 'acquire-recursive-lock :timeout))
    (mp:get-lock lock waitp)))

#+has-timeouts
(defun %acquire-recursive-lock (lock waitp timeout)
  (mp:get-lock lock (cond ((not waitp) nil)
                          (timeout timeout)
                          (t t))))

(defun %release-recursive-lock (lock)
  (mp:giveup-lock lock))

#-has-timeouts
(progn
  (mark-not-implemented 'with-recursive-lock-held :timeout)
  (defmacro %with-recursive-lock ((place timeout) &body body)
    (if timeout
        `(signal-not-implemented 'with-recursive-lock-held :timeout)
        `(mp:with-lock (,place) ,@body))))

#+has-timeouts
(defmacro %with-recursive-lock ((place timeout) &body body)
  `(mp:with-lock (,place :wait-form (or ,timeout t))
     ,@body))


;;;
;;; Semaphores
;;;

(deftype semaphore () 'mp:semaphore)

(defun %make-semaphore (name count)
  (mp:make-semaphore :name name :count count))

(defun %signal-semaphore (semaphore count)
  (mp:signal-semaphore semaphore count))

(defun %wait-on-semaphore (semaphore timeout)
  (cond
    ((null timeout)
     (mp:wait-on-semaphore semaphore)
     t)
    ((plusp timeout)
     #-has-timeouts
     (handler-case
         (with-timeout (timeout)
           (mp:wait-on-semaphore semaphore)
           t)
       (timeout () nil))
     #+has-timeouts
     (mp:semaphore-wait semaphore 1 timeout))
    (t
     (if (mp:try-get-semaphore semaphore) t nil))))


;;;
;;; Condition variables
;;;

(deftype condition-variable ()
  'mp:condition-variable)

(defun %make-condition-variable ( name)
  (declare (ignore name))
  (mp:make-condition-variable))

(defun %condition-wait (cv lock timeout)
  (if timeout
      #-has-timeouts
      (handler-case
          (with-timeout (timeout)
            (mp:condition-variable-wait cv lock))
        (timeout ()
          (%acquire-lock lock t nil)
          nil))
      #+has-timeouts
      (mp:condition-variable-timedwait cv lock timeout)
      (mp:condition-variable-wait cv lock)))

(defun %condition-notify (cv)
  (mp:condition-variable-signal cv))

(defun %condition-broadcast (cv)
  (mp:condition-variable-broadcast cv))

(eval-when (:compile-toplevel :execute)
  (setf *features* (remove :has-timeouts *features*)))
