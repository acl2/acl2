;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'mp::process)

(defun %start-multiprocessing ()
  (mp::startup-idle-and-top-level-loops))

(defun %make-thread (function name)
  ;; CMUCL doesn't like NIL names.
  (mp:make-process function :name (or name "")))

(defun %current-thread ()
  mp:*current-process*)

(defun %thread-name (thread)
  (mp:process-name thread))

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
  (mp:process-interrupt thread function))

(defun %destroy-thread (thread)
  (mp:destroy-process thread))

(defun %thread-alive-p (thread)
  (mp:process-active-p thread))


;;;
;;; Non-recursive locks
;;;

(deftype native-lock () 'mp::error-check-lock)

(defun %make-lock (name)
  (mp:make-lock name :kind :error-check))

(defun %acquire-lock (lock waitp timeout)
  (if (and waitp (null timeout))
      (mp::lock-wait lock "Lock wait")
      (mp::lock-wait-with-timeout lock "Lock wait"
                                  (if waitp timeout 0))))

(defun %release-lock (lock)
  (setf (mp::lock-process lock) nil))

(defmacro %with-lock ((place timeout) &body body)
  `(mp:with-lock-held (,place "Lock wait"  :timeout ,timeout) ,@body))

;;;
;;; Recursive locks
;;;

;;; Note that the locks _are_ recursive, but not "balanced", and only
;;; checked if they are being held by the same process by with-lock-held.
;;; The default with-lock-held in sort of works, in that
;;; it will wait for recursive locks by the same process as well.

(deftype native-recursive-lock () 'mp::recursive-lock)

(defun %make-recursive-lock (name)
  (mp:make-lock name :kind :recursive))

(defun %acquire-recursive-lock (lock waitp timeout)
  (%acquire-lock lock waitp timeout))

(defun %release-recursive-lock (lock)
  (%release-lock lock))

(defmacro %with-recursive-lock ((place timeout) &body body)
  `(mp:with-lock-held (,place "Lock Wait" :timeout ,timeout) ,@body))


;;;
;;; Condition variables
;;;

;;; There's some stuff in x86-vm.lisp that might be worth investigating
;;; whether to build on. There's also process-wait and friends.

(defstruct (condition-variable
            (:constructor %make-condition-variable (name)))
  "Bordeaux-threads implementation of condition variables."
  name
  (lock (%make-lock nil))
  active)

(defmethod print-object ((cv condition-variable) stream)
  (print-unreadable-object (cv stream :type t :identity t)
    (format stream "~S" (condition-variable-name cv))))

(mark-not-implemented 'condition-wait :timeout)
(defun %condition-wait (cv lock timeout)
  (check-type cv condition-variable)
  (when timeout
    (signal-not-implemented 'condition-wait :timeout))
  (%with-lock ((condition-variable-lock cv) nil)
    (setf (condition-variable-active cv) nil))
  (%release-lock lock)
  (mp:process-wait "Condition Wait"
                   #'(lambda () (condition-variable-active cv)))
  (%acquire-lock lock t nil)
  t)

(defun %condition-notify (cv)
  (check-type cv condition-variable)
  (%with-lock ((condition-variable-lock cv) nil)
    (setf (condition-variable-active cv) t))
  (thread-yield))

(mark-not-implemented 'condition-broadcast)
(defun %condition-broadcast (cv)
  (declare (ignore cv))
  (signal-not-implemented 'condition-broadcast))


;;;
;;; Timeouts
;;;

(defmacro with-timeout ((timeout) &body body)
  (once-only (timeout)
    `(mp:with-timeout (,timeout (error 'timeout :length ,timeout))
       ,@body)))
