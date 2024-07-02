;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'threads:thread)

(defun %make-thread (function name)
  (declare (ignore name))
  (threads:create-thread function))

(defun %current-thread ()
  threads:*current-thread*)

(defun %thread-name (thread)
  (declare (ignore thread))
  nil)

(mark-not-implemented 'join-thread)
(defun %join-thread (thread)
  (declare (ignore thread))
  (signal-not-implemented 'join-thread))

(mark-not-implemented 'thread-yield)
(defun %thread-yield ()
  (declare (ignore thread))
  (signal-not-implemented 'thread-yield))

;;;
;;; Introspection/debugging
;;;

(mark-not-implemented 'all-threads)
(defun %all-threads ()
  (declare (ignore thread))
  (signal-not-implemented 'all-threads))

(mark-not-implemented 'interrupt-thread)
(defun %interrupt-thread (thread function)
  (declare (ignore thread))
  (signal-not-implemented 'interrupt-thread))

(defun %destroy-thread (thread)
  (threads:terminate-thread thread))

(mark-not-implemented 'thread-alive-p)
(defun %thread-alive-p (thread)
  (declare (ignore thread))
  (signal-not-implemented 'thread-alive-p))


;;;
;;; Locks
;;;

(mark-not-implemented 'make-lock)
(defun %make-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'make-lock))

(mark-not-implemented 'make-recursive-lock)
(defun %make-recursive-lock (lock waitp timeout)
  (declare (ignore lock waitp timeout))
  (signal-not-implemented 'make-recursive-lock))


;;;
;;; Condition variables
;;;

(mark-not-implemented 'make-condition-variable)
(defun %make-condition-variable (name)
  (declare (ignore name))
  (signal-not-implemented 'make-condition-variable))
