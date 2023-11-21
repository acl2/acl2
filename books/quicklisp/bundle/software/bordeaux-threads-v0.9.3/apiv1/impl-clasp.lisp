;;;; -*- indent-tabs-mode: nil -*-

#|
Copyright 2006, 2007 Greg Pfeil

Distributed under the MIT license (see LICENSE file)
|#

(in-package #:bordeaux-threads)

;;; documentation on the ECL Multiprocessing interface can be found at
;;; http://ecls.sourceforge.net/cgi-bin/view/Main/MultiProcessing

(deftype thread ()
  'mp:process)

;;; Thread Creation

(defun %make-thread (function name)
  (mp:process-run-function name function bordeaux-threads:*default-special-bindings*))

(defun current-thread ()
  mp:*current-process*)

(defun threadp (object)
  (typep object 'mp:process))

(defun thread-name (thread)
  (mp:process-name thread))

;;; Resource contention: locks and recursive locks

(deftype lock () 'mp:mutex)

(deftype recursive-lock ()
  '(and mp:mutex (satisfies mp:recursive-lock-p)))

(defun lock-p (object)
  (typep object 'mp:mutex))

(defun recursive-lock-p (object)
  (and (typep object 'mp:mutex)
       (mp:recursive-lock-p object)))

(defun make-lock (&optional name)
  (mp:make-lock :name (or name :anonymous)))

(defun acquire-lock (lock &optional (wait-p t))
  (mp:get-lock lock wait-p))

(defun release-lock (lock)
  (mp:giveup-lock lock))


(defmacro with-lock-held ((place) &body body)
  `(mp:with-lock (,place) ,@body))

(defun make-recursive-lock (&optional name)
  (mp:make-recursive-mutex (or name :anonymous-recursive-lock)))

(defun acquire-recursive-lock (lock &optional (wait-p t))
  (mp:get-lock lock wait-p))

(defun release-recursive-lock (lock)
  (mp:giveup-lock lock))

(defmacro with-recursive-lock-held ((place) &body body)
  `(mp:with-lock (,place) ,@body))

;;; Resource contention: condition variables

(defun make-condition-variable (&key name)
  (declare (ignore name))
  (mp:make-condition-variable))

(defun condition-wait (condition-variable lock &key timeout)
  (if timeout
      (mp:condition-variable-timedwait condition-variable lock timeout)
      (mp:condition-variable-wait condition-variable lock))
  t)

(defun condition-notify (condition-variable)
  (mp:condition-variable-signal condition-variable))

(defun thread-yield ()
  (mp:process-yield))

;;; Introspection/debugging

(defun all-threads ()
  (mp:all-processes))

(defun interrupt-thread (thread function &rest args)
  (flet ((apply-function ()
           (if args
               (named-lambda %interrupt-thread-wrapper ()
                 (apply function args))
               function)))
    (declare (dynamic-extent #'apply-function))
    (mp:interrupt-process thread (apply-function))))

(defun destroy-thread (thread)
  (signal-error-if-current-thread thread)
  (mp:process-kill thread))

(defun thread-alive-p (thread)
  (mp:process-active-p thread))

(defun join-thread (thread)
  (mp:process-join thread))

(mark-supported)
