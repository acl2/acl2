;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;;; Documentation at http://ccl.clozure.com/ccl-documentation.html#External-Program-Dictionary(

(defun convert-environment (rest)
  (remf rest :replace-environment-p)
  (rename-parameter :environment :env rest))

(defmethod run
    (program args &rest rest &key replace-environment-p &allow-other-keys)
  (when replace-environment-p
    (setf args (append (list "-i" program "PATH=''") args))
    (setf program "env"))
  (process-status (apply #'ccl:run-program
                         program (stringify-args args) :wait t
                         (convert-environment rest))))

(defmethod start
    (program args &rest rest &key replace-environment-p &allow-other-keys)
  (when replace-environment-p
    (setf program "env")
    (setf args (append (list "-i" program) args)))
  (apply #'ccl:run-program
         program (stringify-args args) :wait nil (convert-environment rest)))

(defmethod signal-process ((process ccl:external-process) signal)
  (ccl:signal-external-process process
                               (if (keywordp signal)
                                   (cdr (assoc signal *signal-mapping*))
                                   signal)))

(defmethod process-id ((process ccl:external-process))
  (ccl:external-process-id process))

(defmethod process-input-stream ((process ccl:external-process))
  (ccl:external-process-input-stream process))

(defmethod process-output-stream ((process ccl:external-process))
  (ccl:external-process-output-stream process))

(defmethod process-error-stream ((process ccl:external-process))
  (ccl:external-process-error-stream process))

(defmethod process-status ((process ccl:external-process))
  (ccl:external-process-status process))

(defmethod process-p ((process ccl:external-process))
  t)
