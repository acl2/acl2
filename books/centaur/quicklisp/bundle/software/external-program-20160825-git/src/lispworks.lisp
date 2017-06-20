;;; Copyright 2006-2008 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;; Documentation at http://www.lispworks.com/documentation/lwl42/LWRM-U/html/lwref-u-421.htm
;;; The docs say that :ENVIRONMENT should be an alist, but it should actually be
;;; a list of proper lists.

(defstruct external-process
  process-id
  inputp
  outputp
  stream
  error-stream)

(defun convert-rest (rest)
  (setf (getf rest :error-output) (getf rest :error))
  (remf rest :error)
  (remf rest :replace-environment-p)
  (setf (getf rest :environment)
        (mapcar (lambda (var) (list (car var) (cdr var)))
                (getf rest :environment)))
  rest)

(defmethod run
    (program args &rest rest &key replace-environment-p &allow-other-keys)
  (values :exited
          (apply #'sys:run-shell-command
                 (make-shell-string program args nil replace-environment-p)
                 :wait t
                 (convert-rest rest))))

(defmethod start
    (program args
     &rest rest &key input output replace-environment-p &allow-other-keys)
  (multiple-value-bind (stream error-stream process-id)
      (apply #'sys:run-shell-command
                 (make-shell-string program args nil replace-environment-p)
                 :wait nil
                 :save-exit-status (not (or (eq input :stream)
                                            (eq output :stream)))
                 (convert-rest rest))
    (make-external-process :process-id process-id
                           :inputp (eq input :stream)
                           :outputp (eq output :stream)
                           :stream stream
                           :error-stream error-stream)))

(defmethod process-id ((process external-process))
  (external-process-process-id process))

(defmethod process-input-stream ((process external-process))
  (if (external-process-inputp process)
      (external-process-stream process)))

(defmethod process-output-stream ((process external-process))
  (if (external-process-outputp process)
      (external-process-stream process)))

(defmethod process-error-stream ((process external-process))
  (external-process-error-stream process))

(defmethod process-status ((process external-process))
  (let ((status-code
         #+lispworks6
         (sys:pid-exit-status (external-process-process-id
                               process))
         #-lispworks6
         (sys:pipe-exit-status (or (external-process-stream
                                    process)
                                   (external-process-error-stream
                                    process))
                               :wait nil)))
    (values (if status-code :exited :running) status-code)))

(defmethod process-p ((process external-process))
  t)
