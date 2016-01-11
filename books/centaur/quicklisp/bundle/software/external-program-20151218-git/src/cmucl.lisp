;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;; Documentation at http://common-lisp.net/project/cmucl/doc/cmu-user/extensions.html#toc45

(defun convert-environment (rest environment replace-environment-p)
  (let ((env (mapcar (lambda (var) (cons (intern (car var) :keyword) (cdr var)))
                     environment)))
    (setf (getf rest :env)
          (if replace-environment-p
              (append env '((:PATH . "")))
              (append env ext:*environment-list*))))
  (remf rest :replace-environment-p)
  (remf rest :environment)
  rest)

(defmethod run
    (program args
     &rest rest &key environment replace-environment-p &allow-other-keys)
  (process-status (apply #'ext:run-program
                         program (stringify-args args) :wait t
                         (convert-environment rest environment replace-environment-p))))

(defmethod start
    (program args
     &rest rest &key environment replace-environment-p &allow-other-keys)
  (apply #'ext:run-program
         program (stringify-args args) :wait nil
         (convert-environment rest environment replace-environment-p)))

(defmethod signal-process (process signal)
  (ext:process-kill process (cdr (assoc signal *signal-mapping*))))

(defmethod process-id (process)
  (ext:process-pid process))

(defmethod process-input-stream (process)
  (ext:process-input process))

(defmethod process-output-stream (process)
  (ext:process-output process))

(defmethod process-error-stream (process)
  (ext:process-error process))

(defmethod process-status (process)
  (values (ext:process-status process) (ext:process-exit-code process)))

(defmethod process-p (process)
  (ext:process-p process))
