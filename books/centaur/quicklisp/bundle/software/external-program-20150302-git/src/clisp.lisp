;;; Copyright 2006-2008 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;;; Documentation at http://www.gnu.org/software/clisp/impnotes/shell.html

(defstruct external-process
  in-stream
  out-stream)

(defun check-arguments (input output error)
  (when (or (streamp input) (streamp output))
    (error "CLISP does not support supplying existing streams for input or ~
            output."))
  (when error
    (warn "Can not control error output in CLISP.")))

(defmethod run
    (program args
     &key input output if-output-exists error environment replace-environment-p
     &allow-other-keys)
  (check-arguments input output error)
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (let ((result (ext:run-program program
                                   :arguments (stringify-args args)
                                   :input (if (eq input t) :terminal input)
                                   :output (if (eq output t) :terminal output)
                                   :if-output-exists if-output-exists
                                   :wait t)))
      (cond ((null result) (values :exited 0))
            ((< result 0)  (values :signaled (- result)))
            (t             (values :exited result))))))

(defmethod start
    (program args
     &key input output if-output-exists error environment replace-environment-p
     &allow-other-keys)
  (check-arguments input output error)
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (multiple-value-bind (primary-stream output-stream input-stream)
        (ext:run-program program :arguments args
                         :input (if (eq input t) :terminal input)
                         :output (if (eq output t) :terminal output)
                         :if-output-exists if-output-exists
                         :wait nil)
      (when input-stream (close primary-stream))
      (make-external-process
       :out-stream (when (eq output :stream) (or output-stream primary-stream))
       :in-stream (when (eq input :stream) (or input-stream primary-stream))))))

(defmethod process-input-stream (process)
  (external-process-in-stream process))

(defmethod process-output-stream (process)
  (external-process-out-stream process))

(defmethod process-error-stream (process)
  (declare (ignore process))
  nil)

(defmethod process-p (process)
  (typep process 'external-process))
