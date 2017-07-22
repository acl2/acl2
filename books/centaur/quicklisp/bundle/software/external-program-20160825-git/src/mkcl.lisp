;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;; Code is in mkcl/src/c/unixsys.d

(defstruct external-process
  inputp
  outputp
  stream
  process)

(defmethod run
    (program args
     &key input output error environment replace-environment-p
     &allow-other-keys)
  (if (or output error)
      (warn "Can not control EXTERNAL-PROGRAM:RUN output in MKCL."))
  (if input (error "Can not send input to EXTERNAL-PROGRAM:RUN in MKCL."))
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (values :exited
            (nth-value 2
                       (mk-ext:run-program program (stringify-args args)
                                           :wait t
                                           :input input
                                           :output output
                                           :error error)))))

(defmethod start
    (program args
     &key input output error environment replace-environment-p
     &allow-other-keys)
  (if (eq error :stream)
      (error "MKCL can not create a stream for error output."))
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (multiple-value-bind (stream process return-value)
        (mk-ext:run-program program (stringify-args args)
                            :wait nil
                            :input input
                            :output output
                            :error error)
      (declare (ignore return-value))
      (make-external-process :inputp (eq input :stream)
                             :outputp (eq output :stream)
                             :stream stream
                             :process process))))

(defmethod process-input-stream ((process external-process))
  (if (external-process-inputp process)
      (external-process-stream process)))

(defmethod process-output-stream ((process external-process))
  (if (external-process-outputp process)
      (external-process-stream process)))

(defmethod process-error-stream ((process external-process))
  (declare (ignore process))
  nil)

(defmethod process-id ((process external-process))
  (mk-ext:process-id (external-process-process process)))

(defmethod process-p ((process external-process))
  (declare (ignore process))
  t)

(defmethod process-status ((process external-process))
  (mk-ext:process-status (external-process-process process)))
