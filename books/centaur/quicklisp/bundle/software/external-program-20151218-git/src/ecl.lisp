;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;; Outdated docs in http://ecls.sourceforge.net/new-manual/re11.html, but code
;;; is in ecl/src/c/unixsys.d

(defstruct external-process
  inputp
  outputp
  stream)

(defmethod run
    (program args
     &key input output error environment replace-environment-p
     &allow-other-keys)
  (if (or output error)
      (warn "Can not control EXTERNAL-PROGRAM:RUN output in ECL."))
  (if input (error "Can not send input to EXTERNAL-PROGRAM:RUN in ECL."))
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (values :exited
            (nth-value 1
                       (ext:run-program program (stringify-args args)
                                        :wait t
                                        :input input
                                        :output output
                                        :error error)))))

(defmethod start
    (program args
     &key input output error environment replace-environment-p
     &allow-other-keys)
  (if (eq error :stream)
      (error "ECL can not create a stream for error output."))
  (multiple-value-bind (program args)
      (embed-environment program args environment replace-environment-p)
    (make-external-process :inputp (eq input :stream)
                           :outputp (eq output :stream)
                           :stream (ext:run-program program
                                                    (stringify-args args)
                                                    :wait nil
                                                    :input input
                                                    :output output
                                                    :error error))))

(defmethod process-input-stream ((process external-process))
  (if (external-process-inputp process)
      (external-process-stream process)))

(defmethod process-output-stream ((process external-process))
  (if (external-process-outputp process)
      (external-process-stream process)))

(defmethod process-error-stream ((process external-process))
  (declare (ignore process))
  nil)

(defmethod process-p ((process external-process))
  (declare (ignore process))
  t)
