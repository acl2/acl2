;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(defpackage external-program
  (:use #:cl)
  (:export #:start #:run #:signal-process
	   #:process-id #:process-input-stream
	   #:process-output-stream #:process-error-stream
	   #:process-status #:process-p)
  (:documentation ""))

(in-package :external-program)

(defgeneric start
    (program args
     &key
     input if-input-does-not-exist output if-output-exists error if-error-exists
     environment replace-environment-p
     status-hook)
  (:documentation
   "Runs the specified program in an external (Unix) process,
returning a process object if successful.

`INPUT`, `OUTPUT`, and `ERROR` all behave similarly, accepting one of
the following values:

* `NIL`, specifying that a null stream (e.g., `/dev/null`) should be
  used;
* `T`, specifying that the `EXTERNAL-PROCESS` should use the source or
  destination with which the Lisp was invoked;
* a stream;
* a pathname designator, to redirect to/from a file;
* `:STREAM`, which creates a new stream opened for character input or
  output (accessible via the `EXTERNAL-PROCESS-*-STREAM` functions);
  or
* `:OUTPUT`, (only available for `ERROR`) which directs the error
  output to the same destination as the standard output.

`ENVIRONMENT` contains an alist mapping vars to values.

`REPLACE-ENVIRONMENT-P` indicates whether the argument passed as `ENVIRONMENT`
should replace or extend the current environment. The default is `NIL` (to
extend the environment).

`STATUS-HOOK` is a function the system calls whenever the status of
the process changes. The function takes the process as an argument.")
  (:method (program args &rest rest)
    (declare (ignore program args rest))
    (error "This CL implementation does not support START."))
  (:method ((program pathname) args &rest rest)
    (apply #'start (namestring program) args rest)))

;;; FIXME: should status-hook be available here? If so, :STREAM might
;;; then be a valid arg, since the streams can be accessed from the
;;; status-hook
(defgeneric run
    (program args
     &key
     input if-input-does-not-exist output if-output-exists error if-error-exists
     environment replace-environment-p)
  (:documentation "Runs the specified program similarly to `START`,
  however it blocks and returns the external process status once the
  program exits.

`:STREAM` is not a valid argument to `INPUT`, `OUTPUT`, or `ERROR` for this function.")
  (:method ((program pathname) args &rest rest)
    (apply #'run (namestring program) args rest))
  (:method (program args &rest rest)
    (let ((process (apply #'start program args rest)))
      (do ((status (process-status process) (process-status process)))
          ((not (eq status :running)) (process-status process))))))

;;; FIXME: can we use something like this to catch certain classes of errors?
;; (defmethod run :around (program args &rest rest)
;;   (multiple-value-bind (status code) (call-next-method)
;;     (if (eql status :exited)
;;         (case code
;;           (0 (values))
;;           (71 (error 'program-not-found :program program))
;;           (t (error 'program-exited-with-error
;;                     :program program :code code))))
;;     (values status code)))

(defgeneric signal-process (process signal)
  (:documentation "Sends the specified unix signal to the specified
  external process. Signals an error if unsuccessful. The signal may
  be either an integer, or one of the keywords in
  `EXTERNAL-PROGRAM::*SIGNAL-MAPPING*`.")
  (:method (process signal)
    (declare (ignore signal))
    (if (process-p process)
        (error "This CL implementation does not support SIGNAL-PROCESS.")
        (error "Incorrect argument type (~a) for SIGNAL-PROCESS."
               (type-of process)))))

(defgeneric process-id (process)
  (:documentation "Returns the process id assigned to the external
  process by the operating system. This is typically a positive,
  16-bit number.")
  (:method (process)
    (if (process-p process)
        (error "This CL implementation does not support PROCESS-ID.")
        (error "Incorrect argument type (~a) for PROCESS-ID."
               (type-of process)))))

(defgeneric process-input-stream (process)
  (:documentation "Returns the stream created when the input argument
  to `START` is specified as `:STREAM`.")
  (:method (process)
    (if (process-p process)
        (error "This CL implementation does not support PROCESS-INPUT-STREAM.")
        (error "Incorrect argument type (~a) for PROCESS-INPUT-STREAM."
               (type-of process)))))

(defgeneric process-output-stream (process)
  (:documentation "Returns the stream created when the output argument
  to `START` is specified as `:STREAM`.")
  (:method (process)
    (if (process-p process)
        (error "This CL implementation does not support PROCESS-OUTPUT-STREAM.")
        (error "Incorrect argument type (~a) for PROCESS-OUTPUT-STREAM."
               (type-of process)))))

(defgeneric process-error-stream (process)
  (:documentation "Returns the stream created when the error argument
  to `START` is specified as `:STREAM`.")
  (:method (process)
    (if (process-p process)
        (error "This CL implementation does not support PROCESS-ERROR-STREAM.")
        (error "Incorrect argument type (~a) for PROCESS-ERROR-STREAM."
               (type-of process)))))

(defgeneric process-status (process)
  (:documentation "Returns, as multiple values, a keyword denoting the
  status of the external process (one of `:RUNNING`, `:STOPPED`,
  `:SIGNALED`, or `:EXITED`), and the exit code or terminating signal
  if the first value is other than `:RUNNING`.")
  (:method (process)
    (if (process-p process)
        (error "This CL implementation does not support PROCESS-STATUS.")
        (error "Incorrect argument type (~a) for PROCESS-STATUS."
               (type-of process)))))

(defgeneric process-p (process)
  (:documentation "`T` if object is a process, `NIL` otherwise.")
  (:method (process)
    (declare (ignore process))
    nil))

(defvar *signal-mapping*
  '((:hangup . 1)
    (:interrupt . 2)
    (:quit . 3)
    (:illegal-instruction . 4)
    (:breakpoint-trap . 5)
    (:abort . 6)
    (:emulation-trap . 7)
    (:arithmetic-exception . 8)
    (:killed . 9)
    (:bus-error . 10)
    (:segmentation-fault . 11)
    (:bad-system-call . 12)
    (:broken-pipe . 13)
    (:alarm-clock . 14)))
