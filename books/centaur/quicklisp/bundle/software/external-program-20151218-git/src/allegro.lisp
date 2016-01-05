;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

;;; Contributions 2013 by Utz-Uwe Haus <lisp@uuhaus.de>

(in-package :external-program)

;;;; Documentation at http://www.franz.com/support/documentation/6.2/doc/os-interface.htm#subprocess-functions-1

(eval-when (:compile-toplevel :load-toplevel :execute)
  #-os-windows (require :system)
  (require :osi))

(defmethod run
    (program args
     &key
     input if-input-does-not-exist output if-output-exists error if-error-exists
     environment replace-environment-p
     &allow-other-keys)
  (let* ((input-stream (etypecase input
                         (stream input)
                         ((or pathname string)
                          (open input
                                :if-does-not-exist if-input-does-not-exist))
                         (null nil)
                         (boolean *standard-input*)))
         (output-stream (etypecase output
                          (stream output)
                          ((or pathname string)
                           (open output
                                 :direction :output
                                 :if-exists if-output-exists))
                          (null nil)
                          (boolean *standard-output*)))
         (error-stream (etypecase input
                         (stream error)
                         ((or pathname string)
                          (open error
                                :direction :output
                                :if-exists if-error-exists))
                         (null nil)
                         (boolean *standard-output*)
                         (symbol output-stream))))
    (values :exited
            (excl.osi:with-command-io
                ((make-shell-string program args
                                    environment replace-environment-p))
              (:input (stream)
                      (when input-stream
			(loop :as line := (read-line input-stream nil nil nil)
			   :while line
			   :do (write-line line stream))))
              (:output (line)
                       (when output-stream (write-line line output-stream)))
              (:error-output (line)
                             (when error-stream
                               (write-line line error-stream)))))))


;;; Support for nonblocking processes and explicit stream access
;;; http://www.franz.com/support/documentation/9.0/doc/operators/excl/run-shell-command.htm
;;; http://www.franz.com/support/documentation/9.0/doc/operators/system/reap-os-subprocess.htm
(defstruct allegro-process
  "A process object; unique for each process started by START."
  input
  output
  error
  pid
  reap-result)

;; At any given time only one process will be alive on the OS side and
;; occupy a PID. However: the caller may hang on to our process object
;; even after its os process has died and the pid is
;; re-used. Therefore for each PID we saw we store a weak key-only
;; hash table with the process objects and let the GC clean up for us

(defvar *allegro-process-table*
  (make-hash-table :test #'eql)
  "A hash table keyed on the os-side PID of all processes we create
through excl:run-shell-command to enable reaping dead children. 
Values are weak key-only hash tables containing process structures.")

(defvar *allegro-unreaped-processes*
  (make-hash-table :test #'eq :values nil)
  "A has hash table storing all unreaped processes to keep them from being
collected by the GC if the caller disposes of his reference before the process dies.")

(defun store-process (process)
  "Update bookkeeping table for freshly created PROCESS."
  (let ((tab (or (gethash (allegro-process-pid process)
			  *allegro-process-table*)
		 (setf (gethash (allegro-process-pid process)
				*allegro-process-table*)
		       (make-hash-table :test #'eq :weak-keys t :values nil)))))
    (setf (gethash process *allegro-process-table*) nil
	  (gethash process tab) process)))

(defun find-process-for-pid (pid)
  "Find the (unique) process structure for PID that has not been reaped."
  (let ((tab (gethash pid *allegro-process-table*)))
    (if tab
	(or (loop :for process :being :each :hash-key :of tab
	       :when (null (allegro-process-reap-result process))
	       :return process)
	    (error "PID ~A has no unreaped process." pid))
	(error "PID ~A unknown." pid))))

(defun notice-dead-processes ()
  "Reap all dead children and store their status in *allegro-process-table*
for later perusal."
  (loop :with status :and pid :and sig
     :do (multiple-value-setq (status pid sig)
	   (system:reap-os-subprocess :wait nil))
     :while (and pid (> pid 0))
     ;; some process exited, and we can store its status. 
     ;; Note: ACL 9 may return -1 for the PID. Bug report to Franz Inc. pending.
     :do (let ((process (find-process-for-pid pid)))
	   (setf (allegro-process-reap-result process)
		 (if sig
		     (list :signaled sig)
		     (list :exited status)))
	   (remhash process *allegro-unreaped-processes*))))

(defmethod start (program args
		  &key input output error environment replace-environment-p
		    if-input-does-not-exist if-output-exists
		    if-error-exists
		    &allow-other-keys)
  ;; we mis-use this as a hook to reap processes. That way, at most one
  ;; zombie-like process is around at any time.
  (notice-dead-processes)
  (when replace-environment-p
    (warn "replace-environment unsupported on Allegro CL."))
  (when (and (or (eq nil output)
		 (eq nil error))
	     ;; FIXME: Windows anyone?
	     (not (probe-file #p"/dev/null")))
    (error "Cannot suppress output on this system."))
  (let* ((in (cond
	     ;; nil and t are different on allegro
	     ((eq nil input) (make-string-input-stream ""))
	     ((eq t input) nil)
	     (t input)))
	 (out (cond
	     ;; nil and t are different on allegro
	     ((eq nil output) (open #p"/dev/null" :direction :output :if-exists :supersede))
	     ((eq t input) nil)
	     (t input)))
	 (err (cond
	     ;; nil and t are different on allegro
	     ((eq nil input) (open #p"/dev/null" :direction :output :if-exists :supersede))
	     ((eq t input) nil)
	     ((eq :output output) out)
	     (t input))))
    (multiple-value-bind (instream outstream errstream pid)
	(excl:run-shell-command
	 (format nil "~A~{~^ ~A~}" program args)
	 :wait nil :separate-streams t
	 :input in :output out :error-output err
	 :if-input-does-not-exist if-input-does-not-exist
	 :if-output-exists if-output-exists
	 :if-error-output-exists if-error-exists
	 :environment environment)
      (let ((process (make-allegro-process
		      :input instream :output outstream :error errstream
		      :pid pid :reap-result nil)))
	(store-process process)
	process))))

(defmethod process-p ((process allegro-process))
  t)

(defmethod signal-process (process (signal symbol))
  (let ((sig (assoc signal *signal-mapping*)))
    (if (not sig)
	(error "Symbolic signal ~A not supported." signal)
	(signal-process process sig))))

(defmethod signal-process ((process allegro-process) (signal integer))
  (excl.osi:kill (allegro-process-pid process) signal))

(defmethod process-input-stream ((process allegro-process))
  (allegro-process-input process))

(defmethod process-output-stream ((process allegro-process))
  (allegro-process-output process))

(defmethod process-error-stream ((process allegro-process))
  (allegro-process-error process))

(defmethod process-id ((process allegro-process))
  (allegro-process-pid process))

(defmethod process-status ((process allegro-process))
  (notice-dead-processes)
  ;; ok, check on process now
  (if (allegro-process-reap-result process)
      (apply #'values (allegro-process-reap-result process))
      (values :running)))

