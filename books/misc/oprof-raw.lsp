;; Simple Profiler for OpenMCL -- Raw Lisp Code
;;
;; Written in 2008 by Jared Davis <jared@cs.utexas.edu>.  This code 
;; is in the public domain and may be freely used and copied without
;; restriction.

(in-package "ACL2")

(declaim (type hash-table *oprof.results-table*))

(defparameter *oprof.results-table* 
  ;; A table that records our statistics for each function.  Each entry is of
  ;; the form (calls . total-time)
  (make-hash-table :size 64 :test #'eq))

(defparameter *oprof.active-stack* 
  ;; A stack of the functions that (1) we are profiling, and (2) are currently
  ;; being called.  Each frame has the format (fn . start-time).
  nil)

(defun oprof.watch-fn (f)
  ;; Create an initial entry in the profiling table.
  (setf (gethash f *oprof.results-table*) (cons 0 0))
  ;; Calling this function will now push frames onto the active stack.
  (eval `(CCL::advise ,f
                      (push (cons ',f (get-internal-real-time)) *oprof.active-stack*)
                      :when :before))
  ;; Exiting this function will now pop frames from the active stack 
  ;; and update the results table.
  (eval `(CCL::advise ,f
                      (let ((frame (pop *oprof.active-stack*)))
                        (unless (eq (car frame) ',f)
                          (error "Popped frame is not for the expected function.~%"))
                        (let* ((entry (gethash ',f *oprof.results-table*)))
                          (incf (the fixnum (car entry)))
                          (incf (the fixnum (cdr entry))
                                (- (the fixnum (get-internal-real-time))
                                   (the fixnum (cdr frame))))))
                      :when :after))
  nil)

(defun oprof.watch (fns)
  (loop for f in fns do (oprof.watch-fn f))
  nil)

(defun oprof.unwatch-fn (f)
  (eval `(CCL::unadvise ,f))
  (remhash f *oprof.results-table*)
  nil)

(defun oprof.unwatch (fns)
  (loop for f in fns do (oprof.unwatch-fn f))
  nil)

(defun oprof.stop ()
  (setf *oprof.active-stack* nil)
  (loop for key being the hash-keys of *oprof.results-table* do (oprof.unwatch-fn key))
  nil)
       
(defun oprof.report ()
  (let ((alist nil))
    (loop for key being the hash-keys of *oprof.results-table* using (hash-value value) do
          (push (cons key value) alist))
    (let ((sorted-alist (sort alist #'(lambda (x y) (> (cddr x) (cddr y))))))
      (loop for entry in sorted-alist do
            (format t "~a: ~a calls took ~,2f seconds.~%"
                    (car entry) 
                    (cadr entry) 
                    (coerce (/ (cddr entry) internal-time-units-per-second) 'float)))))
  nil)

(defun oprof.clear ()
  (setf *oprof.active-stack* nil)
  (loop for value being the hash-values of *oprof.results-table* do
        (setf (car value) 0)
        (setf (cdr value) 0))
  nil)

