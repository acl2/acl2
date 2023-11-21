;;;; -*- Mode: LISP; Syntax: Ansi-Common-Lisp; Package: TRIVIAL-BACKTRACE; Base: 10; -*-
(in-package #:trivial-backtrace)

(defstruct frame
  func
  source-filename
  source-pos
  vars)

(defstruct var
  name
  value)

(defstruct pos-form-number
  number)

(defmethod print-object ((pos-form-number pos-form-number) stream)
  (cond 
    (*print-readably* (call-next-method))
    (t
     (format stream "f~A" (pos-form-number-number pos-form-number)))))


(defvar *trivial-backtrace-frame-print-specials*
  '((*print-length* . 100)
    (*print-level* . 20)
    (*print-lines* . 5)
    (*print-pretty* . t)
    (*print-readably* . nil)))

(defun print-frame (frame stream)
  (format stream "~A:~@[~A:~] ~A: ~%" 
	  (or (ignore-errors (translate-logical-pathname (frame-source-filename frame))) (frame-source-filename frame) "<unknown>")
	  (frame-source-pos frame)
	  (frame-func frame))
  (loop for var in (frame-vars frame)
	do 
	(format stream " ~A = ~A~%" (var-name var) 
		(or (ignore-errors 	
			(progv 
			    (mapcar #'car *trivial-backtrace-frame-print-specials*)
			    (mapcar #'cdr *trivial-backtrace-frame-print-specials*)
			  (prin1-to-string 
			   (var-value var))))
		    "<error>"))))

(defun map-backtrace (function)
  (impl-map-backtrace function))

(defun print-map-backtrace (&optional (stream *debug-io*) &rest args)
  (apply 'map-backtrace 
	 (lambda (frame)
	   (print-frame frame stream)) args))

(defun backtrace-string (&rest args)
  (with-output-to-string (stream)
    (apply 'print-map-backtrace stream args)))


#+ccl
(defun impl-map-backtrace (func)
  (ccl::map-call-frames (lambda (ptr &optional context) 
			  (multiple-value-bind (lfun pc)
			      (ccl::cfp-lfun ptr)
			    (let ((source-note (ccl:function-source-note lfun)))
			      (funcall func 
				       (make-frame :func (ccl::lfun-name lfun)
						   :source-filename (ccl:source-note-filename source-note)
						   :source-pos (let ((form-number (ccl:source-note-start-pos source-note)))
								 (when form-number (make-pos-form-number :number form-number)))
						   :vars (loop for (name . value) in (ccl::arguments-and-locals nil ptr lfun pc)
							       collect (make-var :name name :value value)))))))))

#+sbcl
(defun impl-map-backtrace (func)
  (loop for f = (or sb-debug:*stack-top-hint* (sb-di:top-frame)) then (sb-di:frame-down f)
	while f
	do (funcall func 
		    (make-frame :func 
				(ignore-errors
				  (sb-di:debug-fun-name 			    
				   (sb-di:frame-debug-fun f)))
				:source-filename 
				(ignore-errors
				  (sb-di:debug-source-namestring (sb-di:code-location-debug-source (sb-di:frame-code-location f))))
				:source-pos
				(ignore-errors ;;; XXX does not work
				  (let ((cloc (sb-di:frame-code-location f)))
				    (unless (sb-di:code-location-unknown-p cloc)
				      (format nil "tlf~Dfn~D"
					      (sb-di:code-location-toplevel-form-offset cloc)
					      (sb-di:code-location-form-number cloc)))))
				:vars
				(remove-if 'not 
					   (map 'list (lambda(v)
							(ignore-errors
							  (when (eq :valid
							     (sb-di:debug-var-validity v (sb-di:frame-code-location f)))
							    (make-var :name (sb-di:debug-var-symbol v)
								      :value (sb-di:debug-var-value v f)))))
						(ignore-errors (sb-di::debug-fun-debug-vars (sb-di:frame-debug-fun f)))))))))

#+clasp
(defun impl-map-backtrace (func)
  (clasp-debug:with-stack (stack)
      (clasp-debug:map-stack
       #'(lambda(current-frame)
           (funcall func
                    (let ((source (clasp-debug:frame-source-position current-frame)))
                      (make-frame :func (clasp-debug:frame-function current-frame)
                                  :source-filename (if source (clasp-debug:code-source-line-pathname source) nil)
                                  :source-pos (if source (clasp-debug:code-source-line-line-number source) nil)
                                  :vars (let ((index 0))
                                           (mapcar #'(lambda(argument)
                                                       (prog1
                                                           (make-var :name (format nil "Arg-~a" index) :value argument)
                                                         (incf index)))
                                                   (clasp-debug:frame-arguments current-frame)))))))
       
       stack)))

#-(or ccl sbcl clasp)
(defun impl-map-backtrace (func)
  (declare (ignore func))
  (warn "unable to map backtrace for ~a" (lisp-implementation-type)))
