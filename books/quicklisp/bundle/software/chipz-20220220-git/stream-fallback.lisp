;;;; stream-fallback.lisp -- loaded when there is no support for gray streams

(in-package :chipz)

(defun make-decompressing-stream (format stream)
	(declare (ignore format stream))
	(error "make-decompressing-stream is not supported for this lisp implementation"))