(in-package "X86ISA")

(defparameter *console-stream* nil)

(let* ((socket (ccl::make-socket :connect :passive ;; Listen
                                 :local-host "localhost"
                                 :local-port 6444))
       (stream (ccl::accept-connection socket)))
  (setf *console-stream* stream))

(defun write-console (c x86)
  (write-char c *console-stream*)
  (force-output *console-stream*))

(defun read-console (x86)
  (read-char-no-hang *console-stream*))
