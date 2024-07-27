(in-package "X86ISA")

(defparameter *console-stream* nil)

(let* ((socket (ccl::make-socket :connect :passive ;; Listen
                                 :local-host "localhost"
                                 :local-port 6444))
       (stream (ccl::accept-connection socket)))
  (setf *console-stream* stream))

(defun write-tty (c x86)
  (write-char (code-char c) *console-stream*)
  (force-output *console-stream*)
  x86)

(defun read-tty (x86)
  (b* ((c (read-char-no-hang *console-stream*)))
      (mv (if (null c)
            nil
            (char-code c))
          x86)))
