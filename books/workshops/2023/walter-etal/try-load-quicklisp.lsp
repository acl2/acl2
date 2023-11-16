(defun error-no-ql ()
  (error "Quicklisp not found. Either it is not installed, or you have not set it to load automatically. Either set the QUICKLISP_SETUP environment variable to the path to your system's quicklisp/setup.lisp file, or modify build-server.lsp so that it is loaded."))

(defun error-load-failed ()
  (error "Tried to load Quicklisp from either the user-provided QUICKLISP_SETUP file or from the default Quicklisp setup location but this failed."))

(let ((ql-load-attempted
      (cond
       ((member :quicklisp *features*) t)
       ((sb-unix::posix-getenv "QUICKLISP_SETUP")
        (load (sb-unix::posix-getenv "QUICKLISP_SETUP"))
        t)
       ((probe-file "~/quicklisp/setup.lisp")
        (load "~/quicklisp/setup.lisp")
        t)
       (t nil))))
  (cond ((member :quicklisp *features*) t)
        (ql-load-attempted (error-load-failed))
        (t (error-no-ql))))
