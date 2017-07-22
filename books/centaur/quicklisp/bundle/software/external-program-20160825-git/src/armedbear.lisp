;;; Copyright 2006, 2007 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(in-package :external-program)

;;;; No docs, but code is in /Applications/abcl-0.0.9/src/org/armedbear/lisp/ShellCommand.java

(defmethod run
    (program args &key input output error environment replace-environment-p
     &allow-other-keys)
  (when error
    (warn "Can not control EXTERNAL-PROGRAM:RUN error output in ABCL."))
  (when input (error "Can not send input to EXTERNAL-PROGRAM:RUN in ABCL."))
  (values :exited
          (ext:run-shell-command (make-shell-string program args
                                                    environment
                                                    replace-environment-p)
                                 :output output)))
