(in-package "ACL2")

(defun tshell-call-unsound-fn (cmd print save)
  (let* ((rlines nil)
         (stream (get-output-stream-from-channel *standard-co*))
         (print  (if (eq print t)
                     'tshell-echo
                   print))
         (status (shellpool:run cmd
                                :each-line (lambda (line type)
                                             (when save
                                               (push line rlines))
                                             (when print
                                               (funcall print line rlines stream))))))
    (mv status (nreverse rlines))))
