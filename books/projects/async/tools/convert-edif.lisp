(in-package "ACL2")

(defun convert-edif (in-file out-file state)
  (declare (xargs :mode :program ; because of (er soft ...)
                  :stobjs state))
  (let ((ctx 'convert-edif))
    (mv-let (in-channel state)
      (open-input-channel in-file :object state)
      (cond
       ((null in-channel)
        (er soft ctx
            "Unable to open file ~x0 for input."
            in-file))
       (t
        (mv-let (eofp obj state)
          (read-object-with-case in-channel :preserve state)
          (pprogn
           (close-input-channel in-channel state)
           (cond
            (eofp (er soft ctx
                      "Unable to read an expressoin from file ~x0."
                      in-file))
            (t (mv-let (out-channel state)
                 (open-output-channel out-file :object state)
                 (cond
                  ((null out-channel)
                   (er soft ctx
                       "Unable to open file ~x0 for output."
                       out-file))
                  (t
                   (pprogn
                    (print-object$ obj out-channel state)
                    (close-output-channel out-channel state)
                    (value (list :converted-edif out-file)))))))))))))))
