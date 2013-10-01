(in-package "ACL2")

(defun unsound-read-fn (filename hons-mode verbosep)
  (let ((*ser-verbose* verbosep))
    (with-open-file (stream filename :direction :input)
                    (ser-decode-from-stream t hons-mode stream))))
