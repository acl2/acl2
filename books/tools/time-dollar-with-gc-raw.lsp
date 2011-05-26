(in-package "ACL2")

(defmacro time$-with-gc1-raw (val form)
  (declare (ignore val))
  #-(or ccl sbcl lispworks)
  form
  #+(or ccl sbcl)
  `(let* ((start-gc-time #+ccl (ccl:gctime)
                         #+sbcl sb-ext:*gc-run-time*)
          (result (multiple-value-list (time$ ,form)))
          (end-gc-time #+ccl (ccl:gctime)
                       #+sbcl sb-ext:*gc-run-time*)
          (total-gc-time (- end-gc-time start-gc-time)))
     (format t "Total GC time: ~s" total-gc-time)
     (values-list result))
  #+lispworks
  `(hcl:extended-time (time$ ,form)))
