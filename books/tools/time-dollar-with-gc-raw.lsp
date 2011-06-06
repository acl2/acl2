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
          (total-gc-time (/ (- end-gc-time start-gc-time) 
                            #+ccl internal-time-units-per-second
                            #+sbcl internal-time-units-per-second)))
     (format t "Total GC time: ~2$ seconds ~%" total-gc-time)
     (values-list result))
  #+lispworks
  `(hcl:extended-time 

; reported times are in seconds

    (time$ ,form)))
