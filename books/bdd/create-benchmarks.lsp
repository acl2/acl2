(in-package "ACL2")

(set-ld-pre-eval-print :never state)

(set-inhibit-output-lst (list (quote prove) (quote proof-tree) (quote warning) (quote observation)))

(include-book "cbf")

(mv-let (chan state)
        (open-input-channel "benchmarks.lisp" :object state)
        (cond (chan (pprogn (close-input-channel chan state)
                            (value nil)))
              (t (write-benchmark-file "be/" state))))
