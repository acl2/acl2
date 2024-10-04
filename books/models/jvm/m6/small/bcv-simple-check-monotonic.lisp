(in-package "ACL2")
(include-book "bcv-simple-model")


(defthm bcv-simple-check-step-pre-bcv-simple-check-step-pre
  (implies (and (sig-frame-compatible frame1 frame2)
                (bcv-simple-check-step-pre inst frame2))
           (bcv-simple-check-step-pre inst frame1)))
