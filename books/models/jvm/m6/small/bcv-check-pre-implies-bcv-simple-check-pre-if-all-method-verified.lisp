(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")

(defthm bcv-check-step-pre-implies-bcv-simple-check-step-INVOKE
  (implies (and (bcv-check-INVOKE inst sig-frame)
                (bcv-verified-method-table (g 'method-table sig-frame)))
           (bcv-simple-check-INVOKE (g 'inst inst) sig-frame)))

(defthm bcv-check-step-pre-implies-bcv-simple-check-step
  (implies (and (bcv-check-step-pre inst sig-frame)
                (bcv-verified-method-table (g 'method-table sig-frame)))
           (bcv-simple-check-step-pre (g 'inst inst) sig-frame))
  :hints (("Goal" :in-theory (disable bcv-check-INVOKE
                                      bcv-verified-method-table
                                      bcv-simple-check-INVOKE))))