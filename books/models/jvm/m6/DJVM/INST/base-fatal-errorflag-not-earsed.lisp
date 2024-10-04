(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")


(defthm not-no-fatal-error-preserved-resolveClassReference
  (implies (not (no-fatal-error? s))
           (not (no-fatal-error? (resolveClassReference any s)))))