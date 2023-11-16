(in-package "ACL2")

(deftheory-static setup-orig-theory (current-theory :here))
(include-book "arithmetic-5/top" :dir :system)
(deftheory-static arith-5-theory
  (set-difference-theories (current-theory :here)
                           (theory 'setup-orig-theory)))
