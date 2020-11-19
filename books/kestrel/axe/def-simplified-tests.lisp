(in-package "ACL2")

(include-book "def-simplified")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (def-simplified *three* '(+ 1 2))
  (must-be-redundant
   (defconst *three* ''3)))

(deftest
  (def-simplified *car-cons* '(car (cons x y)))
  (must-be-redundant
   (defconst *car-cons* '((0 . x)))))
