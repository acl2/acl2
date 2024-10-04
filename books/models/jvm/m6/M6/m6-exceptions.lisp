(in-package "M6")
(include-book "../M6-DJVM-shared/jvm-exceptions")

(defun raise-exception (any s)
  (jvm::raise-exception any s))

