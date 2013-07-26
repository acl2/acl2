
(in-package "GL")

(include-book "gl")
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "g-make-fast-alist")
(include-book "bfr-aig-bddify")
(include-book "bfr-satlink")

(def-gl-clause-processor glcp-ttags :output nil)
