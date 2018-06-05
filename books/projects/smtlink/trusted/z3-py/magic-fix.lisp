;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (31st May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(define magic-fix ((type symbolp)
                   (x t))
  (declare (ignore type))
  x)
