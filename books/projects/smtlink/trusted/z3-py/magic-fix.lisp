;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (31st May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(defsection SMT-magic-fix
  :parents (verified)
  :short ""

  (define magic-fix ((type symbolp)
                     (x t))
    (declare (ignore type))
    x)

  (in-theory (enable magic-fix))
  (in-theory (disable (:type-prescription magic-fix)))
  )
