;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (May 21st 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

;; Include SMT books
(include-book "hint-interface")

(define fixing-clause ((cl pseudo-term-listp)
                       (hints smtlink-hint-p))
  :returns (fixed-hint smtlink-hint-p)
  (b* ((hints (smtlink-hint-fix hints))
       (cl (pseudo-term-list-fix cl))
       ((smtlink-hint h) hints)
       ;; Currently using just the expanded clause without learning the fixing
       ;; functions. The code assumes all fixing functions are inserted by the
       ;; user.
       (fix-hint h.fix-hint)
       (fixed-hint-pair (make-hint-pair :thm (disjoin cl)
                                        :hints fix-hint)))
    (change-smtlink-hint h :fixed-clause fixed-hint-pair)))

