;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "pretty-printer")

;; (defsection SMT-translator
;;   :parents (z3-py)
;;   :short "SMT-translator does the LISP to Python translation."

(define SMT-translation ((term pseudo-termp)
                         (smtlink-hint smtlink-hint-p)
                         state)
  ;; :returns (mv (py-term paragraphp)
  ;;              (smt-precond pseudo-termp)
  ;;              (uninterpreted-precond pseudo-term-list-listp))
  :mode :program
  :ignore-ok t
  (b* ((term (pseudo-term-fix term))
       (- (cw "SMT-translation: ~q0" term))
       (smtlink-hint (smtlink-hint-fix smtlink-hint)))
    (mv nil nil)))
;;  )
