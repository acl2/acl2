;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "ACL2")

;; (include-book "config")
;; (include-book "helper")
;; (include-book "SMT-extract")
;; (include-book "SMT-formula")
;; (include-book "SMT-function")
;; (include-book "SMT-translator")
;; (include-book "SMT-interpreter")
;; (include-book "SMT-run")
;; (include-book "SMT-py")  ; note (mrg, 28 May 2015): I renamed SMT-z3.lisp to SMT-py.lisp
(include-book "SMT-connect")

;; ;; --------------------------------------------------- ;;
;; ;; Generating documentation

;; (include-book "xdoc/save" :dir :system)  ;; load xdoc::save

;; (defxdoc acl2::top           ;; create a "top" topic
;;   :short "Tutorial and documentation for the ACL2 book, Smtlink."
;;   :long "<h3>Introduction</h3>
;;          <p><b>Smtlink</b> is a tool for integrating external SMT solvers into ACL2.
;;          It is based on the @(see Clause-processor) mechanism.</p>
;;          <p>Under construction ...</p>")

;; (xdoc::save "./Smtlink-manual")  ;; write the manual
