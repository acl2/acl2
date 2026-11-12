;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(include-book "config")

;; verified
(include-book "verified/computed-hints")
(include-book "verified/process")
(include-book "verified/add-hypo-cp")
(include-book "verified/expand-cp")
(include-book "verified/reorder-hypotheses")
(include-book "verified/term-rewrite")
(include-book "verified/tterm-triv-cp")
(include-book "verified/ti-bottom-up")
(include-book "verified/ti-top-down")
(include-book "verified/term-rewrite")
(include-book "verified/tterm-type-extract")
(include-book "verified/alist/int-sym")

;; trusted
(include-book "trusted/smt-lib")
