; Standard System Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-fnnames")
(include-book "all-free-bound-vars")
(include-book "all-lambdas")
(include-book "all-non-gv-exec-ffn-symbs")
(include-book "all-non-gv-ffn-symbs")
(include-book "all-pkg-names")
(include-book "all-program-ffn-symbs")
(include-book "all-vars")
(include-book "all-vars-in-untranslated-term")
(include-book "all-vars-open")
(include-book "check-and-call")
(include-book "check-fn-call")
(include-book "check-if-call")
(include-book "check-lambda-call")
(include-book "check-list-call")
(include-book "check-mbt-call")
(include-book "check-mbt-dollar-call")
(include-book "check-mv-let-call")
(include-book "check-nary-lambda-call")
(include-book "check-or-call")
(include-book "check-unary-lambda-call")
(include-book "check-user-lambda")
(include-book "check-user-term")
(include-book "dumb-occur-var-open")
(include-book "guard-verified-exec-fnsp")
(include-book "guard-verified-fnsp")
(include-book "if-tree-leaf-terms")
(include-book "lambda-closedp")
(include-book "lambda-guard-verified-exec-fnsp")
(include-book "lambda-guard-verified-fnsp")
(include-book "lambda-logic-fnsp")
(include-book "term-guard-obligation")
(include-book "term-possible-numbers-of-results")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/term-queries
  :parents (std/system)
  :short "Utilities to query terms.")
