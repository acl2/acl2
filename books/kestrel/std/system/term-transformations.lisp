; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-fn-into-ifs")
(include-book "apply-term")
(include-book "apply-terms-same-args")
(include-book "apply-unary-to-terms")
(include-book "close-lambdas")
(include-book "conjoin")
(include-book "conjoin-equalities")
(include-book "fapply-term")
(include-book "fapply-terms-same-args")
(include-book "fapply-unary-to-terms")
(include-book "flatten-ands-in-lit")
(include-book "fsublis-fn")
(include-book "fsublis-var")
(include-book "make-mv-let-call")
(include-book "make-mv-nth-calls")
(include-book "mvify")
(include-book "quote-term")
(include-book "quote-term-list")
(include-book "remove-dead-if-branches")
(include-book "remove-mbe")
(include-book "remove-progn")
(include-book "remove-trivial-vars")
(include-book "remove-unused-vars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/term-transformations
  :parents (std/system)
  :short "Utilities to transform terms.")
