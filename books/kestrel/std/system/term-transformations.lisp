; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "apply-term")
(include-book "apply-terms-same-args")
(include-book "apply-unary-to-terms")
(include-book "close-lambdas")
(include-book "fapply-term")
(include-book "fapply-terms-same-args")
(include-book "fapply-unary-to-terms")
(include-book "fsublis-var")
(include-book "remove-dead-if-branches")
(include-book "remove-mbe")
(include-book "remove-progn")
(include-book "remove-trivial-vars")
(include-book "remove-unused-vars")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/term-transformations
  :parents (std/system)
  :short "Utilities to transform terms.")
