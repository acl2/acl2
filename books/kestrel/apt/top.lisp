; APT (Automated Program Transformations) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "utilities/top")

(include-book "common-concepts")
(include-book "common-options")

(include-book "casesplit")

(include-book "expdata")

(include-book "isodata")

(include-book "parteval")

(include-book "propagate-iso")

(include-book "restrict")

(include-book "schemalg")

(include-book "simplify")

(include-book "solve")
(include-book "solve-method-acl2-rewriter")

(include-book "tailrec")
