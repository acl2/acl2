; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "integer-operations")
(include-book "symbolic-execution-rules/integers")

(include-book "../language/abstract-syntax-operations")
(include-book "../language/function-environments")
(include-book "../language/dynamic-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-execution
  :parents (atc-dynamic-semantics)
  :short "A model of C execution for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code in this file has been reformulated
     and moved to @('../langauge/dynamic-semantics.lisp')."))
  :order-subtopics t
  :default-parent t)
