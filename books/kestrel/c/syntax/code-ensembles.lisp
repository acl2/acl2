; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")
(include-book "implementation-environments")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-ensembles
  :parents (syntax-for-tools)
  :short "Code ensembles."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce the notion of code ensemble as consisting of a "
    (xdoc::seetopic "transunit-ensemble" "translation unit ensemble")
    " and an "
    (xdoc::seetopic "implementation-environments" "implementation environment")
    ". The latter provides information for interpreting the former."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod code-ensemble
  :short "Fixtype of code ensembles."
  ((transunits transunit-ensemble)
   (ienv ienv))
  :pred code-ensemblep)
