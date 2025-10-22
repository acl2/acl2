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

(include-book "abstract-syntax-irrelevants")
(include-book "implementation-environments")

(include-book "std/util/defirrelevant" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ code-ensembles
  :parents (abstract-syntax)
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

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-code-ensemble
  :short "An irrelevant code ensemble."
  :type code-ensemblep
  :body (make-code-ensemble
         :transunits (irr-transunit-ensemble)
         :ienv (ienv-default)))
