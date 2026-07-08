; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-environments
  :parents (dynamic-semantics)
  :short "Dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment consists of
     the contextual information needed to execute ASTs.
     It is the dynamic counterpart of a "
    (xdoc::seetopic "static-environments" "static environment")
    ".")
   (xdoc::p
    "Our dynamic environments have no direct counterpart
     in [thesis], [arxiv], and [esop],
     which use beta reduction rules to substitute variables
     (for expressions, types, and ispaces).
     Our dynamic environment is needed
     to express conveniently an interpretive dynamic semantics;
     they may be also needed or convenient
     for a rule-based small-step operational semantics,
     which we plan to do at some point.
     It may also facilitate expressing and proving type soundness.
     If Remora is extended with top-level definitions
     (now there are only @('let') expressions),
     a dynamic environment would keep track of those definitions;
     we already have implicit definitions of the primitive operations in fact.
     But we will investigate all of this as we progress in our work."))
  :order-subtopics t
  :default-parent t)
