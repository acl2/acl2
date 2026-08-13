; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "bound-variable-operations")
(include-book "desugaring")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bound-variables-under-desugaring
  :parents (abstract-syntax)
  :short "Preservation of bound variables under desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that desugaring preserves the bound variables of ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bound-ispace-vars-of-desugar
  :short "Desugaring preserves the bound ispace variables."

  (defrule bind-bound-ispace-vars-of-bind-desugar
    (equal (bind-bound-ispace-vars (bind-desugar bind))
           (bind-bound-ispace-vars bind))
    :expand ((bind-desugar bind))
    :enable bind-bound-ispace-vars)

  (defrule bind-list-bound-ispace-vars-of-bind-list-desugar
    (equal (bind-list-bound-ispace-vars (bind-list-desugar binds))
           (bind-list-bound-ispace-vars binds))
    :induct t
    :expand ((bind-list-desugar binds))
    :enable bind-list-bound-ispace-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bound-type-vars-of-desugar
  :short "Desugaring preserves the bound type variables."

  (defrule bind-bound-type-vars-of-bind-desugar
    (equal (bind-bound-type-vars (bind-desugar bind))
           (bind-bound-type-vars bind))
    :expand ((bind-desugar bind))
    :enable bind-bound-type-vars)

  (defrule bind-list-bound-type-vars-of-bind-list-desugar
    (equal (bind-list-bound-type-vars (bind-list-desugar binds))
           (bind-list-bound-type-vars binds))
    :induct t
    :expand ((bind-list-desugar binds))
    :enable bind-list-bound-type-vars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: expr vars
