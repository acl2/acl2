; Solidity Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOLIDITY")

(include-book "sld-refs")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ boolean-values
  :parents (values)
  :short (xdoc::topstring "Boolean values " xdoc::*sld-types-booleans* ".")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bool
  :short "Fixtype of boolean values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the values of the @('bool') type."))
  ((get acl2::bool))
  :tag :bool
  :layout :list
  :pred boolp
  ///

  (defruled boolp-alt-def
    (equal (boolp x)
           (or (equal x (bool t))
               (equal x (bool nil))))
    :enable boolp))
