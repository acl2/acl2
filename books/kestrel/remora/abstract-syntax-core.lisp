; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(include-book "kestrel/fty/deffold-reduce" :dir :system)
(include-book "kestrel/utilities/ordinals" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-core
  :parents (abstract-syntax)
  :short "Core abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We characterize the subset of the ASTs
     that form the core of the language.
     This is mostly based on [thesis],
     but some choices are discussed in the documentation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce corep
  :short "Check if the ASTs are in the core subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "We exclude:")
   (xdoc::ul
    (xdoc::li
     "Shapes with zero or more dimensions,
      because they are expressible as concatenations of
      shapes with single dimensions.")
    (xdoc::li
     "Shape splices,
      because they are expressible as concatenations.")
    (xdoc::li
     "Bracket types,
      because they are expressible as array types.")
    (xdoc::li
     "String literals,
      because they are expressible as array expressions.")
    (xdoc::li
     "Combined applications,
      because they are expressible as simpler applications.")
    (xdoc::li
     "Bracket expressions,
      because they are expressible as array expressions.")
    (xdoc::li
     "Let expressions,
      because they are expressible as applications of lambdas.")
    (xdoc::li
     "Bindings,
      because they are only used in let expressions.")))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          var+type
          var+type-list
          exprs/atoms/binds
          prog)
  :result booleanp
  :default t
  :combine and
  :override
  ((shape :dims nil)
   (shape :splice nil)
   (type :bracket nil)
   (expr :string nil)
   (expr :capp nil)
   (expr :bracket nil)
   (expr :let nil)
   (bind nil)))
