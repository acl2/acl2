; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-core")
(include-book "abstract-syntax-structural-operations")

(include-book "kestrel/fty/deffold-map" :dir :system)

(acl2::controlled-configuration)

(local (in-theory (enable* abstract-syntax-corep-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ desugaring
  :parents (abstract-syntax)
  :short "Abstract syntax desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a desugaring transformation from all ASTs to the core ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map desugar
  :short "Desugar ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A shape with a list of zero or more dimensions
     is turned into a concatenation of single-dimension shapes.")
   (xdoc::p
    "A shape splice is turned into a concatenation.")
   (xdoc::p
    "A bracket type is turned into an array type
     whose shape is the concatenation of the shapes."))
  :types (shapes
          ispace
          ispace-list
          ispace-list-option
          types
          var+type
          var+type-list
          ;; TODO:
          ;; exprs/atoms/binds
          ;; prog
         )
  :override
  ((shape :dims (shape-append (shape-dim-list shape.dims)))
   (shape :splice (shape-append (shape-list-desugar shape.shapes)))
   (type :bracket (make-type-array :elem (type-desugar type.elem)
                                   :shape (shape-append
                                           (shape-list-desugar type.shapes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-desugar
  :short "Desugaring always returns core ASTs."

  (defret-mutual shapes-corep-of-shapes-desugar
    (defret shape-corep-of-shape-desugar
      (shape-corep fty::result)
      :fn shape-desugar)
    (defret shape-list-corep-of-shape-list-desugar
      (shape-list-corep fty::result)
      :fn shape-list-desugar)
    :mutual-recursion shapes-desugar
    :hints (("Goal" :in-theory (enable shape-desugar shape-list-desugar))))

  (defret ispace-corep-of-ispace-desugar
    (ispace-corep fty::result)
    :fn ispace-desugar
    :hints (("Goal" :in-theory (enable ispace-desugar))))

  (defret ispace-list-corep-of-ispace-list-desugar
    (ispace-list-corep fty::result)
    :fn ispace-list-desugar
    :hints (("Goal" :induct t :in-theory (enable ispace-list-desugar))))

  (defret ispace-list-option-corep-of-ispace-list-option-desugar
    (ispace-list-option-corep fty::result)
    :fn ispace-list-option-desugar
    :hints (("Goal" :in-theory (enable ispace-list-option-desugar))))

  (defret-mutual types-corep-of-types-desugar
    (defret type-corep-of-type-desugar
      (type-corep fty::result)
      :fn type-desugar)
    (defret type-list-corep-of-type-list-desugar
      (type-list-corep fty::result)
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar type-list-desugar))))

  (defret var+type-corep-of-var+type-desugar
    (var+type-corep fty::result)
    :fn var+type-desugar
    :hints (("Goal" :in-theory (enable var+type-desugar))))

  (defret var+type-list-corep-of-var+type-list-desugar
    (var+type-list-corep fty::result)
    :fn var+type-list-desugar
    :hints (("Goal" :induct t :in-theory (enable var+type-list-desugar))))

  ;; TODO: add more when more functions are defined

)
