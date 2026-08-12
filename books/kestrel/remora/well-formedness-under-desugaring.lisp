; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-well-formedness")
(include-book "desugaring")

(local (include-book "kestrel/lists-light/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ well-formedness-under-desugaring
  :parents (abstract-syntax)
  :short "Preservation of well-formedness under desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that desugaring preserves the well-formedness of ASTs:
     the desugaring of a well-formed AST is well-formed.
     This is one of the preservation properties
     mentioned in @(see abstract-syntax-well-formedness)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection wfp-of-desugar
  :short "Desugaring preserves well-formedness."

  (defrule ispace-list-wfp-of-ispace-list-desugar-in-splice
    (equal (ispace-list-wfp (ispace-list-desugar-in-splice ispaces))
           (ispace-list-wfp ispaces))
    :induct t
    :enable (ispace-list-desugar-in-splice
             ispace-desugar-in-splice
             ispace-wfp
             ast-wfp-rules))

  (defret-mutual wfp-of-shapes/ispaces-desugar
    (defret shape-wfp-of-shape-desugar
      (shape-wfp result)
      :hyp (shape-wfp shape)
      :fn shape-desugar)
    (defret shape-list-wfp-of-shape-list-desugar
      (shape-list-wfp result)
      :hyp (shape-list-wfp shape-list)
      :fn shape-list-desugar)
    (defret ispace-wfp-of-ispace-desugar
      (ispace-wfp result)
      :hyp (ispace-wfp ispace)
      :fn ispace-desugar)
    (defret ispace-list-wfp-of-ispace-list-desugar
      (ispace-list-wfp result)
      :hyp (ispace-list-wfp ispace-list)
      :fn ispace-list-desugar)
    :mutual-recursion shapes/ispaces-desugar
    :hints (("Goal" :in-theory (enable* shape-desugar
                                        shape-list-desugar
                                        ispace-desugar
                                        ispace-list-desugar
                                        shape-wfp
                                        shape-list-wfp
                                        ispace-wfp
                                        ispace-list-wfp
                                        dim-list-wfp
                                        ast-wfp-rules))))

  (defret-mutual wfp-of-types-desugar
    (defret type-wfp-of-type-desugar
      (type-wfp result)
      :hyp (type-wfp type)
      :fn type-desugar)
    (defret type-list-wfp-of-type-list-desugar
      (type-list-wfp result)
      :hyp (type-list-wfp type-list)
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable* type-desugar
                                        type-list-desugar
                                        type-wfp
                                        type-list-wfp
                                        ast-wfp-rules))))

  (defret type-option-wfp-of-type-option-desugar
    (type-option-wfp result)
    :hyp (type-option-wfp type-option)
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-wfp
                                       type-option-some->val))))

  (defret var+type?-wfp-of-var+type?-desugar
    (var+type?-wfp result)
    :hyp (var+type?-wfp var+type?)
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar
                                       var+type?-wfp))))

  (defret var+type?-list-wfp-of-var+type?-list-desugar
    (var+type?-list-wfp result)
    :hyp (var+type?-list-wfp var+type?-list)
    :fn var+type?-list-desugar
    :hints (("Goal"
             :induct t
             :in-theory (enable* var+type?-list-desugar
                                 ast-wfp-rules))))

  (defret-mutual wfp-of-exprs/atoms/binds-desugar
    (defret expr-wfp-of-expr-desugar
      (expr-wfp result)
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-wfp-of-expr-list-desugar
      (expr-list-wfp result)
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-wfp-of-atom-desugar
      (atom-wfp result)
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-wfp-of-atom-list-desugar
      (atom-list-wfp result)
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-wfp-of-bind-desugar
      (bind-wfp result)
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-wfp-of-bind-list-desugar
      (bind-list-wfp result)
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable* expr-desugar
                                        expr-list-desugar
                                        atom-desugar
                                        atom-list-desugar
                                        bind-desugar
                                        bind-list-desugar
                                        expr-wfp
                                        expr-list-wfp
                                        atom-wfp
                                        atom-list-wfp
                                        bind-wfp
                                        bind-list-wfp
                                        type-option-wfp
                                        type-list-option-wfp
                                        ispace-list-option-wfp
                                        type-var-list-option-wfp
                                        ispace-var-list-option-wfp
                                        ast-wfp-rules
                                        ast-desugar-rules
                                        type-option-some->val)))))
