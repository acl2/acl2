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
(include-book "bound-variables-under-desugaring")
(include-book "free-variable-operations")
(include-book "desugaring")

(local (include-book "osets"))

(local (include-book "kestrel/lists-light/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* ast-free-ispace-vars-rules
                           ast-free-type-vars-rules
                           ast-free-expr-vars-rules
                           ast-wfp-rules
                           ast-desugar-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ free-variables-under-desugaring
  :parents (abstract-syntax-well-formedness)
  :short "Preservation of free variables under desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that desugaring preserves the free variables of ASTs:
     a desugared AST has the same free ispace, type, and expression variables
     as the original AST.")
   (xdoc::p
    "The theorems about expressions, atoms, and bindings
     have well-formedness hypotheses:
     desugaring does not preserve the free variables of
     certain ill-formed ASTs,
     namely n-ary abstractions with no parameters,
     whose desugaring introduces a spurious parameter,
     and n-ary unboxing expressions with no ispace variables,
     whose desugaring drops the target;
     well-formedness excludes these ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-ispace-vars-of-desugar
  :short "Desugaring preserves the free ispace variables."

  (defrule ispace-list-free-ispace-vars-of-ispace-list-desugar-in-splice
    (equal (ispace-list-free-ispace-vars
            (ispace-list-desugar-in-splice ispaces))
           (ispace-list-free-ispace-vars ispaces))
    :induct t
    :enable (ispace-list-desugar-in-splice
             ispace-desugar-in-splice
             ispace-free-ispace-vars))

  (defret-mutual free-ispace-vars-of-shapes/ispaces-desugar
    (defret shape-free-ispace-vars-of-shape-desugar
      (equal (shape-free-ispace-vars result)
             (shape-free-ispace-vars shape))
      :fn shape-desugar)
    (defret shape-list-free-ispace-vars-of-shape-list-desugar
      (equal (shape-list-free-ispace-vars result)
             (shape-list-free-ispace-vars shape-list))
      :fn shape-list-desugar)
    (defret ispace-free-ispace-vars-of-ispace-desugar
      (equal (ispace-free-ispace-vars result)
             (ispace-free-ispace-vars ispace))
      :fn ispace-desugar)
    (defret ispace-list-free-ispace-vars-of-ispace-list-desugar
      (equal (ispace-list-free-ispace-vars result)
             (ispace-list-free-ispace-vars ispace-list))
      :fn ispace-list-desugar)
    :mutual-recursion shapes/ispaces-desugar
    :hints (("Goal"
             :in-theory
             (enable shape-desugar
                     shape-list-desugar
                     ispace-desugar
                     ispace-list-desugar
                     shape-free-ispace-vars
                     shape-list-free-ispace-vars
                     ispace-free-ispace-vars
                     ispace-list-free-ispace-vars
                     dim-list-free-ispace-vars
                     shape-list-free-ispace-vars-of-shape-dims-list))))

  (defret-mutual free-ispace-vars-of-types-desugar
    (defret type-free-ispace-vars-of-type-desugar
      (equal (type-free-ispace-vars result)
             (type-free-ispace-vars type))
      :fn type-desugar)
    (defret type-list-free-ispace-vars-of-type-list-desugar
      (equal (type-list-free-ispace-vars result)
             (type-list-free-ispace-vars type-list))
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar
                                       type-list-desugar
                                       type-free-ispace-vars
                                       type-list-free-ispace-vars))))

  (defret type-option-free-ispace-vars-of-type-option-desugar
    (equal (type-option-free-ispace-vars result)
           (type-option-free-ispace-vars type-option))
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-free-ispace-vars
                                       type-option-some->val))))

  (defret var+type?-free-ispace-vars-of-var+type?-desugar
    (equal (var+type?-free-ispace-vars result)
           (var+type?-free-ispace-vars var+type?))
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar
                                       var+type?-free-ispace-vars))))

  (defret var+type?-list-free-ispace-vars-of-var+type?-list-desugar
    (equal (var+type?-list-free-ispace-vars result)
           (var+type?-list-free-ispace-vars var+type?-list))
    :fn var+type?-list-desugar
    :hints (("Goal"
             :induct t
             :in-theory (enable var+type?-list-desugar
                                var+type?-list-free-ispace-vars))))

  (defrulel ispace-list-free-ispace-vars-fold
    (implies (consp ispaces)
             (equal (set::union (ispace-free-ispace-vars (car ispaces))
                                (ispace-list-free-ispace-vars (cdr ispaces)))
                    (ispace-list-free-ispace-vars ispaces))))

  (defrulel var+type?-list-free-ispace-vars-fold
    (implies (consp var+type?s)
             (equal (set::union (var+type?-free-ispace-vars (car var+type?s))
                                (var+type?-list-free-ispace-vars
                                 (cdr var+type?s)))
                    (var+type?-list-free-ispace-vars var+type?s))))

  (defret-mutual free-ispace-vars-of-exprs/atoms/binds-desugar
    (defret expr-free-ispace-vars-of-expr-desugar
      (equal (expr-free-ispace-vars result)
             (expr-free-ispace-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-free-ispace-vars-of-expr-list-desugar
      (equal (expr-list-free-ispace-vars result)
             (expr-list-free-ispace-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-free-ispace-vars-of-atom-desugar
      (equal (atom-free-ispace-vars result)
             (atom-free-ispace-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-free-ispace-vars-of-atom-list-desugar
      (equal (atom-list-free-ispace-vars result)
             (atom-list-free-ispace-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-free-ispace-vars-of-bind-desugar
      (equal (bind-free-ispace-vars result)
             (bind-free-ispace-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-free-ispace-vars-of-bind-list-desugar
      (equal (bind-list-free-ispace-vars result)
             (bind-list-free-ispace-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-free-ispace-vars
                                       expr-list-free-ispace-vars
                                       atom-free-ispace-vars
                                       atom-list-free-ispace-vars
                                       bind-free-ispace-vars
                                       bind-list-free-ispace-vars
                                       type-option-free-ispace-vars
                                       type-list-option-free-ispace-vars
                                       ispace-list-option-free-ispace-vars
                                       expr-wfp
                                       expr-list-wfp
                                       atom-wfp
                                       atom-list-wfp
                                       bind-wfp
                                       bind-list-wfp
                                       type-option-some->val
                                       acl2::consp-of-cdr
                                       consp-of-cdr-of-atom-lambdan->params
                                       len->=-2-when-consp-of-cdr
                                       union-of-differences
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-type-vars-of-desugar
  :short "Desugaring preserves the free type variables."

  (defret-mutual free-type-vars-of-types-desugar
    (defret type-free-type-vars-of-type-desugar
      (equal (type-free-type-vars result)
             (type-free-type-vars type))
      :fn type-desugar)
    (defret type-list-free-type-vars-of-type-list-desugar
      (equal (type-list-free-type-vars result)
             (type-list-free-type-vars type-list))
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar
                                       type-list-desugar
                                       type-free-type-vars
                                       type-list-free-type-vars))))

  (defret type-option-free-type-vars-of-type-option-desugar
    (equal (type-option-free-type-vars result)
           (type-option-free-type-vars type-option))
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-free-type-vars
                                       type-option-some->val))))

  (defret var+type?-free-type-vars-of-var+type?-desugar
    (equal (var+type?-free-type-vars result)
           (var+type?-free-type-vars var+type?))
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar
                                       var+type?-free-type-vars))))

  (defret var+type?-list-free-type-vars-of-var+type?-list-desugar
    (equal (var+type?-list-free-type-vars result)
           (var+type?-list-free-type-vars var+type?-list))
    :fn var+type?-list-desugar
    :hints (("Goal"
             :induct t
             :in-theory (enable var+type?-list-desugar
                                var+type?-list-free-type-vars))))

  (defrulel var+type?-list-free-type-vars-fold
    (implies (consp var+type?s)
             (equal (set::union (var+type?-free-type-vars (car var+type?s))
                                (var+type?-list-free-type-vars
                                 (cdr var+type?s)))
                    (var+type?-list-free-type-vars var+type?s))))

  (defret-mutual free-type-vars-of-exprs/atoms/binds-desugar
    (defret expr-free-type-vars-of-expr-desugar
      (equal (expr-free-type-vars result)
             (expr-free-type-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-free-type-vars-of-expr-list-desugar
      (equal (expr-list-free-type-vars result)
             (expr-list-free-type-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-free-type-vars-of-atom-desugar
      (equal (atom-free-type-vars result)
             (atom-free-type-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-free-type-vars-of-atom-list-desugar
      (equal (atom-list-free-type-vars result)
             (atom-list-free-type-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-free-type-vars-of-bind-desugar
      (equal (bind-free-type-vars result)
             (bind-free-type-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-free-type-vars-of-bind-list-desugar
      (equal (bind-list-free-type-vars result)
             (bind-list-free-type-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-free-type-vars
                                       expr-list-free-type-vars
                                       atom-free-type-vars
                                       atom-list-free-type-vars
                                       bind-free-type-vars
                                       bind-list-free-type-vars
                                       type-option-free-type-vars
                                       type-list-option-free-type-vars
                                       expr-wfp
                                       expr-list-wfp
                                       atom-wfp
                                       atom-list-wfp
                                       bind-wfp
                                       bind-list-wfp
                                       type-option-some->val
                                       acl2::consp-of-cdr
                                       consp-of-cdr-of-atom-lambdan->params
                                       len->=-2-when-consp-of-cdr
                                       union-of-differences
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection free-expr-vars-of-desugar
  :short "Desugaring preserves the free expression variables."

  (defret-mutual free-expr-vars-of-exprs/atoms/binds-desugar
    (defret expr-free-expr-vars-of-expr-desugar
      (equal (expr-free-expr-vars result)
             (expr-free-expr-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-free-expr-vars-of-expr-list-desugar
      (equal (expr-list-free-expr-vars result)
             (expr-list-free-expr-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-free-expr-vars-of-atom-desugar
      (equal (atom-free-expr-vars result)
             (atom-free-expr-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-free-expr-vars-of-atom-list-desugar
      (equal (atom-list-free-expr-vars result)
             (atom-list-free-expr-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-free-expr-vars-of-bind-desugar
      (equal (bind-free-expr-vars result)
             (bind-free-expr-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-free-expr-vars-of-bind-list-desugar
      (equal (bind-list-free-expr-vars result)
             (bind-list-free-expr-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-free-expr-vars
                                       expr-list-free-expr-vars
                                       atom-free-expr-vars
                                       atom-list-free-expr-vars
                                       bind-free-expr-vars
                                       bind-list-free-expr-vars
                                       expr-wfp
                                       expr-list-wfp
                                       atom-wfp
                                       atom-list-wfp
                                       bind-wfp
                                       bind-list-wfp
                                       var+type?-list->var
                                       acl2::consp-of-cdr
                                       consp-of-cdr-of-atom-lambdan->params
                                       len->=-2-when-consp-of-cdr
                                       mergesort-when-consp)))))
