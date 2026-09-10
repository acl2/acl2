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
(include-book "all-variable-operations")
(include-book "desugaring")

(local (include-book "osets"))

(local (include-book "kestrel/lists-light/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* ast-all-ispace-vars-rules
                           ast-all-type-vars-rules
                           ast-all-expr-vars-rules
                           ast-wfp-rules
                           ast-desugar-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ all-variables-under-desugaring
  :parents (abstract-syntax-variable-operations)
  :short "Preservation of all (i.e. free and bound) variables
          under desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that desugaring preserves all the variables of ASTs:
     a desugared AST has the same
     ispace, type, and expression variables as the original AST.")
   (xdoc::p
    "The theorems about expressions, atoms, and bindings
     have well-formedness hypotheses:
     desugaring does not preserve the variables of
     certain ill-formed ASTs,
     namely n-ary abstractions with no parameters,
     whose desugaring introduces a spurious parameter,
     and n-ary unboxing expressions with no ispace variables,
     whose desugaring drops the target;
     well-formedness excludes these ASTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection all-ispace-vars-of-desugar
  :short "Desugaring preserves all the ispace variables."

  (defrule ispace-list-all-ispace-vars-of-ispace-list-desugar-in-splice
    (equal (ispace-list-all-ispace-vars
            (ispace-list-desugar-in-splice ispaces))
           (ispace-list-all-ispace-vars ispaces))
    :induct t
    :enable (ispace-list-desugar-in-splice
             ispace-desugar-in-splice
             ispace-all-ispace-vars))

  (defret-mutual all-ispace-vars-of-shapes/ispaces-desugar
    (defret shape-all-ispace-vars-of-shape-desugar
      (equal (shape-all-ispace-vars result)
             (shape-all-ispace-vars shape))
      :fn shape-desugar)
    (defret shape-list-all-ispace-vars-of-shape-list-desugar
      (equal (shape-list-all-ispace-vars result)
             (shape-list-all-ispace-vars shape-list))
      :fn shape-list-desugar)
    (defret ispace-all-ispace-vars-of-ispace-desugar
      (equal (ispace-all-ispace-vars result)
             (ispace-all-ispace-vars ispace))
      :fn ispace-desugar)
    (defret ispace-list-all-ispace-vars-of-ispace-list-desugar
      (equal (ispace-list-all-ispace-vars result)
             (ispace-list-all-ispace-vars ispace-list))
      :fn ispace-list-desugar)
    :mutual-recursion shapes/ispaces-desugar
    :hints (("Goal" :in-theory (enable shape-desugar
                                       shape-list-desugar
                                       ispace-desugar
                                       ispace-list-desugar
                                       shape-all-ispace-vars
                                       shape-list-all-ispace-vars
                                       ispace-all-ispace-vars
                                       ispace-list-all-ispace-vars
                                       dim-list-all-ispace-vars))))

  (defret-mutual all-ispace-vars-of-types-desugar
    (defret type-all-ispace-vars-of-type-desugar
      (equal (type-all-ispace-vars result)
             (type-all-ispace-vars type))
      :fn type-desugar)
    (defret type-list-all-ispace-vars-of-type-list-desugar
      (equal (type-list-all-ispace-vars result)
             (type-list-all-ispace-vars type-list))
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar
                                       type-list-desugar
                                       type-all-ispace-vars
                                       type-list-all-ispace-vars))))

  (defret type-option-all-ispace-vars-of-type-option-desugar
    (equal (type-option-all-ispace-vars result)
           (type-option-all-ispace-vars type-option))
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-all-ispace-vars
                                       type-option-some->val))))

  (defret var+type?-all-ispace-vars-of-var+type?-desugar
    (equal (var+type?-all-ispace-vars result)
           (var+type?-all-ispace-vars var+type?))
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar
                                       var+type?-all-ispace-vars))))

  (defret var+type?-list-all-ispace-vars-of-var+type?-list-desugar
    (equal (var+type?-list-all-ispace-vars result)
           (var+type?-list-all-ispace-vars var+type?-list))
    :fn var+type?-list-desugar
    :hints (("Goal"
             :induct t
             :in-theory (enable var+type?-list-desugar
                                var+type?-list-all-ispace-vars))))

  (defrulel ispace-list-all-ispace-vars-fold
    (implies (consp ispaces)
             (equal (set::union (ispace-all-ispace-vars (car ispaces))
                                (ispace-list-all-ispace-vars (cdr ispaces)))
                    (ispace-list-all-ispace-vars ispaces))))

  (defrulel var+type?-list-all-ispace-vars-fold
    (implies (consp var+type?s)
             (equal (set::union (var+type?-all-ispace-vars (car var+type?s))
                                (var+type?-list-all-ispace-vars
                                 (cdr var+type?s)))
                    (var+type?-list-all-ispace-vars var+type?s))))

  (defret-mutual all-ispace-vars-of-exprs/atoms/binds-desugar
    (defret expr-all-ispace-vars-of-expr-desugar
      (equal (expr-all-ispace-vars result)
             (expr-all-ispace-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-all-ispace-vars-of-expr-list-desugar
      (equal (expr-list-all-ispace-vars result)
             (expr-list-all-ispace-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-all-ispace-vars-of-atom-desugar
      (equal (atom-all-ispace-vars result)
             (atom-all-ispace-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-all-ispace-vars-of-atom-list-desugar
      (equal (atom-list-all-ispace-vars result)
             (atom-list-all-ispace-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-all-ispace-vars-of-bind-desugar
      (equal (bind-all-ispace-vars result)
             (bind-all-ispace-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-all-ispace-vars-of-bind-list-desugar
      (equal (bind-list-all-ispace-vars result)
             (bind-list-all-ispace-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-all-ispace-vars
                                       expr-list-all-ispace-vars
                                       atom-all-ispace-vars
                                       atom-list-all-ispace-vars
                                       bind-all-ispace-vars
                                       bind-list-all-ispace-vars
                                       type-option-all-ispace-vars
                                       type-list-option-all-ispace-vars
                                       ispace-list-option-all-ispace-vars
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
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection all-type-vars-of-desugar
  :short "Desugaring preserves all the type variables."

  (defret-mutual all-type-vars-of-types-desugar
    (defret type-all-type-vars-of-type-desugar
      (equal (type-all-type-vars result)
             (type-all-type-vars type))
      :fn type-desugar)
    (defret type-list-all-type-vars-of-type-list-desugar
      (equal (type-list-all-type-vars result)
             (type-list-all-type-vars type-list))
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar
                                       type-list-desugar
                                       type-all-type-vars
                                       type-list-all-type-vars))))

  (defret type-option-all-type-vars-of-type-option-desugar
    (equal (type-option-all-type-vars result)
           (type-option-all-type-vars type-option))
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-all-type-vars
                                       type-option-some->val))))

  (defret var+type?-all-type-vars-of-var+type?-desugar
    (equal (var+type?-all-type-vars result)
           (var+type?-all-type-vars var+type?))
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar
                                       var+type?-all-type-vars))))

  (defret var+type?-list-all-type-vars-of-var+type?-list-desugar
    (equal (var+type?-list-all-type-vars result)
           (var+type?-list-all-type-vars var+type?-list))
    :fn var+type?-list-desugar
    :hints (("Goal"
             :induct t
             :in-theory (enable var+type?-list-desugar
                                var+type?-list-all-type-vars))))

  (defrulel var+type?-list-all-type-vars-fold
    (implies (consp var+type?s)
             (equal (set::union (var+type?-all-type-vars (car var+type?s))
                                (var+type?-list-all-type-vars
                                 (cdr var+type?s)))
                    (var+type?-list-all-type-vars var+type?s))))

  (defret-mutual all-type-vars-of-exprs/atoms/binds-desugar
    (defret expr-all-type-vars-of-expr-desugar
      (equal (expr-all-type-vars result)
             (expr-all-type-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-all-type-vars-of-expr-list-desugar
      (equal (expr-list-all-type-vars result)
             (expr-list-all-type-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-all-type-vars-of-atom-desugar
      (equal (atom-all-type-vars result)
             (atom-all-type-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-all-type-vars-of-atom-list-desugar
      (equal (atom-list-all-type-vars result)
             (atom-list-all-type-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-all-type-vars-of-bind-desugar
      (equal (bind-all-type-vars result)
             (bind-all-type-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-all-type-vars-of-bind-list-desugar
      (equal (bind-list-all-type-vars result)
             (bind-list-all-type-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-all-type-vars
                                       expr-list-all-type-vars
                                       atom-all-type-vars
                                       atom-list-all-type-vars
                                       bind-all-type-vars
                                       bind-list-all-type-vars
                                       type-option-all-type-vars
                                       type-list-option-all-type-vars
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
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection all-expr-vars-of-desugar
  :short "Desugaring preserves all the expression variables."

  (defret-mutual all-expr-vars-of-exprs/atoms/binds-desugar
    (defret expr-all-expr-vars-of-expr-desugar
      (equal (expr-all-expr-vars result)
             (expr-all-expr-vars expr))
      :hyp (expr-wfp expr)
      :fn expr-desugar)
    (defret expr-list-all-expr-vars-of-expr-list-desugar
      (equal (expr-list-all-expr-vars result)
             (expr-list-all-expr-vars expr-list))
      :hyp (expr-list-wfp expr-list)
      :fn expr-list-desugar)
    (defret atom-all-expr-vars-of-atom-desugar
      (equal (atom-all-expr-vars result)
             (atom-all-expr-vars atom))
      :hyp (atom-wfp atom)
      :fn atom-desugar)
    (defret atom-list-all-expr-vars-of-atom-list-desugar
      (equal (atom-list-all-expr-vars result)
             (atom-list-all-expr-vars atom-list))
      :hyp (atom-list-wfp atom-list)
      :fn atom-list-desugar)
    (defret bind-all-expr-vars-of-bind-desugar
      (equal (bind-all-expr-vars result)
             (bind-all-expr-vars bind))
      :hyp (bind-wfp bind)
      :fn bind-desugar)
    (defret bind-list-all-expr-vars-of-bind-list-desugar
      (equal (bind-list-all-expr-vars result)
             (bind-list-all-expr-vars bind-list))
      :hyp (bind-list-wfp bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable expr-desugar
                                       expr-list-desugar
                                       atom-desugar
                                       atom-list-desugar
                                       bind-desugar
                                       bind-list-desugar
                                       expr-all-expr-vars
                                       expr-list-all-expr-vars
                                       atom-all-expr-vars
                                       atom-list-all-expr-vars
                                       bind-all-expr-vars
                                       bind-list-all-expr-vars
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
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))
