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

(local (in-theory (enable* ast-all-type-vars-rules
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
     type and expression variables as the original AST.")
   (xdoc::p
    "The theorems about expressions, atoms, and bindings
     have well-formedness hypotheses:
     desugaring does not preserve the variables of
     certain ill-formed ASTs,
     namely n-ary abstractions with no parameters,
     whose desugaring introduces a spurious parameter,
     and n-ary unboxing expressions with no ispace variables,
     whose desugaring drops the target;
     well-formedness excludes these ASTs.")
   (xdoc::p
    "The theorems for the ispace variables are not here yet:
     they do not hold for @(tsee ast-all-ispace-vars) as currently defined,
     because that operation does not include
     the ispace variables introduced by
     ispace abstractions and unboxing expressions
     (unlike @(tsee ast-all-type-vars), which includes
     the type variables introduced by type abstractions,
     and unlike @(tsee ast-all-expr-vars), which includes
     the expression variables introduced by
     expression abstractions and unboxing expressions).
     Since desugaring turns
     the ispace parameters of combined function bindings
     into ispace abstractions,
     those variables are lost."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: ispace vars (see the discussion in the topic above)

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
                                       mergesort-when-consp
                                       set::union-symmetric
                                       set::union-commutative)))))
