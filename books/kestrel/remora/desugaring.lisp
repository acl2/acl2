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
(include-book "abstract-syntax-structurals")
(include-book "character-literal-codes")

(include-book "kestrel/fty/deffold-map" :dir :system)

(acl2::controlled-configuration)

(local (in-theory (enable* ast-corep-rules)))

(local (in-theory (enable typep-when-result-not-error
                          type-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ desugaring
  :parents (abstract-syntax)
  :short "Abstract syntax desugaring."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a desugaring transformation from all ASTs to the core ASTs.")
   (xdoc::p
    "In [impl], this is done during parsing,
     on the fly as ASTs as constructed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-lit-desugar ((clit char-litp))
  :returns (ilit int-litp)
  :short "Desugar a character literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Character literals are only used in string literals,
     which desugar to array expressions
     whose atoms are integers that are the codes of the character literals.
     So here we desugar a character literal to an integer literal:
     we obtain the code of the character literal
     and we represent it with the minimum number of digits without sign."))
  (make-int-lit :sign? nil
                :digits (str::nat-to-dec-chars (char-lit-code clit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection char-lit-list-desugar ((x char-lit-listp))
  :returns (ilits int-lit-listp)
  :short "Lift @(tsee char-lit-desugar)."
  (char-lit-desugar x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-desugar-in-splice ((ispace ispacep))
  :returns (new-ispace ispacep)
  :short "Desugar an ispace that occurs in a shape splice."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since shape splices are desugared to shape concatenations,
     we need to turn dimensions into singleton shapes.
     This is done by this ACL2 function."))
  (ispace-case
   ispace
   :dim (ispace-shape (shape-dims (list ispace.dim)))
   :shape (ispace-fix ispace))

  ///

  (defret ispace-kind-of-ispace-desugar-in-splice
    (equal (ispace-kind new-ispace) :shape))

  (defrule ispace-corep-of-ispace-desugar-in-splice
    (equal (ispace-corep (ispace-desugar-in-splice ispace))
           (ispace-corep ispace))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-list-desugar-in-splice ((x ispace-listp))
  :returns (new-ispaces ispace-listp)
  :short "Lift @(tsee ispace-desugar-in-splice) to lists."
  (ispace-desugar-in-splice x)

  ///

  (defret ispace-list-case-shape-of-ispace-list-desugar-in-splice
    (ispace-list-case-shape new-ispaces)
    :hints (("Goal" :induct t)))

  (defrule ispace-list-corep-of-ispace-list-desugar-in-splice
    (equal (ispace-list-corep (ispace-list-desugar-in-splice ispaces))
           (ispace-list-corep ispaces))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-map desugar
  :short "Desugar ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A shape with a list of zero or more dimensions is handled as follows:
     if the shape has no dimensions, it is turned into the empty concatenation;
     if the shape has one dimension, it is left unchanges;
     if the shape has two or more dimensions,
     it is turned into the concanetation of the singletons of the dimensions.")
   (xdoc::p
    "A shape splice is turned into a concatenation.")
   (xdoc::p
    "A bracket type is turned into an array type
     whose shape is the concatenation of the shapes.")
   (xdoc::p
    "An atom expression is turned into a 0-rank array expression.")
   (xdoc::p
    "A non-empty string is turned into an array expression
     with the length of the string as its single dimension
     and with the characters, converted to integers, as atoms.
     The empty string is turned into an empty array expression
     with the type of integers.")
   (xdoc::p
    "A combined application is turned into its constituent applications,
     also based on whether type and ispace arguments are present or not.")
   (xdoc::p
    "A bracket expression is turned into a frame expression
     with a single dimension that is the number of sub-expressions,
     and the sub-expressions as arguments.
     Bracket expressions are never empty in concrete syntax;
     we should carry that invariant to the AST here.")
   (xdoc::p
    "All function bindings are turned into value bindings,
     with an appropriate lambda abstraction.
     As explained in @(tsee ast-corep),
     in general it is not possible to desugar @('let'),
     but at least we can desugar its function bindings.
     If the function binding includes the optional type,
     then the value binding includes the optional type as well,
     obtained by combining the function binding's type
     with parts of the function binding:
     for a term function binding, it is a function type;
     for a type function binding, it is a universal type;
     for an ispace function binding, it is a product type.
     A combined function binding results in nested lambda abstractions."))
  :types (shapes/ispaces
          ispace-list-option
          types
          type-option
          var+type?
          var+type?-list
          exprs/atoms/binds)
  :override
  ((shape :dims (cond ((endp shape.dims) ; no dimensions
                       (shape-append nil))
                      ((endp (cdr shape.dims)) ; one dimension
                       (shape-fix shape))
                      (t ; two or more dimensions
                       (shape-append
                        (shape-dims-list (list-to-singletons shape.dims))))))
   (shape :splice (shape-append
                   (ispace-shape-list->shape
                    (ispace-list-desugar-in-splice
                     (ispace-list-desugar shape.ispaces)))))
   (type :bracket (make-type-array
                   :elem (type-desugar type.elem)
                   :ispace (ispace-shape
                            (shape-append
                             (ispace-shape-list->shape
                              (ispace-list-desugar-in-splice
                               (ispace-list-desugar type.ispaces)))))))
   (expr :atom (make-expr-array :dims nil
                                :atoms (list (atom-desugar expr.atom))))
   (expr :string (if (consp expr.chars)
                     (make-expr-array
                      :dims (list (len expr.chars))
                      :atoms (atom-base-list
                              (base-lit-int-list
                               (char-lit-list-desugar expr.chars))))
                     (make-expr-array-empty :dims (list 0)
                                            :type (type-base (base-type-int)))))
   (expr :capp (b* ((fun (expr-desugar expr.fun))
                    (fun-targs
                     (type-list-option-case
                      expr.targs
                      :some (make-expr-tapp
                             :fun fun
                             :args (type-list-desugar expr.targs.val))
                      :none fun))
                    (fun-targs-iargs
                     (ispace-list-option-case
                      expr.iargs
                      :some (make-expr-iappn
                             :fun fun-targs
                             :args (ispace-list-desugar expr.iargs.val))
                      :none fun-targs))
                    (fun-targs-iargs-args
                     (make-expr-app
                      :fun fun-targs-iargs
                      :args (expr-list-desugar expr.args))))
                 fun-targs-iargs-args))
   (expr :bracket (b* ((exprs (expr-list-desugar expr.exprs)))
                    (make-expr-frame :dims (list (len exprs))
                                     :exprs exprs)))
   (bind :fun (b* ((params (var+type?-list-desugar bind.params))
                   (type? (type-option-desugar bind.type?))
                   (expr (expr-desugar bind.expr))
                   (lambda-type?
                    (type-option-case
                     type?
                     :some (b* ((in (var+type?-list->type-list-or-err params)))
                             (if (reserrp in)
                                 nil
                               (make-type-fun :in in :out type?.val)))
                     :none nil))
                   (lambda-expr
                    (make-expr-array
                     :dims nil
                     :atoms (list (make-atom-lambda :params params
                                                    :body expr
                                                    :type? type?)))))
                (make-bind-val :var bind.var
                               :type? lambda-type?
                               :expr lambda-expr)))
   (bind :tfun (b* ((type? (type-option-desugar bind.type?))
                    (expr (expr-desugar bind.expr))
                    (lambda-type?
                     (type-option-case
                      type?
                      :some (make-type-forall :params bind.params
                                              :body type?.val)
                      :none nil))
                    (lambda-expr
                     (make-expr-array
                      :dims nil
                      :atoms (list (make-atom-tlambda :params bind.params
                                                      :body expr)))))
                 (make-bind-val :var bind.var
                                :type? lambda-type?
                                :expr lambda-expr)))
   (bind :ifun (b* ((type? (type-option-desugar bind.type?))
                    (expr (expr-desugar bind.expr))
                    (lambda-type?
                     (type-option-case
                      type?
                      :some (make-type-pi :params bind.params
                                          :body type?.val)
                      :none nil))
                    (lambda-expr
                     (make-expr-array
                      :dims nil
                      :atoms (list (make-atom-ilambdan :params bind.params
                                                       :body expr)))))
                 (make-bind-val :var bind.var
                                :type? lambda-type?
                                :expr lambda-expr)))
   (bind :cfun (b* ((params (var+type?-list-desugar bind.params))
                    (type (type-desugar bind.type))
                    (expr (expr-desugar bind.expr))
                    (lambda-expr
                     (make-expr-array
                      :dims nil
                      :atoms (list (make-atom-lambda :params params
                                                     :body expr
                                                     :type? type))))
                    (ilambda-lambda-expr
                     (ispace-var-list-option-case
                      bind.iparams?
                      :some (make-expr-array
                             :dims nil
                             :atoms (list (make-atom-ilambdan
                                           :params bind.iparams?.val
                                           :body lambda-expr)))
                      :none lambda-expr))
                    (tlambda-ilambda-lambda-expr
                     (type-var-list-option-case
                      bind.tparams?
                      :some (make-expr-array
                             :dims nil
                             :atoms (list (make-atom-tlambda
                                           :params bind.tparams?.val
                                           :body ilambda-lambda-expr)))
                      :none ilambda-lambda-expr))
                    (in (var+type?-list->type-list-or-err params))
                    (lambda-type?
                     (if (reserrp in)
                         nil
                       (b* ((lambda-type (make-type-fun :in in :out type))
                            (ilambda-lambda-type
                             (ispace-var-list-option-case
                              bind.iparams?
                              :some (make-type-pi :params bind.iparams?.val
                                                  :body lambda-type)
                              :none lambda-type)))
                         (type-var-list-option-case
                          bind.tparams?
                          :some (make-type-forall :params bind.tparams?.val
                                                  :body ilambda-lambda-type)
                          :none ilambda-lambda-type)))))
                 (make-bind-val :var bind.var
                                :type? lambda-type?
                                :expr tlambda-ilambda-lambda-expr))))
  :name ast-desugar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ast-desugar-additional-theorems
  :short "Additional theorems about the desugaring functions."

  (defruled type-option-desugar-iff
    (iff (type-option-desugar type)
         type)
    :enable type-option-desugar)

  (defruled type-option-desugar-to-type-desugar
    (implies x
             (equal (type-option-desugar x)
                    (type-desugar x)))
    :enable (type-option-desugar
             type-option-some->val))

  (add-to-ruleset ast-desugar-rules
                  '(type-option-desugar-iff
                    type-option-desugar-to-type-desugar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection corep-of-desugar
  :short "Desugaring always returns core ASTs."

  (defret-mutual shapes/ispaces-corep-of-shapes/ispaces-desugar
    (defret shape-corep-of-shape-desugar
      (shape-corep result)
      :fn shape-desugar)
    (defret shape-list-corep-of-shape-list-desugar
      (shape-list-corep result)
      :fn shape-list-desugar)
    (defret ispace-corep-of-ispace-desugar
      (ispace-corep result)
      :fn ispace-desugar)
    (defret ispace-list-corep-of-ispace-list-desugar
      (ispace-list-corep result)
      :fn ispace-list-desugar)
    :mutual-recursion shapes/ispaces-desugar
    :hints
    (("Goal"
      :in-theory
      (enable shape-desugar
              shape-list-desugar
              ispace-desugar
              ispace-list-desugar
              shape-list-corep-of-shape-dims-list-of-list-to-singletons))))

  (defret ispace-list-option-corep-of-ispace-list-option-desugar
    (ispace-list-option-corep result)
    :fn ispace-list-option-desugar
    :hints (("Goal" :in-theory (enable ispace-list-option-desugar))))

  (defret-mutual types-corep-of-types-desugar
    (defret type-corep-of-type-desugar
      (type-corep result)
      :fn type-desugar)
    (defret type-list-corep-of-type-list-desugar
      (type-list-corep result)
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints (("Goal" :in-theory (enable type-desugar type-list-desugar))))

  (defret type-option-corep-of-type-option-desugar
    (type-option-corep result)
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar))))

  (defret var+type?-corep-of-var+type?-desugar
    (var+type?-corep result)
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar))))

  (defret var+type?-list-corep-of-var+type?-list-desugar
    (var+type?-list-corep result)
    :fn var+type?-list-desugar
    :hints (("Goal" :induct t :in-theory (enable var+type?-list-desugar))))

  (defret-mutual exprs/atoms/binds-corep-of-exprs/atoms/binds-desugar
    (defret expr-corep-of-expr-desugar
      (expr-corep result)
      :fn expr-desugar)
    (defret expr-list-corep-of-expr-list-desugar
      (expr-list-corep result)
      :fn expr-list-desugar)
    (defret atom-corep-of-atom-desugar
      (atom-corep result)
      :fn atom-desugar)
    (defret atom-list-corep-of-atom-desugar
      (atom-list-corep result)
      :fn atom-list-desugar)
    (defret bind-corep-of-bind-desugar
      (bind-corep result)
      :fn bind-desugar)
    (defret bind-list-corep-of-bind-list-desugar
      (bind-list-corep result)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints
    (("Goal"
      :in-theory (enable* expr-desugar
                          expr-list-desugar
                          atom-desugar
                          atom-list-desugar
                          bind-desugar
                          bind-list-desugar
                          ast-desugar-rules
                          type-list-corep-of-var+type?-list->type-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection desugar-when-corep
  :short "Desugaring does nothing on core ASTs."

  (defret-mutual shapes/ispaces-desugar-when-shapes/ispaces-corep
    (defret shape-desugar-when-shape-corep
      (equal result (shape-fix shape))
      :hyp (shape-corep shape)
      :fn shape-desugar)
    (defret shape-list-desugar-when-shape-list-corep
      (equal result (shape-list-fix shape-list))
      :hyp (shape-list-corep shape-list)
      :fn shape-list-desugar)
    (defret ispace-desugar-when-ispace-corep
      (equal result (ispace-fix ispace))
      :hyp (ispace-corep ispace)
      :fn ispace-desugar)
    (defret ispace-list-desugar-when-ispace-list-corep
      (equal result (ispace-list-fix ispace-list))
      :hyp (ispace-list-corep ispace-list)
      :fn ispace-list-desugar)
    :mutual-recursion shapes/ispaces-desugar
    :hints
    (("Goal" :in-theory (enable shape-desugar
                                shape-list-desugar
                                ispace-desugar
                                ispace-list-desugar
                                shape-corep))))

  (defret ispace-list-option-desugar-when-ispace-list-option-corep
    (equal result (ispace-list-option-fix ispace-list-option))
    :hyp (ispace-list-option-corep ispace-list-option)
    :fn ispace-list-option-desugar
    :hints (("Goal" :in-theory (enable ispace-list-option-desugar))))

  (defret-mutual types-desugar-when-types-corep
    (defret type-desugar-when-type-corep
      (equal result (type-fix type))
      :hyp (type-corep type)
      :fn type-desugar)
    (defret type-list-desugar-when-type-list-corep
      (equal result (type-list-fix type-list))
      :hyp (type-list-corep type-list)
      :fn type-list-desugar)
    :mutual-recursion types-desugar
    :hints
    (("Goal" :in-theory (enable type-desugar type-list-desugar type-corep))))

  (defret type-option-desugar-when-type-option-corep
    (equal result (type-option-fix type-option))
    :hyp (type-option-corep type-option)
    :fn type-option-desugar
    :hints (("Goal" :in-theory (enable type-option-desugar
                                       type-option-some->val
                                       type-option-fix))))

  (defret var+type?-desugar-when-var+type?-corep
    (equal result (var+type?-fix var+type?))
    :hyp (var+type?-corep var+type?)
    :fn var+type?-desugar
    :hints (("Goal" :in-theory (enable var+type?-desugar))))

  (defret var+type?-list-desugar-when-var+type?-list-corep
    (equal result (var+type?-list-fix var+type?-list))
    :hyp (var+type?-list-corep var+type?-list)
    :fn var+type?-list-desugar
    :hints (("Goal" :induct t :in-theory (enable var+type?-list-desugar))))

  (defret-mutual exprs/atoms/binds-desugar-when-exprs/atoms/binds-corep
    (defret expr-desugar-when-expr-corep
      (equal result (expr-fix expr))
      :hyp (expr-corep expr)
      :fn expr-desugar)
    (defret expr-list-desugar-when-expr-list-corep
      (equal result (expr-list-fix expr-list))
      :hyp (expr-list-corep expr-list)
      :fn expr-list-desugar)
    (defret atom-desugar-when-atom-corep
      (equal result (atom-fix atom))
      :hyp (atom-corep atom)
      :fn atom-desugar)
    (defret atom-list-desugar-when-atom-list-corep
      (equal result (atom-list-fix atom-list))
      :hyp (atom-list-corep atom-list)
      :fn atom-list-desugar)
    (defret bind-desugar-when-bind-corep
      (equal result (bind-fix bind))
      :hyp (bind-corep bind)
      :fn bind-desugar)
    (defret bind-list-desugar-when-bind-list-corep
      (equal result (bind-list-fix bind-list))
      :hyp (bind-list-corep bind-list)
      :fn bind-list-desugar)
    :mutual-recursion exprs/atoms/binds-desugar
    :hints (("Goal" :in-theory (enable* expr-desugar
                                        expr-list-desugar
                                        atom-desugar
                                        atom-list-desugar
                                        bind-desugar
                                        bind-list-desugar
                                        expr-corep
                                        ast-corep-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection desugar-idempotent
  :short "Desugaring is idempotent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of
     @(tsee corep-of-desugar) and @(tsee desugar-when-corep)."))

  (defrule shape-desugar-idempotent
    (equal (shape-desugar (shape-desugar shape))
           (shape-desugar shape)))

  (defrule shape-list-desugar-idempotent
    (equal (shape-list-desugar (shape-list-desugar shapes))
           (shape-list-desugar shapes)))

  (defrule ispace-desugar-idempotent
    (equal (ispace-desugar (ispace-desugar ispace))
           (ispace-desugar ispace)))

  (defrule ispace-list-desugar-idempotent
    (equal (ispace-list-desugar (ispace-list-desugar ispaces))
           (ispace-list-desugar ispaces)))

  (defrule ispace-list-option-desugar-idempotent
    (equal (ispace-list-option-desugar (ispace-list-option-desugar ispaces?))
           (ispace-list-option-desugar ispaces?)))

  (defrule type-desugar-idempotent
    (equal (type-desugar (type-desugar type))
           (type-desugar type)))

  (defrule type-list-desugar-idempotent
    (equal (type-list-desugar (type-list-desugar types))
           (type-list-desugar types)))

  (defrule type-option-desugar-idempotent
    (equal (type-option-desugar (type-option-desugar type?))
           (type-option-desugar type?)))

  (defrule var+type?-desugar-idempotent
    (equal (var+type?-desugar (var+type?-desugar var+type?))
           (var+type?-desugar var+type?)))

  (defrule var+type?-list-desugar-idempotent
    (equal (var+type?-list-desugar (var+type?-list-desugar var+type?s))
           (var+type?-list-desugar var+type?s)))

  (defrule expr-desugar-idempotent
    (equal (expr-desugar (expr-desugar expr))
           (expr-desugar expr)))

  (defrule expr-list-desugar-idempotent
    (equal (expr-list-desugar (expr-list-desugar exprs))
           (expr-list-desugar exprs)))

  (defrule atom-desugar-idempotent
    (equal (atom-desugar (atom-desugar atom))
           (atom-desugar atom)))

  (defrule atom-list-desugar-idempotent
    (equal (atom-list-desugar (atom-list-desugar atoms))
           (atom-list-desugar atoms))))
