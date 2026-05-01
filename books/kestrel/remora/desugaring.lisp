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

(defines shapes-desugar
  :short "Desugar shapes and lists of shapes."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define shape-desugar ((shape shapep))
    :returns (core-shape shapep)
    :parents (abstract-syntax-desugaring shapes-desugar)
    :short "Desugar a shape."
    :long
    (xdoc::topstring
     (xdoc::p
      "A shape with a list of zero or more dimensions
       is turned into a concatenation of single-dimension shapes.")
     (xdoc::p
      "A shape splice is turned into a concatenation."))
    (shape-case
     shape
     :var (shape-var shape.name)
     :dim (shape-dim shape.dim)
     :dims (shape-append (shape-dim-list shape.dims))
     :append (shape-append (shape-list-desugar shape.shapes))
     :splice (shape-append (shape-list-desugar shape.shapes)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define shape-list-desugar ((shapes shape-listp))
    :returns (core-shapes shape-listp)
    :parents (abstract-syntax-desugaring shapes-desugar)
    :short "Desugar a list of shapes."
    (cond ((endp shapes) nil)
          (t (cons (shape-desugar (car shapes))
                   (shape-list-desugar (cdr shapes)))))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual shapes-desugar)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (std::defprojection shape-list-desugar (x)
    :parents nil
    (shape-desugar x)
    :already-definedp t)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual shapes-corep-of-shapes-desugar
    (defret shape-corep-of-shape-desugar
      (shape-corep core-shape)
      :fn shape-desugar)
    (defret shape-list-corep-of-shape-list-desugar
      (shape-list-corep core-shapes)
      :fn shape-list-desugar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-desugar ((ispace ispacep))
  :returns (core-ispace ispacep)
  :short "Desugar an ispace."
  (ispace-case
   ispace
   :dim (ispace-dim ispace.dim)
   :shape (ispace-shape (shape-desugar ispace.shape)))

  ///

  (defret ispace-corep-of-ispace-desugar
    (ispace-corep core-ispace)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection ispace-list-desugar ((x ispace-listp))
  :returns (core-ispaces ispace-listp)
  :short "Desugar a list of ispaces."
  (ispace-desugar x)

  ///

  (defret ispace-list-corep-of-ispace-list-desugar
    (ispace-list-corep core-ispaces)
    :fn ispace-list-desugar
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-list-option-desugar ((ispaces? ispace-list-optionp))
  :returns (core-ispaces? ispace-list-optionp)
  :short "Desugar an optional list of ispaces."
  (ispace-list-option-case
   ispaces?
   :some (ispace-list-option-some (ispace-list-desugar ispaces?.val))
   :none (ispace-list-option-none))

  ///

  (defret ispace-list-option-corep-of-ispace-list-option-desugar
    (ispace-list-option-corep core-ispaces?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines types-desugar
  :short "Desugar types and lists of types."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-desugar ((type typep))
    :returns (core-type typep)
    :parents (abstract-syntax-desugaring types-desugar)
    :short "Desugar a type."
    :long
    (xdoc::topstring
     (xdoc::p
      "A bracket type is turned into an array type
       whose shape is the concatenation of the shapes."))
    (type-case
     type
     :var (type-var type.var)
     :base (type-base type.type)
     :array (make-type-array :elem (type-desugar type.elem)
                             :shape (shape-desugar type.shape))
     :bracket (make-type-array :elem (type-desugar type.elem)
                               :shape (shape-append
                                       (shape-list-desugar type.shapes)))
     :fun (make-type-fun :in (type-list-desugar type.in)
                         :out (type-desugar type.out))
     :forall (make-type-forall :params type.params
                               :body (type-desugar type.body))
     :pi (make-type-pi :params type.params
                       :body (type-desugar type.body))
     :sigma (make-type-sigma :params type.params
                             :body (type-desugar type.body)))
    :measure (type-count type))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define type-list-desugar ((types type-listp))
    :returns (core-types type-listp)
    :parents (abstract-syntax-desugaring types-desugar)
    :short "Desugar a list of types."
    (cond ((endp types) nil)
          (t (cons (type-desugar (car types))
                   (type-list-desugar (cdr types)))))
    :measure (type-list-count types))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual types-desugar)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (std::defprojection type-list-desugar (x)
    :parents nil
    (type-desugar x)
    :already-definedp t)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual types-corep-of-types-desugar
    (defret type-corep-of-type-desugar
      (type-corep core-type)
      :fn type-desugar)
    (defret type-list-corep-of-type-list-desugar
      (type-list-corep core-types)
      :fn type-list-desugar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+type-desugar ((var+type var+type-p))
  :returns (core-var+type var+type-p)
  :short "Desugar a variable with type."
  (b* ((var (var+type->var var+type))
       (type (var+type->type var+type)))
    (make-var+type :var var :type (type-desugar type)))

  ///

  (defret var+type-corep-of-var+type-desugar
    (var+type-corep core-var+type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection var+type-list-desugar ((x var+type-listp))
  :returns (core-vars+types var+type-listp)
  :short "Desugar a list of variables with types."
  (var+type-desugar x)

  ///

  (defret var+type-list-corep-of-var+type-list-desugar
    (var+type-list-corep core-vars+types)
    :fn var+type-list-desugar
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
