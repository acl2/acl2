; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax")
(include-book "values-to-abstract-syntax")

(local (include-book "std/lists/len" :dir :system))

(include-book "kestrel/json/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ deserializer
  :parents (abstract-syntax)
  :short "Mapping from JSON values to Remora ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "[impl] serializes its internal ASTs to JSON.
     Here we define the inverse mapping, from "
    (xdoc::seetopic "json::json" "JSON values")
    " to the ASTs defined as "
    (xdoc::seetopic "abstract-syntax-trees" "fixtypes")
    ", so that ASTs produced by [impl] can be recreated in ACL2.")
   (xdoc::p
    "We currently deserialize only "
    (xdoc::seetopic "ast-huncheckedp" "[impl]'s unchecked ASTs")
    ".")
   (xdoc::p
    "TERecord, Struct, and FieldProj ASTs from [impl]
     are not yet supported in ACL2.")
   (xdoc::p
    "Each conversion function is named @('X-fromJSON'),
     where @('X') is the name of the corresponding AST fixtype
     (e.g. @('dim'), @('var+type?'), @('expr')).
     Every @('X-fromJSON') function takes a @(tsee json::valuep)
     and returns @('(mv erp x)'):
     @('erp') is non-@('nil') (an error message) when the JSON value
     does not correspond to a valid AST,
     in which case @('x') is an irrelevant placeholder value of the
     fixtype;
     otherwise @('erp') is @('nil') and @('x') is the resulting AST,
     which is in the "
    (xdoc::seetopic "abstract-syntax-haskell" "subset corresponding to [impl]")
    ". JSON objects are dispatched on their @('\"tag\"') member,
     whose string value names the [impl] AST node being decoded."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; These lemmas establish that the JSON value returned by
;; json::object-member-value has a strictly smaller value-count than the
;; enclosing object.  This is what justifies the measures of the mutually
;; recursive fromJSON functions below, which recur into member values
;; obtained via json::object-member-value (directly, or indirectly via the
;; elements of a member value that is a JSON array).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl value-list-count-of-object-member-values-aux
  (implies (json::member-listp members)
           (<= (json::value-list-count
                (json::object-member-values-aux name members))
               (json::member-list-count members)))
  :hints (("Goal" :induct (json::object-member-values-aux name members)
                  :in-theory (enable json::object-member-values-aux
                                     json::value-list-count
                                     json::member-list-count)))
  :rule-classes :linear)

(defruledl value-list-count-of-object-member-values
  (implies (json::value-case object :object)
           (< (json::value-list-count (json::object-member-values name object))
              (json::value-count object)))
  :hints (("Goal" :in-theory (enable json::object-member-values
                                     json::value-count)
                  :use (:instance value-list-count-of-object-member-values-aux
                                  (members (json::value-object->members object)))))
  :rule-classes :linear)

(defruledl member-list-count-of-member-listp
  (implies (json::member-listp members)
           (<= 1
               (json::member-list-count members)))
  :hints (("Goal" :in-theory (enable json::member-list-count)))
  :rule-classes :linear)

(defruledl value-count-of-value-case-object
  (implies (json::value-case object :object)
           (<= 3
               (json::value-count object)))
  :hints (("Goal" :in-theory (enable json::value-count)
                  :use (:instance member-list-count-of-member-listp
                                  (members (json::value-object->members object)))))
  :rule-classes :linear)

(defruledl value-count-of-object-member-value
  :short "The @(tsee json::value-count) of a named member's value
          is strictly less than the @(tsee json::value-count)
          of the enclosing JSON object."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is local and disabled, since it is an implementation detail
     of this book's measures, not meant to be used elsewhere.  Each
     @(tsee defines) below that recurs into member values obtained via
     @(tsee json::object-member-value) enables this rule locally,
     via @(':hints'), for its own termination proof."))
  (implies (json::value-case object :object)
           (< (json::value-count (json::object-member-value name object))
              (json::value-count object)))
  :hints (("Goal" :in-theory (enable json::object-member-value
                                     json::value-count
                                     json::irr-value)
                  :use ((:instance value-count-of-value-case-object
                                   (object object))
                        (:instance value-list-count-of-object-member-values
                                   (name name)
                                   (object object)))))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Dim
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines dim-fromJSON

    (define dim-fromJSON ((j json::valuep))
      :returns (mv erp (x dimp))
      :measure (json::value-count j)
      :short "Convert a JSON value encoding a @('Dim') to a @(tsee dim)."
      (b* (((acl2::reterr)
            (make-dim-const :val 0)))
        (if (json::value-case j :object)
            (b* ((tag-j
                  (json::object-member-value "tag" j)))
              (if (json::value-case tag-j :string)
                  (b* ((tag
                        (json::value-string->get tag-j)))
                    (cond
                      ((equal tag "DimVar")
                       (b* ((name-j
                             (json::object-member-value "name" j)))
                         (if (json::value-case name-j :string)
                             (b* ((name
                                   (json::value-string->get name-j)))
                               (acl2::retok (make-dim-var :name name)))
                           (acl2::reterr (msg "The \"name\" member of a DimVar object must be a string, but ~x0 is not." name-j)))))
                      ((equal tag "DimN")
                       (b* ((val-j
                             (json::object-member-value "val" j)))
                         (if (json::value-case val-j :number)
                             (b* ((val
                                   (json::value-number->get val-j)))
                               (if (natp val)
                                   (acl2::retok (make-dim-const :val val))
                                 (acl2::reterr (msg "The \"val\" member of a DimN object must be a natural, but ~x0 is not." val))))
                           (acl2::reterr (msg "The \"val\" member of a DimN object must be a number, but ~x0 is not." val-j)))))
                      ((equal tag "Add")
                       (b* ((dims-j
                             (json::object-member-value "dims" j)))
                         (if (json::value-case dims-j :array)
                             (b* ((dims-js
                                   (json::value-array->elements dims-j))
                                  ((acl2::erp dims)
                                   (dim-list-fromJSON dims-js)))
                               (acl2::retok (make-dim-add :dims dims)))
                           (acl2::reterr (msg "The \"dims\" member of an Add object must be a JSON array, but ~x0 is not." dims-j)))))
                      ((equal tag "Mul")
                       (b* ((dims-j
                             (json::object-member-value "dims" j)))
                         (if (json::value-case dims-j :array)
                             (b* ((dims-js
                                   (json::value-array->elements dims-j))
                                  ((acl2::erp dims)
                                   (dim-list-fromJSON dims-js)))
                               (acl2::retok (make-dim-mul :dims dims)))
                           (acl2::reterr (msg "The \"dims\" member of a Mul object must be a JSON array, but ~x0 is not." dims-j)))))
                      ((equal tag "Sub")
                       (b* ((dims-j
                             (json::object-member-value "dims" j)))
                         (if (json::value-case dims-j :array)
                             (b* ((dims-js
                                   (json::value-array->elements dims-j))
                                  ((acl2::erp dims)
                                   (dim-list-fromJSON dims-js)))
                               (acl2::retok (make-dim-sub :dims dims)))
                           (acl2::reterr (msg "The \"dims\" member of a Sub object must be a JSON array, but ~x0 is not." dims-j)))))
                      (t
                       (acl2::reterr (msg "~x0 is not a recognized tag for a Dim." tag)))))
                (acl2::reterr (msg "The \"tag\" member of a Dim object must be a string, but ~x0 is not." tag-j))))
          (acl2::reterr (msg "A JSON value representing a Dim must be a JSON object, but ~x0 is not." j)))))

  (define dim-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x dim-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to a @(tsee dim-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (dim-fromJSON (car js)))
               ((acl2::erp tl)
                (dim-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  :verify-guards nil
  :hints (("Goal" :in-theory (enable value-count-of-object-member-value)))
  ///
  (verify-guards dim-fromJSON))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Shape
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines shape-fromJSON

  (define shape-fromJSON ((j json::valuep))
    :returns (mv erp (x shapep))
    :measure (json::value-count j)
    :short "Convert a JSON value encoding a @('Shape') to a @(tsee shape)."
    (b* (((acl2::reterr)
          (make-shape-dims :dims nil)))
      (if (json::value-case j :object)
          (b* ((tag-j
                (json::object-member-value "tag" j)))
            (if (json::value-case tag-j :string)
                (b* ((tag
                      (json::value-string->get tag-j)))
                  (cond
                    ((equal tag "ShapeVar")
                     (b* ((name-j
                           (json::object-member-value "name" j)))
                       (if (json::value-case name-j :string)
                           (b* ((name
                                 (json::value-string->get name-j)))
                             (acl2::retok (make-shape-var :name name)))
                         (acl2::reterr (msg "The \"name\" member of a ShapeVar object must be a string, but ~x0 is not." name-j)))))
                    ((equal tag "ShapeDim")
                     (b* ((dim-j
                           (json::object-member-value "dim" j))
                          ((acl2::erp dim)
                           (dim-fromJSON dim-j)))
                       (acl2::retok (make-shape-dims :dims (list dim)))))
                    ((equal tag "Concat")
                     (b* ((shapes-j
                           (json::object-member-value "shapes" j)))
                       (if (json::value-case shapes-j :array)
                           (b* ((shapes-js
                                 (json::value-array->elements shapes-j))
                                ((acl2::erp shapes)
                                 (shape-list-fromJSON shapes-js)))
                             (acl2::retok (make-shape-append :shapes shapes)))
                         (acl2::reterr (msg "The \"shapes\" member of a Concat object must be a JSON array, but ~x0 is not." shapes-j)))))
                    (t
                     (acl2::reterr (msg "~x0 is not a recognized tag for a Shape." tag)))))
              (acl2::reterr (msg "The \"tag\" member of a Shape object must be a string, but ~x0 is not." tag-j))))
        (acl2::reterr (msg "A JSON value representing a Shape must be a JSON object, but ~x0 is not." j)))))

  (define shape-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x shape-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to a @(tsee shape-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (shape-fromJSON (car js)))
               ((acl2::erp tl)
                (shape-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  :verify-guards nil
  :hints (("Goal" :in-theory (enable value-count-of-object-member-value)))
  ///
  (verify-guards shape-fromJSON)

  (defret-mutual ast-huncheckedp-of-shape-fromJSON
    (defret shape-huncheckedp-of-shape-fromJSON
        (implies (not erp)
                 (shape-huncheckedp x))
      :fn shape-fromJSON)
    (defret shape-list-huncheckedp-of-shape-list-fromJSON
        (implies (not erp)
                 (shape-list-huncheckedp x))
      :fn shape-list-fromJSON)
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ISpace
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-fromJSON ((j json::valuep))
  :returns (mv erp (x ispacep))
  :short "Convert a JSON value encoding an @('ISpace') to a @(tsee ispace)."
  (b* (((acl2::reterr)
        (make-ispace-dim :dim (make-dim-const :val 0))))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "Dim")
                   (b* ((dim-j
                         (json::object-member-value "dim" j))
                        ((acl2::erp dim)
                         (dim-fromJSON dim-j)))
                     (acl2::retok (make-ispace-dim :dim dim))))
                  ((equal tag "Shape")
                   (b* ((shape-j
                         (json::object-member-value "shape" j))
                        ((acl2::erp shape)
                         (shape-fromJSON shape-j)))
                     (acl2::retok (make-ispace-shape :shape shape))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for an ISpace." tag)))))
            (acl2::reterr (msg "The \"tag\" member of an ISpace object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing an ISpace must be a JSON object, but ~x0 is not." j))))

  ///

  (defret ispace-huncheckedp-of-ispace-fromJSON
      (implies (not erp)
               (ispace-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

(define ispace-list-fromJSON ((js json::value-listp))
  :returns (mv erp (x ispace-listp))
  :measure (json::value-list-count js)
  :short "Convert a JSON array's elements to an @(tsee ispace-listp)."
  (b* (((acl2::reterr) nil))
    (if (consp js)
        (b* (((acl2::erp hd)
              (ispace-fromJSON (car js)))
             ((acl2::erp tl)
              (ispace-list-fromJSON (cdr js))))
          (acl2::retok (cons hd tl)))
      (acl2::retok nil)))

  ///

  (defret ispace-list-huncheckedp-of-ispace-list-fromJSON
      (implies (not erp)
               (ispace-list-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ISpaceParam
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-fromJSON ((j json::valuep))
  :returns (mv erp (x ispace-varp))
  :short "Convert a JSON value encoding an @('ISpaceParam')
          to an @(tsee ispace-var)."
  (b* (((acl2::reterr)
        (make-ispace-var-dim :name "")))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "DimParam")
                   (b* ((name-j
                         (json::object-member-value "name" j)))
                     (if (json::value-case name-j :string)
                         (b* ((name
                               (json::value-string->get name-j)))
                           (acl2::retok (make-ispace-var-dim :name name)))
                       (acl2::reterr (msg "The \"name\" member of a DimParam object must be a string, but ~x0 is not." name-j)))))
                  ((equal tag "ShapeParam")
                   (b* ((name-j
                         (json::object-member-value "name" j)))
                     (if (json::value-case name-j :string)
                         (b* ((name
                               (json::value-string->get name-j)))
                           (acl2::retok (make-ispace-var-shape :name name)))
                       (acl2::reterr (msg "The \"name\" member of a ShapeParam object must be a string, but ~x0 is not." name-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for an ISpaceParam." tag)))))
            (acl2::reterr (msg "The \"tag\" member of an ISpaceParam object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing an ISpaceParam must be a JSON object, but ~x0 is not." j)))))

(define ispace-var-list-fromJSON ((js json::value-listp))
  :returns (mv erp (x ispace-var-listp))
  :measure (json::value-list-count js)
  :short "Convert a JSON array's elements to an @(tsee ispace-var-listp)."
  (b* (((acl2::reterr) nil))
    (if (consp js)
        (b* (((acl2::erp hd)
              (ispace-var-fromJSON (car js)))
             ((acl2::erp tl)
              (ispace-var-list-fromJSON (cdr js))))
          (acl2::retok (cons hd tl)))
      (acl2::retok nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; TypeParamExp
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var-fromJSON ((j json::valuep))
  :returns (mv erp (x type-varp))
  :short "Convert a JSON value encoding a @('TypeParamExp')
          to a @(tsee type-var)."
  (b* (((acl2::reterr)
        (make-type-var-atom :name "")))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "TEAtomTypeParam")
                   (b* ((name-j
                         (json::object-member-value "name" j)))
                     (if (json::value-case name-j :string)
                         (b* ((name
                               (json::value-string->get name-j)))
                           (acl2::retok (make-type-var-atom :name name)))
                       (acl2::reterr (msg "The \"name\" member of a TEAtomTypeParam object must be a string, but ~x0 is not." name-j)))))
                  ((equal tag "TEArrayTypeParam")
                   (b* ((name-j
                         (json::object-member-value "name" j)))
                     (if (json::value-case name-j :string)
                         (b* ((name
                               (json::value-string->get name-j)))
                           (acl2::retok (make-type-var-array :name name)))
                       (acl2::reterr (msg "The \"name\" member of a TEArrayTypeParam object must be a string, but ~x0 is not." name-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for a TypeParamExp." tag)))))
            (acl2::reterr (msg "The \"tag\" member of a TypeParamExp object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing a TypeParamExp must be a JSON object, but ~x0 is not." j)))))

(define type-var-list-fromJSON ((js json::value-listp))
  :returns (mv erp (x type-var-listp))
  :measure (json::value-list-count js)
  :short "Convert a JSON array's elements to a @(tsee type-var-listp)."
  (b* (((acl2::reterr) nil))
    (if (consp js)
        (b* (((acl2::erp hd)
              (type-var-fromJSON (car js)))
             ((acl2::erp tl)
              (type-var-list-fromJSON (cdr js))))
          (acl2::retok (cons hd tl)))
      (acl2::retok nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; TypeExp
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines type-fromJSON

  (define type-fromJSON ((j json::valuep))
    :returns (mv erp (x typep))
    :measure (json::value-count j)
    :short "Convert a JSON value encoding a @('TypeExp') to a @(tsee type)."
    (b* (((acl2::reterr)
          (make-type-base :type (make-base-type-bool ))))
      (if (json::value-case j :object)
          (b* ((tag-j
                (json::object-member-value "tag" j)))
            (if (json::value-case tag-j :string)
                (b* ((tag
                      (json::value-string->get tag-j)))
                  (cond
                    ((equal tag "TEAtomVar")
                     (b* ((name-j
                           (json::object-member-value "name" j)))
                       (if (json::value-case name-j :string)
                           (b* ((name
                                 (json::value-string->get name-j)))
                             (acl2::retok (make-type-var
                                           :var (make-type-var-atom :name name))))
                         (acl2::reterr (msg "The \"name\" member of a TEAtomVar object must be a string, but ~x0 is not." name-j)))))
                    ((equal tag "TEArrayVar")
                     (b* ((name-j
                           (json::object-member-value "name" j)))
                       (if (json::value-case name-j :string)
                           (b* ((name
                                 (json::value-string->get name-j)))
                             (acl2::retok (make-type-var
                                           :var (make-type-var-array :name name))))
                         (acl2::reterr (msg "The \"name\" member of a TEArrayVar object must be a string, but ~x0 is not." name-j)))))
                    ((equal tag "TEBool")
                     (acl2::retok (make-type-base
                                   :type (make-base-type-bool ))))
                    ((equal tag "TEInt")
                     (acl2::retok (make-type-base
                                   :type (make-base-type-int ))))
                    ((equal tag "TEFloat")
                     (acl2::retok (make-type-base
                                   :type (make-base-type-float ))))
                    ((equal tag "TEArray")
                     (b* ((elem-j
                           (json::object-member-value "elem" j))
                          ((acl2::erp elem)
                           (type-fromJSON elem-j))
                          (shape-j
                           (json::object-member-value "shape" j))
                          ((acl2::erp shape)
                           (shape-fromJSON shape-j)))
                       (acl2::retok (make-type-array
                                     :elem elem
                                     :ispace (make-ispace-shape :shape shape)))))
                    ((equal tag "TEArrow")
                     (b* ((in-j
                           (json::object-member-value "in" j))
                          ((acl2::erp in)
                           (type-fromJSON in-j))
                          (out-j
                           (json::object-member-value "out" j))
                          ((acl2::erp out)
                           (type-fromJSON out-j)))
                       (acl2::retok (make-type-fun
                                     :in in
                                     :out out))))
                    ((equal tag "TEForall")
                     (b* ((params-j
                           (json::object-member-value "params" j))
                          (body-j
                           (json::object-member-value "body" j)))
                       (if (json::value-case params-j :array)
                           (b* ((params-js
                                 (json::value-array->elements params-j))
                                ((acl2::erp params)
                                 (type-var-list-fromJSON params-js))
                                ((acl2::erp body)
                                 (type-fromJSON body-j)))
                             (if (consp params)
                                 (acl2::retok
                                  (make-type-forall/foralln params body))
                               (acl2::reterr (msg "The \"params\" member of a TEForall object must be a nonempty list, but ~x0 is not." params))))
                         (acl2::reterr (msg "The \"params\" member of a TEForall object must be a JSON array, but ~x0 is not." params-j)))))
                    ((equal tag "TEPi")
                     (b* ((params-j
                           (json::object-member-value "params" j))
                          (body-j
                           (json::object-member-value "body" j)))
                       (if (json::value-case params-j :array)
                           (b* ((params-js
                                 (json::value-array->elements params-j))
                                ((acl2::erp params)
                                 (ispace-var-list-fromJSON params-js))
                                ((acl2::erp body)
                                 (type-fromJSON body-j)))
                             (if (consp params)
                                 (acl2::retok (make-type-pi/pin params body))
                               (acl2::reterr (msg "The \"params\" member of a TEPi object must be a nonempty list, but ~x0 is not." params))))
                         (acl2::reterr (msg "The \"params\" member of a TEPi object must be a JSON array, but ~x0 is not." params-j)))))
                    ((equal tag "TESigma")
                     (b* ((params-j
                           (json::object-member-value "params" j))
                          (body-j
                           (json::object-member-value "body" j)))
                       (if (json::value-case params-j :array)
                           (b* ((params-js
                                 (json::value-array->elements params-j))
                                ((acl2::erp params)
                                 (ispace-var-list-fromJSON params-js))
                                ((acl2::erp body)
                                 (type-fromJSON body-j)))
                             (if (consp params)
                                 (acl2::retok
                                  (make-type-sigma/sigman params body))
                               (acl2::reterr (msg "The \"params\" member of a TESigma object must be a nonempty list, but ~x0 is not." params))))
                         (acl2::reterr (msg "The \"params\" member of a TESigma object must be a JSON array, but ~x0 is not." params-j)))))
                    ((equal tag "TERecord")
                     (acl2::reterr (msg "TERecord objects are not yet supported")))
                    (t
                     (acl2::reterr (msg "~x0 is not a recognized tag for a TypeExp." tag)))))
              (acl2::reterr (msg "The \"tag\" member of a TypeExp object must be a string, but ~x0 is not." tag-j))))
        (acl2::reterr (msg "A JSON value representing a TypeExp must be a JSON object, but ~x0 is not." j)))))

  (define type-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x type-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to a @(tsee type-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (type-fromJSON (car js)))
               ((acl2::erp tl)
                (type-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  :verify-guards nil
  :hints (("Goal" :in-theory (enable value-count-of-object-member-value)))

  ///

  ;; These lemmas are needed to discharge the guard of endp
  ;; in the TEForall, TEPi, and TESigma cases of type-fromJSON above,
  ;; where we check the length of the params list to decide between the
  ;; unary and n-ary forms.
  (defruledl not-cdr-when-not-consp-cdr-and-type-var-listp
      (implies (and (type-var-listp x)
                    (not (consp (cdr x))))
               (not (cdr x)))
    :enable type-var-listp)
  (defruledl not-cdr-when-not-consp-cdr-and-ispace-var-listp
      (implies (and (ispace-var-listp x)
                    (not (consp (cdr x))))
               (not (cdr x)))
    :enable ispace-var-listp)

  ///

  (verify-guards type-fromJSON
      :hints (("Goal" :in-theory (enable not-cdr-when-not-consp-cdr-and-type-var-listp
                                         not-cdr-when-not-consp-cdr-and-ispace-var-listp))))

  (defret-mutual ast-huncheckedp-of-type-fromJSON
    (defret type-huncheckedp-of-type-fromJSON
        (implies (not erp)
                 (type-huncheckedp x))
      :fn type-fromJSON)
    (defret type-list-huncheckedp-of-type-list-fromJSON
        (implies (not erp)
                 (type-list-huncheckedp x))
      :fn type-list-fromJSON)
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules
                                        make-type-forall/foralln
                                        make-type-pi/pin
                                        make-type-sigma/sigman)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Base
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base-lit-fromJSON ((j json::valuep))
  :returns (mv erp (x base-litp))
  :short "Convert a JSON value encoding a @('Base') literal
          to a @(tsee base-lit)."
  (b* (((acl2::reterr)
        (make-base-lit-bool :lit nil)))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "BoolVal")
                   (b* ((lit-j
                         (json::object-member-value "lit" j)))
                     (cond ((json::value-case lit-j :true)
                            (acl2::retok (make-base-lit-bool :lit t)))
                           ((json::value-case lit-j :false)
                            (acl2::retok (make-base-lit-bool :lit nil)))
                           (t
                            (acl2::reterr (msg "The \"lit\" member of a BoolVal object must be a JSON boolean, but ~x0 is not." lit-j))))))
                  ((equal tag "IntVal")
                   (b* ((lit-j
                         (json::object-member-value "lit" j)))
                     (if (json::value-case lit-j :number)
                         (b* ((lit
                               (json::value-number->get lit-j)))
                           (if (integerp lit)
                               (b* ((ilit
                                     (int-to-int-lit lit)))
                                 (acl2::retok (make-base-lit-int :lit ilit)))
                             (acl2::reterr (msg "The \"lit\" member of an IntVal object must be an integer, but ~x0 is not." lit))))
                       (acl2::reterr (msg "The \"lit\" member of an IntVal object must be a number, but ~x0 is not." lit-j)))))
                  ((equal tag "FloatVal")
                   (b* ((lit-j
                         (json::object-member-value "lit" j)))
                     (if (json::value-case lit-j :number)
                         (b* ((lit
                               (json::value-number->get lit-j))
                              ((mv err flit)
                               (rational-to-float-lit lit))
                              ((when err)
                               (acl2::reterr (msg "The number ~x0 cannot be represented as a Remora float literal." lit))))
                           (acl2::retok (make-base-lit-float :lit flit)))
                       (acl2::reterr (msg "The \"lit\" member of a FloatVal object must be a number, but ~x0 is not." lit-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for a Base." tag)))))
            (acl2::reterr (msg "The \"tag\" member of a Base object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing a Base must be a JSON object, but ~x0 is not." j)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; PatBase
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var+type?-fromJSON ((j json::valuep))
  :returns (mv erp (x var+type?-p))
  :short "Convert a JSON value encoding a @('PatBase')
          to a @(tsee var+type?)."
  (b* (((acl2::reterr)
        (make-var+type? :var "" :type? (make-type-option-none ))))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "PatId")
                   (b* ((var-j
                         (json::object-member-value "var" j))
                        (type-j
                         (json::object-member-value "type" j)))
                     (if (json::value-case var-j :string)
                         (b* ((var
                               (json::value-string->get var-j))
                              ((acl2::erp type)
                               (type-fromJSON type-j)))
                           (acl2::retok (make-var+type?
                                         :var var
                                         :type? (make-type-option-some :val type))))
                       (acl2::reterr (msg "The \"var\" member of a PatId object must be a string, but ~x0 is not." var-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for a PatBase." tag)))))
            (acl2::reterr (msg "The \"tag\" member of a PatBase object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing a PatBase must be a JSON object, but ~x0 is not." j))))

  ///

  (defret var+type?-huncheckedp-of-var+type?-fromJSON
      (implies (not erp)
               (var+type?-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

(define var+type?-list-fromJSON ((js json::value-listp))
  :returns (mv erp (x var+type?-listp))
  :measure (json::value-list-count js)
  :short "Convert a JSON array's elements to a @(tsee var+type?-listp)."
  (b* (((acl2::reterr) nil))
    (if (consp js)
        (b* (((acl2::erp hd)
              (var+type?-fromJSON (car js)))
             ((acl2::erp tl)
              (var+type?-list-fromJSON (cdr js))))
          (acl2::retok (cons hd tl)))
      (acl2::retok nil)))

  ///

  (defret var+type?-list-huncheckedp-of-var+type?-list-fromJSON
      (implies (not erp)
               (var+type?-list-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; AtomBase, BindBase, and ExpBase are mutually recursive,
;; so their fromJSON counterparts (together with their list forms and the
;; [Int]-to-nat-listp helper nat-list-fromJSON) are defined as a single
;; mutually recursive clique below.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-fromJSON

  (define atom-fromJSON ((j json::valuep))
    :returns (mv erp (x atomp))
    :measure (json::value-count j)
    :short "Convert a JSON value encoding an @('AtomBase') to a @(tsee atom)."
    (b* (((acl2::reterr)
          (make-atom-base :lit (make-base-lit-bool :lit nil))))
      (if (json::value-case j :object)
          (b* ((tag-j
                (json::object-member-value "tag" j)))
            (if (json::value-case tag-j :string)
                (b* ((tag
                      (json::value-string->get tag-j)))
                  (cond
                    ((equal tag "Base")
                     (b* ((lit-j
                           (json::object-member-value "lit" j))
                          ((acl2::erp lit)
                           (base-lit-fromJSON lit-j)))
                       (acl2::retok (make-atom-base :lit lit))))
                    ((equal tag "Lambda")
                     (b* ((param-j
                           (json::object-member-value "param" j))
                          ((acl2::erp param)
                           (var+type?-fromJSON param-j))
                          (body-j
                           (json::object-member-value "body" j))
                          ((acl2::erp body)
                           (expr-fromJSON body-j)))
                       (acl2::retok (make-atom-lambda
                                     :param param
                                     :body body
                                     :type? (make-type-option-none )))))
                    ((equal tag "TLambda")
                     (b* ((param-j
                           (json::object-member-value "param" j))
                          ((acl2::erp param)
                           (type-var-fromJSON param-j))
                          (body-j
                           (json::object-member-value "body" j))
                          ((acl2::erp body)
                           (expr-fromJSON body-j)))
                       (acl2::retok (make-atom-tlambda
                                     :param param
                                     :body body))))
                    ((equal tag "ILambda")
                     (b* ((param-j
                           (json::object-member-value "param" j))
                          ((acl2::erp param)
                           (ispace-var-fromJSON param-j))
                          (body-j
                           (json::object-member-value "body" j))
                          ((acl2::erp body)
                           (expr-fromJSON body-j)))
                       (acl2::retok (make-atom-ilambda
                                     :param param
                                     :body body))))
                    ((equal tag "Box")
                     (b* ((ispace-j
                           (json::object-member-value "ispace" j))
                          ((acl2::erp ispace)
                           (ispace-fromJSON ispace-j))
                          (array-j
                           (json::object-member-value "array" j))
                          ((acl2::erp array)
                            (expr-fromJSON array-j))
                          (type-j
                           (json::object-member-value "type" j)))
                       (if (json::value-case type-j :null)
                           (acl2::retok (make-atom-box
                                         :ispace ispace
                                         :array array
                                         :type? (make-type-option-none )))
                         (b* (((acl2::erp type)
                               (type-fromJSON type-j)))
                           (acl2::retok (make-atom-box
                                         :ispace ispace
                                         :array array
                                         :type? (make-type-option-some
                                                 :val type)))))))
                    (t
                     (acl2::reterr (msg "~x0 is not a recognized tag for an AtomBase." tag)))))
              (acl2::reterr (msg "The \"tag\" member of an AtomBase object must be a string, but ~x0 is not." tag-j))))
        (acl2::reterr (msg "A JSON value representing an AtomBase must be a JSON object, but ~x0 is not." j)))))

  (define atom-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x atom-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to an @(tsee atom-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (atom-fromJSON (car js)))
               ((acl2::erp tl)
                (atom-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  (define bind-fromJSON ((j json::valuep))
    :returns (mv erp (x bindp))
    :measure (json::value-count j)
    :short "Convert a JSON value encoding a @('BindBase') to a @(tsee bind)."
    (b* (((acl2::reterr)
          (make-bind-val :var "" :type? (make-type-option-none )
                         :expr (make-expr-var :name ""))))
      (if (json::value-case j :object)
          (b* ((tag-j
                (json::object-member-value "tag" j)))
            (if (json::value-case tag-j :string)
                (b* ((tag
                      (json::value-string->get tag-j)))
                  (cond
                    ((equal tag "BindVal")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          (type-j
                           (json::object-member-value "type" j))
                          (expr-j
                           (json::object-member-value "expr" j)))
                       (if (json::value-case var-j :string)
                           (b* ((var
                                 (json::value-string->get var-j))
                                ((acl2::erp expr)
                                 (expr-fromJSON expr-j)))
                             (if (json::value-case type-j :null)
                                 (acl2::retok (make-bind-val
                                               :var var
                                               :type? (make-type-option-none )
                                               :expr expr))
                               (b* (((acl2::erp type)
                                     (type-fromJSON type-j)))
                                 (acl2::retok (make-bind-val
                                               :var var
                                               :type? (make-type-option-some
                                                       :val type)
                                               :expr expr)))))
                         (acl2::reterr (msg "The \"var\" member of a BindVal object must be a string, but ~x0 is not." var-j)))))
                    ((equal tag "BindType")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          ((acl2::erp var)
                           (type-var-fromJSON var-j))
                          (type-j
                           (json::object-member-value "type" j))
                          ((acl2::erp type)
                           (type-fromJSON type-j)))
                       (acl2::retok (make-bind-type :var var :type type))))
                    ((equal tag "BindISpace")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          ((acl2::erp var)
                           (ispace-var-fromJSON var-j))
                          (ispace-j
                           (json::object-member-value "ispace" j))
                          ((acl2::erp ispace)
                           (ispace-fromJSON ispace-j)))
                       (acl2::retok (make-bind-ispace :var var :ispace ispace))))
                    ((equal tag "BindFun")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          (params-j
                           (json::object-member-value "params" j))
                          (type-j
                           (json::object-member-value "type" j))
                          (expr-j
                           (json::object-member-value "expr" j)))
                       (if (json::value-case var-j :string)
                           (if (json::value-case params-j :array)
                               (b* ((var
                                     (json::value-string->get var-j))
                                    (params-js
                                     (json::value-array->elements params-j))
                                    ((acl2::erp params)
                                     (var+type?-list-fromJSON params-js))
                                    ((acl2::erp expr)
                                     (expr-fromJSON expr-j)))
                                 (if (consp params)
                                     (if (json::value-case type-j :null)
                                         (acl2::retok (make-bind-fun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-none )
                                                       :expr expr))
                                       (b* (((acl2::erp type)
                                             (type-fromJSON type-j)))
                                         (acl2::retok (make-bind-fun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-some
                                                               :val type)
                                                       :expr expr))))
                                   (acl2::reterr (msg "The \"params\" member of a BindFun object must be a nonempty list, but ~x0 is not." params))))
                             (acl2::reterr (msg "The \"params\" member of a BindFun object must be a JSON array, but ~x0 is not." params-j)))
                         (acl2::reterr (msg "The \"var\" member of a BindFun object must be a string, but ~x0 is not." var-j)))))
                    ((equal tag "BindTFun")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          (params-j
                           (json::object-member-value "params" j))
                          (type-j
                           (json::object-member-value "type" j))
                          (expr-j
                           (json::object-member-value "expr" j)))
                       (if (json::value-case var-j :string)
                           (if (json::value-case params-j :array)
                               (b* ((var
                                     (json::value-string->get var-j))
                                    (params-js
                                     (json::value-array->elements params-j))
                                    ((acl2::erp params)
                                     (type-var-list-fromJSON params-js))
                                    ((acl2::erp expr)
                                     (expr-fromJSON expr-j)))
                                 (if (consp params)
                                     (if (json::value-case type-j :null)
                                         (acl2::retok (make-bind-tfun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-none )
                                                       :expr expr))
                                       (b* (((acl2::erp type)
                                             (type-fromJSON type-j)))
                                         (acl2::retok (make-bind-tfun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-some
                                                               :val type)
                                                       :expr expr))))
                                   (acl2::reterr (msg "The \"params\" member of a BindTFun object must be a nonempty list, but ~x0 is not." params))))
                             (acl2::reterr (msg "The \"params\" member of a BindTFun object must be a JSON array, but ~x0 is not." params-j)))
                         (acl2::reterr (msg "The \"var\" member of a BindTFun object must be a string, but ~x0 is not." var-j)))))
                    ((equal tag "BindIFun")
                     (b* ((var-j
                           (json::object-member-value "var" j))
                          (params-j
                           (json::object-member-value "params" j))
                          (type-j
                           (json::object-member-value "type" j))
                          (expr-j
                           (json::object-member-value "expr" j)))
                       (if (json::value-case var-j :string)
                           (if (json::value-case params-j :array)
                               (b* ((var
                                     (json::value-string->get var-j))
                                    (params-js
                                     (json::value-array->elements params-j))
                                    ((acl2::erp params)
                                     (ispace-var-list-fromJSON params-js))
                                    ((acl2::erp expr)
                                     (expr-fromJSON expr-j)))
                                 (if (consp params)
                                     (if (json::value-case type-j :null)
                                         (acl2::retok (make-bind-ifun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-none )
                                                       :expr expr))
                                       (b* (((acl2::erp type)
                                             (type-fromJSON type-j)))
                                         (acl2::retok (make-bind-ifun
                                                       :var var
                                                       :params params
                                                       :type? (make-type-option-some
                                                               :val type)
                                                       :expr expr))))
                                   (acl2::reterr (msg "The \"params\" member of a BindIFun object must be a nonempty list, but ~x0 is not." params))))
                             (acl2::reterr (msg "The \"params\" member of a BindIFun object must be a JSON array, but ~x0 is not." params-j)))
                         (acl2::reterr (msg "The \"var\" member of a BindIFun object must be a string, but ~x0 is not." var-j)))))
                    (t
                     (acl2::reterr (msg "~x0 is not a recognized tag for a BindBase." tag)))))
              (acl2::reterr (msg "The \"tag\" member of a BindBase object must be a string, but ~x0 is not." tag-j))))
        (acl2::reterr (msg "A JSON value representing a BindBase must be a JSON object, but ~x0 is not." j)))))

  (define bind-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x bind-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to a @(tsee bind-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (bind-fromJSON (car js)))
               ((acl2::erp tl)
                (bind-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  (define expr-fromJSON ((j json::valuep))
    :returns (mv erp (x exprp))
    :measure (json::value-count j)
    :short "Convert a JSON value encoding an @('ExpBase') to a @(tsee expr)."
    (b* (((acl2::reterr)
          (make-expr-var :name "")))
      (if (json::value-case j :object)
          (b* ((tag-j
                (json::object-member-value "tag" j)))
            (if (json::value-case tag-j :string)
                (b* ((tag
                      (json::value-string->get tag-j)))
                  (cond
                    ((equal tag "Var")
                     (b* ((name-j
                           (json::object-member-value "name" j)))
                       (if (json::value-case name-j :string)
                           (b* ((name
                                 (json::value-string->get name-j)))
                             (acl2::retok (make-expr-var :name name)))
                         (acl2::reterr (msg "The \"name\" member of a Var object must be a string, but ~x0 is not." name-j)))))
                    ((equal tag "Array")
                     (b* ((dims-j
                           (json::object-member-value "dims" j))
                          (atoms-j
                           (json::object-member-value "atoms" j)))
                       (if (json::value-case dims-j :array)
                           (if (json::value-case atoms-j :array)
                               (b* ((dims-js
                                     (json::value-array->elements dims-j))
                                    ((acl2::erp dims)
                                     (nat-list-fromJSON dims-js))
                                    (atoms-js
                                     (json::value-array->elements atoms-j))
                                    ((acl2::erp atoms)
                                     (atom-list-fromJSON atoms-js)))
                                 (if (consp atoms)
                                     (acl2::retok (make-expr-array
                                                   :dims dims
                                                   :atoms atoms))
                                   (acl2::reterr (msg "The \"atoms\" member of an Array object must be a nonempty list, but ~x0 is not." atoms))))
                             (acl2::reterr (msg "The \"atoms\" member of an Array object must be a JSON array, but ~x0 is not." atoms-j)))
                         (acl2::reterr (msg "The \"dims\" member of an Array object must be a JSON array, but ~x0 is not." dims-j)))))
                    ((equal tag "EmptyArray")
                     (b* ((dims-j
                           (json::object-member-value "dims" j))
                          (type-j
                           (json::object-member-value "type" j)))
                       (if (json::value-case dims-j :array)
                           (b* ((dims-js
                                 (json::value-array->elements dims-j))
                                ((acl2::erp dims)
                                 (nat-list-fromJSON dims-js))
                                ((acl2::erp type)
                                 (type-fromJSON type-j)))
                             (acl2::retok (make-expr-array-empty
                                               :dims dims
                                               :type type)))
                         (acl2::reterr (msg "The \"dims\" member of an EmptyArray object must be a JSON array, but ~x0 is not." dims-j)))))
                    ((equal tag "Frame")
                     (b* ((dims-j
                           (json::object-member-value "dims" j))
                          (exprs-j
                           (json::object-member-value "exprs" j)))
                       (if (json::value-case dims-j :array)
                           (if (json::value-case exprs-j :array)
                               (b* ((dims-js
                                     (json::value-array->elements dims-j))
                                    ((acl2::erp dims)
                                     (nat-list-fromJSON dims-js))
                                    (exprs-js
                                     (json::value-array->elements exprs-j))
                                    ((acl2::erp exprs)
                                     (expr-list-fromJSON exprs-js)))
                                 (if (consp exprs)
                                     (acl2::retok (make-expr-frame
                                                   :dims dims
                                                   :exprs exprs))
                                   (acl2::reterr (msg "The \"exprs\" member of an Frame object must be a nomempty list, but ~x0 is not." exprs))))
                             (acl2::reterr (msg "The \"exprs\" member of a Frame object must be a JSON array, but ~x0 is not." exprs-j)))
                         (acl2::reterr (msg "The \"dims\" member of a Frame object must be a JSON array, but ~x0 is not." dims-j)))))
                    ((equal tag "EmptyFrame")
                     (b* ((dims-j
                           (json::object-member-value "dims" j))
                          (type-j
                           (json::object-member-value "type" j)))
                       (if (json::value-case dims-j :array)
                           (b* ((dims-js
                                 (json::value-array->elements dims-j))
                                ((acl2::erp dims)
                                 (nat-list-fromJSON dims-js))
                                ((acl2::erp type)
                                 (type-fromJSON type-j)))
                             (acl2::retok (make-expr-frame-empty
                                               :dims dims
                                               :type type)))
                         (acl2::reterr (msg "The \"dims\" member of an EmptyFrame object must be a JSON array, but ~x0 is not." dims-j)))))
                    ((equal tag "App")
                     (b* ((fun-j
                           (json::object-member-value "fun" j))
                          ((acl2::erp fun)
                           (expr-fromJSON fun-j))
                          (arg-j
                           (json::object-member-value "arg" j))
                          ((acl2::erp arg)
                           (expr-fromJSON arg-j)))
                       (acl2::retok (make-expr-app
                                     :fun fun
                                     :arg arg))))
                    ((equal tag "TApp")
                     (b* ((fun-j
                           (json::object-member-value "fun" j))
                          ((acl2::erp fun)
                           (expr-fromJSON fun-j))
                          (arg-j
                           (json::object-member-value "arg" j))
                          ((acl2::erp arg)
                           (type-fromJSON arg-j)))
                       (acl2::retok (make-expr-tapp
                                     :fun fun
                                     :arg arg))))
                    ((equal tag "IApp")
                     (b* ((fun-j
                           (json::object-member-value "fun" j))
                          ((acl2::erp fun)
                           (expr-fromJSON fun-j))
                          (arg-j
                           (json::object-member-value "arg" j))
                          ((acl2::erp arg)
                           (ispace-fromJSON arg-j)))
                       (acl2::retok (make-expr-iapp
                                     :fun fun
                                     :arg arg))))
                    ((equal tag "Unbox")
                     (b* ((ispace-j
                           (json::object-member-value "ispace" j))
                          (var-j
                           (json::object-member-value "var" j))
                          (target-j
                           (json::object-member-value "target" j))
                          (body-j
                           (json::object-member-value "body" j)))
                       (if (json::value-case var-j :string)
                           (b* (((acl2::erp ispace)
                                 (ispace-var-fromJSON ispace-j))
                                (var
                                 (json::value-string->get var-j))
                                ((acl2::erp target)
                                 (expr-fromJSON target-j))
                                ((acl2::erp body)
                                 (expr-fromJSON body-j)))
                             (acl2::retok (make-expr-unbox
                                           :ispace ispace
                                           :var var
                                           :target target
                                           :body body
                                           :type? (make-type-option-none))))
                         (acl2::reterr (msg "The \"var\" member of an Unbox object must be a string, but ~x0 is not." var-j)))))
                    ((equal tag "Let")
                     (b* ((binds-j
                           (json::object-member-value "binds" j))
                          (body-j
                           (json::object-member-value "body" j)))
                       (if (json::value-case binds-j :array)
                           (b* ((binds-js
                                 (json::value-array->elements binds-j))
                                ((acl2::erp binds)
                                 (bind-list-fromJSON binds-js))
                                ((acl2::erp body)
                                 (expr-fromJSON body-j)))
                             (if (consp binds)
                                 (acl2::retok (make-expr-let
                                               :binds binds
                                               :body body))
                               (acl2::reterr (msg "The \"binds\" member of a Let object must be a nonempty list, but ~x0 is not." binds))))
                         (acl2::reterr (msg "The \"binds\" member of a Let object must be a JSON array, but ~x0 is not." binds-j)))))
                    ((equal tag "Struct")
                     (acl2::reterr (msg "Struct objects are not yet supported")))
                    ((equal tag "FieldProj")
                     (acl2::reterr (msg "FieldProj objects are not yet supported")))
                    (t
                     (acl2::reterr (msg "~x0 is not a recognized tag for an ExpBase." tag)))))
              (acl2::reterr (msg "The \"tag\" member of an ExpBase object must be a string, but ~x0 is not." tag-j))))
        (acl2::reterr (msg "A JSON value representing an ExpBase must be a JSON object, but ~x0 is not." j)))))

  (define expr-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x expr-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array's elements to an @(tsee expr-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (b* (((acl2::erp hd)
                (expr-fromJSON (car js)))
               ((acl2::erp tl)
                (expr-list-fromJSON (cdr js))))
            (acl2::retok (cons hd tl)))
        (acl2::retok nil))))

  (define nat-list-fromJSON ((js json::value-listp))
    :returns (mv erp (x nat-listp))
    :measure (json::value-list-count js)
    :short "Convert a JSON array of @('Int')s to a @(tsee nat-listp)."
    (b* (((acl2::reterr) nil))
      (if (consp js)
          (if (json::value-case (car js) :number)
              (b* ((hd
                    (json::value-number->get (car js))))
                (if (natp hd)
                    (b* (((acl2::erp tl)
                          (nat-list-fromJSON (cdr js))))
                      (acl2::retok (cons hd tl)))
                  (acl2::reterr (msg "Expected a natural, but ~x0 is not." hd))))
            (acl2::reterr (msg "Expected a JSON number, but ~x0 is not." (car js))))
        (acl2::retok nil))))

  :verify-guards nil
  :hints (("Goal" :in-theory (enable value-count-of-object-member-value)))
  ///
  (verify-guards expr-fromJSON)

  (defret-mutual ast-huncheckedp-of-expr-fromJSON
    (defret atom-huncheckedp-of-atom-fromJSON
        (implies (not erp)
                 (atom-huncheckedp x))
      :fn atom-fromJSON)
    (defret atom-list-huncheckedp-of-atom-list-fromJSON
        (implies (not erp)
                 (atom-list-huncheckedp x))
      :fn atom-list-fromJSON)
    (defret bind-huncheckedp-of-bind-fromJSON
      (implies (not erp)
               (bind-huncheckedp x))
      :fn bind-fromJSON)
    (defret bind-list-huncheckedp-of-bind-list-fromJSON
      (implies (not erp)
               (bind-list-huncheckedp x))
      :fn bind-list-fromJSON)
    (defret expr-huncheckedp-of-expr-fromJSON
      (implies (not erp)
               (expr-huncheckedp x))
      :fn expr-fromJSON)
    (defret expr-list-huncheckedp-of-expr-list-fromJSON
      (implies (not erp)
               (expr-list-huncheckedp x))
      :fn expr-list-fromJSON)
    :skip-others t
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; DeclBase
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-fromJSON ((j json::valuep))
  :returns (mv erp (x declp))
  :short "Convert a JSON value encoding a @('DeclBase') to a @(tsee decl)."
  (b* (((acl2::reterr)
        (make-decl-def
         :bind (make-bind-val
                :var ""
                :type? (make-type-option-none )
                :expr (make-expr-var :name "")))))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "Def")
                   (b* ((bind-j
                         (json::object-member-value "bind" j))
                        ((acl2::erp bind)
                         (bind-fromJSON bind-j)))
                     (acl2::retok (make-decl-def :bind bind))))
                  ((equal tag "Entry")
                   (b* ((var-j
                         (json::object-member-value "var" j))
                        (params-j
                         (json::object-member-value "params" j))
                        (type-j
                         (json::object-member-value "type" j))
                        (expr-j
                         (json::object-member-value "expr" j)))
                     (if (json::value-case var-j :string)
                         (if (json::value-case params-j :array)
                             (b* ((var
                                   (json::value-string->get var-j))
                                  (params-js
                                   (json::value-array->elements params-j))
                                  ((acl2::erp params)
                                   (var+type?-list-fromJSON params-js))
                                  ((acl2::erp expr)
                                   (expr-fromJSON expr-j)))
                               (if (json::value-case type-j :null)
                                   (acl2::retok (make-decl-entry
                                                 :var var
                                                 :params params
                                                 :type? (make-type-option-none )
                                                 :expr expr))
                                 (b* (((acl2::erp type)
                                       (type-fromJSON type-j)))
                                   (acl2::retok (make-decl-entry
                                                 :var var
                                                 :params params
                                                 :type? (make-type-option-some
                                                         :val type)
                                                 :expr expr)))))
                           (acl2::reterr (msg "The \"params\" member of an Entry object must be a JSON array, but ~x0 is not." params-j)))
                       (acl2::reterr (msg "The \"var\" member of an Entry object must be a string, but ~x0 is not." var-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for a DeclBase." tag)))))
            (acl2::reterr (msg "The \"tag\" member of a DeclBase object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing a DeclBase must be a JSON object, but ~x0 is not." j))))

  ///

  (defret decl-huncheckedp-of-decl-fromJSON
      (implies (not erp)
               (decl-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

(define decl-list-fromJSON ((js json::value-listp))
  :returns (mv erp (x decl-listp))
  :measure (json::value-list-count js)
  :short "Convert a JSON array's elements to a @(tsee decl-listp)."
  (b* (((acl2::reterr) nil))
    (if (consp js)
        (b* (((acl2::erp hd)
              (decl-fromJSON (car js)))
             ((acl2::erp tl)
              (decl-list-fromJSON (cdr js))))
          (acl2::retok (cons hd tl)))
      (acl2::retok nil)))

  ///

  (defret decl-list-huncheckedp-of-decl-list-fromJSON
      (implies (not erp)
               (decl-list-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ProgBase
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-fromJSON ((j json::valuep))
  :returns (mv erp (x filep))
  :short "Convert a JSON value encoding a @('ProgBase') to a @(tsee file)."
  (b* (((acl2::reterr)
        (make-file :imports nil :decls nil)))
    (if (json::value-case j :object)
        (b* ((tag-j
              (json::object-member-value "tag" j)))
          (if (json::value-case tag-j :string)
              (b* ((tag
                    (json::value-string->get tag-j)))
                (cond
                  ((equal tag "Prog")
                   (b* ((decs-j
                         (json::object-member-value "progDecs" j)))
                     (if (json::value-case decs-j :array)
                         (b* ((decs-js
                               (json::value-array->elements decs-j))
                              ((acl2::erp decs)
                               (decl-list-fromJSON decs-js)))
                           (acl2::retok (make-file
                                         :imports nil
                                         :decls decs)))
                       (acl2::reterr (msg "The \"progDecs\" member of a Prog object must be a JSON array, but ~x0 is not." decs-j)))))
                  (t
                   (acl2::reterr (msg "~x0 is not a recognized tag for a ProgBase." tag)))))
            (acl2::reterr (msg "The \"tag\" member of a ProgBase object must be a string, but ~x0 is not." tag-j))))
      (acl2::reterr (msg "A JSON value representing a ProgBase must be a JSON object, but ~x0 is not." j))))

  ///

  (defret file-huncheckedp-of-file-fromJSON
      (implies (not erp)
               (file-huncheckedp x))
    :hints (("Goal" :in-theory (enable* ast-huncheckedp-rules)))))
