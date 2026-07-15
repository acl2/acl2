; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-values-and-environments")

(local (include-book "std/basic/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitive-operation-values
  :parents (expression-values-and-environments)
  :short "Primitive operation values."
  :long
  (xdoc::topstring
   (xdoc::p
    "By `primitive operation' we mean
     a built-in Remora function
     that is not implemented in Remora
     and that is implicitly in scope (unless overwritten).
     Syntactically, it is a variable,
     whose value is the reification of the operation.
     We represent this as a special kind of expression value,
     which includes not only the ``full'' operations,
     but also partially instantiated forms of those operations;
     the latter are essentially closures.
     See @(tsee primop-value) for details and examples.")
   (xdoc::p
    "The term `primitive' comes from [thesis], [arxiv], and [esop].
     Instead, [impl] uses the terms `primitive' and `intrinsic':
     the first for the ones on integer and similar types,
     and the second for the ones on lists and similar types.
     The latter are polymorphic while the former are monomorphic,
     but that division is not the explicit intention in [impl]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum primop-value
  :short "Fixtype of primitive operation values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixtype contains summands for the primitive operations themselves,
     in correspondence with the entries of @(tsee primop-types),
     as well as summands for partially and fully instantiated
     polymorphic operations (more details below).")
   (xdoc::p
    "A value of this fixtype represents a primitive operation,
     or an instantiation stage thereof,
     as a scalar (zero-rank array) function value,
     analogously to how the three kinds of lambda abstractions
     are scalar function values.
     These are incorporated into @(tsee expr-value)
     as its @(':primop') summand;
     the operations they denote is evaluated via
     the ACL2 functions in @(see primitives-evaluation).")
   (xdoc::p
    "The operations from @(':int-add') to @(':bool-to-float') are monomorphic:
     the element type of each operation's zero-rank array type
     is a function type between base types.
     Remora also has polymorphic primitive operations,
     such as @('head'), @('tail'), and @('length'),
     where the element type of the zero-rank array type
     involves universal and product types.
     Since a polymorphic operation cannot be
     directly applied to expression values,
     but must first be applied to type values and/or ispace values,
     this fixtype includes,
     for each polymorphic operation,
     a summand for each instantiation stage of the operation,
     whose fields hold the instantiation values received so far.")
   (xdoc::p
    "Currently the only polymorphic operations are
     @('head'), @('tail'), and @('length'),
     each with three similar stages.
     For example, here are the stages of @('length'):
     @(':length') is the uninstantiated operation;
     @(':length-t') is the operation applied to
     a type value for its type parameter;
     @(':length-t-d-s') is the operation further applied to
     ispace values for its ispace parameters,
     i.e. a natural number for the dimension parameter
     and a list of natural numbers for the shape parameter."))
  (:int-add ())
  (:int-sub ())
  (:int-mul ())
  (:int-div ())
  (:int-expt ())
  (:int-mod ())
  (:int-max ())
  (:int-min ())
  (:int-bit-and ())
  (:int-bit-or ())
  (:int-bit-xor ())
  (:int-shl ())
  (:int-shr ())
  (:int-bit-not ())
  (:int-popc ())
  (:int-eq ())
  (:int-neq ())
  (:int-lt ())
  (:int-gt ())
  (:int-leq ())
  (:int-geq ())
  (:int-to-float ())
  (:int-to-bool ())
  (:float-add ())
  (:float-sub ())
  (:float-mul ())
  (:float-div ())
  (:float-expt ())
  (:float-max ())
  (:float-min ())
  (:float-sqrt ())
  (:float-eq ())
  (:float-neq ())
  (:float-lt ())
  (:float-gt ())
  (:float-leq ())
  (:float-geq ())
  (:float-truncate ())
  (:float-round ())
  (:float-ceiling ())
  (:float-floor ())
  (:bool-not ())
  (:bool-and ())
  (:bool-or ())
  (:bool-eq ())
  (:bool-neq ())
  (:bool-to-int ())
  (:bool-to-float ())
  (:head ())
  (:head-t ((tval type-value)))
  (:head-t-d-s ((tval type-value)
                (dval nat)
                (sval nat-list)))
  (:tail ())
  (:tail-t ((tval type-value)))
  (:tail-t-d-s ((tval type-value)
                (dval nat)
                (sval nat-list)))
  (:length ())
  (:length-t ((tval type-value)))
  (:length-t-d-s ((tval type-value)
                  (dval nat)
                  (sval nat-list)))
  (:append ())
  (:append-t ((tval type-value)))
  (:append-t-m-n-s ((tval type-value)
                  (mval nat)
                  (nval nat)
                  (sval nat-list)))
  :pred primop-valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-funp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is
          applicable to expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "A primitive operation value (see @(tsee primop-value))
     may be applicable to expression values (via term applications),
     or to type values (via type applications),
     or to ispace values (via ispace applications).
     This predicate,
     along with @(tsee primop-value-tfunp) and @(tsee primop-value-ifunp),
     checks these applicabilities,
     which are exhaustive and non-overlapping.
     The three predicates mirror the three kinds of lambda abstraction values,
     i.e. the @(':lambda'), @(':tlambda'), and @(':ilambda') summands
     of @(tsee expr-value).")
   (xdoc::p
    "This predicate holds on the monomorphic primitive operations,
     which need no instantiation,
     and on the fully instantiated stages
     of the polymorphic primitive operations."))
  (primop-value-case op
                     :head nil
                     :head-t nil
                     :tail nil
                     :tail-t nil
                     :length nil
                     :length-t nil
                     :append nil
                     :append-t nil
                     :otherwise t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-tfunp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is
          applicable to type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee primop-value-funp) for
     a description of the three applicability predicates.")
   (xdoc::p
    "This predicate holds on
     the stages of polymorphic primitive operations
     that expect type values next."))
  (primop-value-case op
                     :head t
                     :tail t
                     :length t
                     :append t
                     :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-ifunp ((op primop-valuep))
  :returns (yes/no booleanp)
  :short "Check if a primitive operation value is applicable to ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee primop-value-funp) for
     a description of the three applicability predicates.")
   (xdoc::p
    "This predicate holds on
     the stages of polymorphic primitive operations
     that expect ispace values next."))
  (primop-value-case op
                     :head-t t
                     :tail-t t
                     :length-t t
                     :append-t t
                     :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection primop-value-applicability-theorems
  :short "Theorems about the applicability predicates
          for primitive operation values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates
     @(tsee primop-value-funp),
     @(tsee primop-value-tfunp), and
     @(tsee primop-value-ifunp)
     are exhaustive and non-overlapping:
     every primitive operation value satisfies exactly one of them."))

  (defrule primop-value-applicability-exhaustive
    (or (primop-value-funp op)
        (primop-value-tfunp op)
        (primop-value-ifunp op))
    :rule-classes nil
    :enable (primop-value-funp
             primop-value-tfunp
             primop-value-ifunp))

  (defrule primop-value-applicability-non-overlapping
    (and (not (and (primop-value-funp op)
                   (primop-value-tfunp op)))
         (not (and (primop-value-funp op)
                   (primop-value-ifunp op)))
         (not (and (primop-value-tfunp op)
                   (primop-value-ifunp op))))
    :rule-classes nil
    :enable (primop-value-funp
             primop-value-tfunp
             primop-value-ifunp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define primop-value-uninstantiated ((op primop-valuep))
  :returns (uninst primop-valuep)
  :short "Uninstantiated stage of a primitive operation value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This maps each stage of a polymorphic primitive operation
     to the uninstantiated stage of the same operation,
     discarding the instantiation values (if any);
     it maps every other primitive operation value to itself."))
  (primop-value-case op
                     :head-t (primop-value-head)
                     :head-t-d-s (primop-value-head)
                     :tail-t (primop-value-tail)
                     :tail-t-d-s (primop-value-tail)
                     :length-t (primop-value-length)
                     :length-t-d-s (primop-value-length)
                     :append-t (primop-value-append)
                     :append-t-m-n-s (primop-value-append)
                     :otherwise (primop-value-fix op)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-of-primop-value-fun ((op primop-valuep))
  :guard (primop-value-funp op)
  :returns (type type-valuep)
  :short "Type of a primitive operation value applicable to expression values,
          as a type value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type value form of the type that
     @(tsee primop-types) associates to the operation's surface name.
     We keep this consistent with @(tsee primop-types) by construction;
     a theorem relating the two could be added later.")
   (xdoc::p
    "Currently this type is always
     a zero-rank array of the operation's function type,
     whose inputs and output are themselves
     zero-rank arrays of base types.
     From this type value we can obtain,
     for an operation used as a function value,
     both the expected cell dimensions of its arguments
     and the type of its result,
     uniformly with how the same information
     is obtained for lambda abstractions.")
   (xdoc::p
    "This function is restricted, via the guard,
     to the primitive operation values applicable to expression values,
     which are the ones used as function values.
     For the fully instantiated stages
     of polymorphic primitive operations,
     the function type value is constructed
     from the instantiation values in the fields:
     for the @(':length-t-d-s') stage of @('length'),
     the input is an array of the stored type value,
     whose dimensions are the stored dimension
     followed by the stored shape,
     and the output is the zero-rank array of the integer type.
     For the stages not applicable to expression values,
     which are outside the guard,
     we return an irrelevant type value."))
  (b* ((int-tv (make-type-value-array
                :elem (type-value-base (base-type-int))
                :dims nil))
       (bool-tv (make-type-value-array
                 :elem (type-value-base (base-type-bool))
                 :dims nil))
       (float-tv (make-type-value-array
                  :elem (type-value-base (base-type-float))
                  :dims nil))
       (int-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv int-tv) :out int-tv)
         :dims nil))
       (int-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out int-tv)
         :dims nil))
       (int-relop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv int-tv) :out bool-tv)
         :dims nil))
       (int-to-float-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out float-tv)
         :dims nil))
       (int-to-bool-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list int-tv) :out bool-tv)
         :dims nil))
       (float-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv float-tv) :out float-tv)
         :dims nil))
       (float-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv) :out float-tv)
         :dims nil))
       (float-relop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv float-tv) :out bool-tv)
         :dims nil))
       (float-to-int-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list float-tv) :out int-tv)
         :dims nil))
       (bool-unop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out bool-tv)
         :dims nil))
       (bool-binop-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv bool-tv) :out bool-tv)
         :dims nil))
       (bool-to-int-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out int-tv)
         :dims nil))
       (bool-to-float-tv
        (make-type-value-array
         :elem (make-type-value-fun :in (list bool-tv) :out float-tv)
         :dims nil)))
    (primop-value-case
     op
     :int-add int-binop-tv
     :int-sub int-binop-tv
     :int-mul int-binop-tv
     :int-div int-binop-tv
     :int-expt int-binop-tv
     :int-mod int-binop-tv
     :int-max int-binop-tv
     :int-min int-binop-tv
     :int-bit-and int-binop-tv
     :int-bit-or int-binop-tv
     :int-bit-xor int-binop-tv
     :int-shl int-binop-tv
     :int-shr int-binop-tv
     :int-bit-not int-unop-tv
     :int-popc int-unop-tv
     :int-eq int-relop-tv
     :int-neq int-relop-tv
     :int-lt int-relop-tv
     :int-gt int-relop-tv
     :int-leq int-relop-tv
     :int-geq int-relop-tv
     :int-to-float int-to-float-tv
     :int-to-bool int-to-bool-tv
     :float-add float-binop-tv
     :float-sub float-binop-tv
     :float-mul float-binop-tv
     :float-div float-binop-tv
     :float-expt float-binop-tv
     :float-max float-binop-tv
     :float-min float-binop-tv
     :float-sqrt float-unop-tv
     :float-eq float-relop-tv
     :float-neq float-relop-tv
     :float-lt float-relop-tv
     :float-gt float-relop-tv
     :float-leq float-relop-tv
     :float-geq float-relop-tv
     :float-truncate float-to-int-tv
     :float-round float-to-int-tv
     :float-ceiling float-to-int-tv
     :float-floor float-to-int-tv
     :bool-not bool-unop-tv
     :bool-and bool-binop-tv
     :bool-or bool-binop-tv
     :bool-eq bool-binop-tv
     :bool-neq bool-binop-tv
     :bool-to-int bool-to-int-tv
     :bool-to-float bool-to-float-tv
     :head (prog2$ (impossible) (type-value-base (base-type-bool)))
     :head-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :head-t-d-s (make-type-value-array
                  :elem (make-type-value-fun
                         :in (list (make-type-value-array
                                    :elem op.tval
                                    :dims (cons (1+ op.dval) op.sval)))
                         :out (make-type-value-array
                               :elem op.tval
                               :dims op.sval))
                  :dims nil)
     :tail (prog2$ (impossible) (type-value-base (base-type-bool)))
     :tail-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :tail-t-d-s (make-type-value-array
                  :elem (make-type-value-fun
                         :in (list (make-type-value-array
                                    :elem op.tval
                                    :dims (cons (1+ op.dval) op.sval)))
                         :out (make-type-value-array
                               :elem op.tval
                               :dims (cons op.dval op.sval)))
                  :dims nil)
     :length (prog2$ (impossible) (type-value-base (base-type-bool)))
     :length-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :length-t-d-s (make-type-value-array
                    :elem (make-type-value-fun
                           :in (list (make-type-value-array
                                      :elem op.tval
                                      :dims (cons op.dval op.sval)))
                           :out int-tv)
                    :dims nil)
     :append (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t (prog2$ (impossible) (type-value-base (base-type-bool)))
     :append-t-m-n-s (make-type-value-array
                      :elem (make-type-value-fun
                             :in (list (make-type-value-array
                                        :elem op.tval
                                        :dims (cons op.mval op.sval))
                                       (make-type-value-array
                                        :elem op.tval
                                        :dims (cons op.nval op.sval)))
                             :out (make-type-value-array
                                   :elem op.tval
                                   :dims (cons (+ op.mval op.nval) op.sval)))
                      :dims nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-funp)))

  ///

  (defret type-value-kind-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind type) :array))
    :hints (("Goal" :in-theory (enable primop-value-funp))))

  (defret type-value-kind-of-elem-of-type-of-primop-value-fun
    (implies (primop-value-funp op)
             (equal (type-value-kind (type-value-array->elem type)) :fun))
    :hints (("Goal" :in-theory (enable primop-value-funp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define arity-of-primop-value-fun ((op primop-valuep))
  :guard (primop-value-funp op)
  :returns (arity natp)
  :short "Arity of a primitive operation value applicable to expression values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the number of expression arguments that the operation takes,
     matching the @('prim-...') function that defines its semantics
     in @(see primitives-evaluation):
     1 for the unary operations, 2 for the binary ones.")
   (xdoc::p
    "We define this as the number of inputs
     of the operation's function type (see @(tsee type-of-primop-value-fun)),
     so that the arity cannot diverge from the type.
     Like @(tsee type-of-primop-value-fun),
     this function is restricted, via the guard,
     to the values applicable to expression values."))
  (len (type-value-fun->in
        (type-value-array->elem (type-of-primop-value-fun op)))))
