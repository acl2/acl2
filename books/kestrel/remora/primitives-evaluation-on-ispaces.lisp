; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Quan Luu (quan.luu@kestrel.edu)
;          Sarah Johnson

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "expression-values-and-environments")
(include-book "abstract-syntax-constructors")

(local (include-book "kestrel/lists-light/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitives-evaluation-on-ispaces
  :parents (dynamic-semantics)
  :short "Evaluation of Remora primitives on ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "Remora primitives, like other Remora functions,
     may be applied to types, ispaces, or expressions,
     according to the stages implied by their curried function types.
     See @(tsee primop-value) for a discussion of the stages.")
   (xdoc::p
    "Here we define the application of primitives to ispaces;
     more precisely, the application of
     primitive operation values satisfying @(tsee primop-value-ifunp)
     to ispace values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-iota/static ((s nat-listp))
  :returns (val expr-value-resultp)
  :short "Evaluation of the static index enumeration."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the @('iota/static') operation:
     the single ispace application supplies the shape @('s'),
     and the result is the array of that shape
     whose atoms are the naturals below the number of elements,
     in row-major order.
     Unlike most other operations, no argument cell is involved:
     the ispace application directly yields the final array,
     as with @('reify-dim') and @('reify-shape').")
   (xdoc::p
    "If the shape has a zero dimension, the result is empty;
     the element type is always the integer atom type."))
  (b* ((s (nat-list-fix s))
       ((when (member-equal 0 s))
        (expr-value-with-empty-dim s (type-value-base (base-type-int))))
       (atoms (expr-value-base-list
               (base-value-int-list
                (int-value-list-of (nat-list-from-to 0 (nat-list-product s)))))))
    (expr-value-with-nonempty-dims s atoms))
  :guard-hints (("Goal" :in-theory (enable nfix
                                           fix
                                           integer-listp-when-nat-listp
                                           expr-value-list-wfp-of-expr-value-base-list
                                           dims-of-expr-value-list-of-expr-value-base-list)))

  ///

  (defret expr-value-wfp-of-prim-iota/static
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hyp (nat-listp s)
    :hints (("Goal" :in-theory (enable expr-value-list-wfp-of-expr-value-base-list
                                       dims-of-expr-value-list-of-expr-value-base-list
                                       nfix
                                       fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-reify-dim ((d natp))
  :returns (val expr-valuep)
  :short "Evaluation of dimension reification."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the @('reify-dim') operation:
     the single ispace application supplies the dimension @('d'),
     and the result is the integer scalar with that value.
     Unlike most other operations, no argument cell is involved:
     the ispace application directly yields the final scalar,
     as with @('iota/static') and @('reify-shape').
     Also unlike most other operations, no error is possible,
     as with @('reify-shape'),
     so the result type is @(tsee expr-valuep),
     not @(tsee expr-value-resultp)."))
  (expr-value-base (base-value-int (int-value (lnfix d))))

  ///

  (defret expr-value-wfp-of-prim-reify-dim
    (expr-value-wfp val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-reify-shape ((s nat-listp))
  :returns (val expr-valuep)
  :short "Evaluation of shape reification."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the @('reify-shape') operation:
     the single ispace application supplies the shape @('s'),
     and the result is a box whose array value is
     the vector of the dimensions of the shape, as integers,
     whose witness is the rank of the shape (the length of that vector),
     and whose type is the existential type in
     the operation's type in @(tsee primop-types).
     Unlike most other operations, no argument cell is involved:
     the ispace application directly yields the final box,
     as with @('iota/static') and @('reify-dim');
     like the latter, no error is possible.")
   (xdoc::p
    "If the shape is empty, the rank is 0,
     and the boxed array value is the empty vector."))
  (b* ((s (nat-list-fix s))
       (rank (len s))
       (stype (make-type-value-sigma
               :param (ispace-var-dim "r")
               :body (t[] :int (shp "$r"))
               :denv (make-type-denv :ienv (make-ispace-denv :ispaces nil)
                                     :types nil)))
       ((when (endp s))
        (make-expr-value-box
         :ispace (ispace-value-dim 0)
         :array (expr-value-with-empty-dim (list 0)
                                           (type-value-base (base-type-int)))
         :type stype))
       (atoms (expr-value-base-list
               (base-value-int-list
                (int-value-list-of s)))))
    (make-expr-value-box
     :ispace (ispace-value-dim rank)
     :array (expr-value-with-nonempty-dims (list rank) atoms)
     :type stype))
  :guard-hints
  (("Goal" :in-theory (enable nfix
                              fix
                              nat-list-product
                              expr-value-list-wfp-of-expr-value-base-list
                              dims-of-expr-value-list-of-expr-value-base-list)))

  ///

  (defret expr-value-wfp-of-prim-reify-shape
    (expr-value-wfp val)
    :hyp (nat-listp s)
    :hints (("Goal" :in-theory (enable expr-value-list-wfp-of-expr-value-base-list
                                       dims-of-expr-value-list-of-expr-value-base-list
                                       nat-list-product
                                       nfix
                                       fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-undefined ()
  :returns (val expr-value-resultp)
  :short "Evaluation of the undefined operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the @('undefined') operation:
     it always fails.
     In [impl] this operation is Haskell's @('undefined'),
     i.e. its evaluation raises an error;
     here we return an error value.
     The instantiation values are irrelevant,
     so this function takes no arguments:
     the type and the shape only matter statically,
     to let the operation be used
     where a value of any type and shape is expected."))
  (reserr nil)

  ///

  (defret expr-value-wfp-of-prim-undefined
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop-ifun ((op primop-valuep) (ival ispace-valuep))
  :guard (primop-value-ifunp op)
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation value
          to an ispace value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of applying an ispace lambda abstraction to an ispace value:
     it is called by @(tsee eval-iapp)
     on a scalar primitive operation value
     and the ispace argument value.")
   (xdoc::p
    "The guard requires the value to be applicable to ispace values
     (see @(tsee primop-value-ifunp)).
     Each stage applicable to ispace values expects
     an ispace value of a specific sort,
     namely the sort of the next ispace parameter
     in the operation's type in @(tsee primop-types):
     a dimension for the stages that store just a type value
     (except @(':reshape-t'), which expects the first of two shapes),
     a shape for the stages that also store a dimension or a shape;
     the uninstantiated stage of @('sum'), which has no type parameter,
     stores nothing and expects a shape directly;
     the @('iota/static'), @('reify-dim'), and @('reify-shape') operations,
     which consist of a single stage,
     also store nothing and expect
     a shape (a dimension, for @('reify-dim')) directly;
     the uninstantiated stage of @('iota'), which has no type parameter,
     stores nothing and expects a dimension directly.
     We check that the ispace value has the expected sort;
     then we construct the next instantiation stage of the operation,
     which stores the ispace values received
     (a dimension and a shape
     for @('head'), @('tail'), @('length'), @('reverse'), and @('reduce');
     a dimension and two shapes for @('fold');
     two dimensions and a shape for @('append') and @('flatten');
     a dimension for @('index');
     two dimensions for @('index2d');
     a shape for @('sum');
     two shapes for @('reshape');
     two dimensions for @('transpose2d');
     a dimension for @('iota');
     two shapes for @('trace')),
     along with the previously received type values (if any);
     for @('iota/static'), @('reify-dim'), and @('reify-shape'),
     the application instead directly yields the final result,
     and for @('undefined') it yields an error.
     Anything else is an error."))
  (primop-value-case
   op
   :head-t (ispace-value-case
            ival
            :dim (expr-value-primop
                  (make-primop-value-head-t-d :tval op.tval
                                              :dval ival.val))
            :shape (reserr nil))
   :head-t-d (ispace-value-case
              ival
              :dim (reserr nil)
              :shape (expr-value-primop
                      (make-primop-value-head-t-d-s :tval op.tval
                                                    :dval op.dval
                                                    :sval ival.val)))
   :tail-t (ispace-value-case
            ival
            :dim (expr-value-primop
                  (make-primop-value-tail-t-d :tval op.tval
                                              :dval ival.val))
            :shape (reserr nil))
   :tail-t-d (ispace-value-case
              ival
              :dim (reserr nil)
              :shape (expr-value-primop
                      (make-primop-value-tail-t-d-s :tval op.tval
                                                    :dval op.dval
                                                    :sval ival.val)))
   :length-t (ispace-value-case
              ival
              :dim (expr-value-primop
                    (make-primop-value-length-t-d :tval op.tval
                                                  :dval ival.val))
              :shape (reserr nil))
   :length-t-d (ispace-value-case
                ival
                :dim (reserr nil)
                :shape (expr-value-primop
                        (make-primop-value-length-t-d-s :tval op.tval
                                                        :dval op.dval
                                                        :sval ival.val)))
   :append-t (ispace-value-case
              ival
              :dim (expr-value-primop
                    (make-primop-value-append-t-m :tval op.tval
                                                  :mval ival.val))
              :shape (reserr nil))
   :append-t-m (ispace-value-case
                ival
                :dim (expr-value-primop
                      (make-primop-value-append-t-m-n :tval op.tval
                                                      :mval op.mval
                                                      :nval ival.val))
                :shape (reserr nil))
   :append-t-m-n (ispace-value-case
                  ival
                  :dim (reserr nil)
                  :shape (expr-value-primop
                          (make-primop-value-append-t-m-n-s :tval op.tval
                                                            :mval op.mval
                                                            :nval op.nval
                                                            :sval ival.val)))
   :reverse-t (ispace-value-case
               ival
               :dim (expr-value-primop
                     (make-primop-value-reverse-t-d :tval op.tval
                                                    :dval ival.val))
               :shape (reserr nil))
   :reverse-t-d (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (expr-value-primop
                         (make-primop-value-reverse-t-d-s :tval op.tval
                                                          :dval op.dval
                                                          :sval ival.val)))
   :index-t (ispace-value-case
             ival
             :dim (expr-value-primop
                   (make-primop-value-index-t-m :tval op.tval
                                                :mval ival.val))
             :shape (reserr nil))
   :index2d-t (ispace-value-case
               ival
               :dim (expr-value-primop
                     (make-primop-value-index2d-t-m :tval op.tval
                                                    :mval ival.val))
               :shape (reserr nil))
   :index2d-t-m (ispace-value-case
                 ival
                 :dim (expr-value-primop
                       (make-primop-value-index2d-t-m-n :tval op.tval
                                                        :mval op.mval
                                                        :nval ival.val))
                 :shape (reserr nil))
   :sum (ispace-value-case
         ival
         :dim (reserr nil)
         :shape (expr-value-primop
                 (make-primop-value-sum-s :sval ival.val)))
   :reshape-t (ispace-value-case
               ival
               :dim (reserr nil)
               :shape (expr-value-primop
                       (make-primop-value-reshape-t-s1 :tval op.tval
                                                       :s1val ival.val)))
   :reshape-t-s1 (ispace-value-case
                  ival
                  :dim (reserr nil)
                  :shape (expr-value-primop
                          (make-primop-value-reshape-t-s1-s2 :tval op.tval
                                                             :s1val op.s1val
                                                             :s2val ival.val)))
   :flatten-t (ispace-value-case
               ival
               :dim (expr-value-primop
                     (make-primop-value-flatten-t-m :tval op.tval
                                                    :mval ival.val))
               :shape (reserr nil))
   :flatten-t-m (ispace-value-case
                 ival
                 :dim (expr-value-primop
                       (make-primop-value-flatten-t-m-n :tval op.tval
                                                        :mval op.mval
                                                        :nval ival.val))
                 :shape (reserr nil))
   :flatten-t-m-n (ispace-value-case
                   ival
                   :dim (reserr nil)
                   :shape (expr-value-primop
                           (make-primop-value-flatten-t-m-n-s :tval op.tval
                                                              :mval op.mval
                                                              :nval op.nval
                                                              :sval ival.val)))
   :transpose2d-t (ispace-value-case
                   ival
                   :dim (expr-value-primop
                         (make-primop-value-transpose2d-t-m :tval op.tval
                                                            :mval ival.val))
                   :shape (reserr nil))
   :transpose2d-t-m (ispace-value-case
                     ival
                     :dim (expr-value-primop
                           (make-primop-value-transpose2d-t-m-n :tval op.tval
                                                                :mval op.mval
                                                                :nval ival.val))
                     :shape (reserr nil))
   :iota/static (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (prim-iota/static ival.val))
   :reduce-t (ispace-value-case
              ival
              :dim (expr-value-primop
                    (make-primop-value-reduce-t-d :tval op.tval
                                                  :dval ival.val))
              :shape (reserr nil))
   :reduce-t-d (ispace-value-case
                ival
                :dim (reserr nil)
                :shape (expr-value-primop
                        (make-primop-value-reduce-t-d-s :tval op.tval
                                                        :dval op.dval
                                                        :sval ival.val)))
   :fold-t-t2 (ispace-value-case
               ival
               :dim (expr-value-primop
                     (make-primop-value-fold-t-t2-d :tval op.tval
                                                    :t2val op.t2val
                                                    :dval ival.val))
               :shape (reserr nil))
   :fold-t-t2-d (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (expr-value-primop
                         (make-primop-value-fold-t-t2-d-s :tval op.tval
                                                          :t2val op.t2val
                                                          :dval op.dval
                                                          :sval ival.val)))
   :fold-t-t2-d-s (ispace-value-case
                   ival
                   :dim (reserr nil)
                   :shape (expr-value-primop
                           (make-primop-value-fold-t-t2-d-s-s2
                            :tval op.tval
                            :t2val op.t2val
                            :dval op.dval
                            :sval op.sval
                            :s2val ival.val)))
   :reify-dim (ispace-value-case
               ival
               :dim (prim-reify-dim ival.val)
               :shape (reserr nil))
   :reify-shape (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (prim-reify-shape ival.val))
   :iota (ispace-value-case
          ival
          :dim (expr-value-primop
                (make-primop-value-iota-d
                 :dval ival.val))
          :shape (reserr nil))
   :trace-t-r (ispace-value-case
               ival
               :dim (reserr nil)
               :shape (expr-value-primop
                       (make-primop-value-trace-t-r-s :tval op.tval
                                                      :rval op.rval
                                                      :sval ival.val)))
   :trace-t-r-s (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (expr-value-primop
                         (make-primop-value-trace-t-r-s-q :tval op.tval
                                                          :rval op.rval
                                                          :sval op.sval
                                                          :qval ival.val)))
   :undefined-t (ispace-value-case
                 ival
                 :dim (reserr nil)
                 :shape (prim-undefined))
   :otherwise (prog2$ (impossible) (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-ifunp)))

  ///

  (defret expr-value-wfp-of-eval-primop-ifun
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hints (("Goal" :in-theory (enable primop-value-wfp
                                       check-dims-of-primop-value)))))
