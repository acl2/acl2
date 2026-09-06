; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-equivalence")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence-derived-rules
  :parents (static-semantics)
  :short "Derived inference rules for type equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see ispace-equivalence-derived-rules):
     each derived rule comes with a proof tree constructor,
     defined in terms of the constructors of the defining rules,
     as well as a @('make-...') macro with keyword arguments;
     the derived rule is proved as a theorem
     from the validity theorem of the proof tree constructor,
     via the soundness theorem @('type-eq-when-proof-validp')
     and the witness function @('type-eq-proof')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-trans-swapped
  :short "Transitivity of type equivalence with the premises swapped."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-trans-swapped)."))

  (define type-eq-proof-trans-swapped (type1
                                       type2
                                       type3
                                       (premise1-proof type-eq-proofp)
                                       (premise2-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (make-type-eq-proof-trans :type1 type1
                              :type2 type2
                              :type3 type3
                              :premise1-proof premise2-proof
                              :premise2-proof premise1-proof)

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-trans-swapped
      (implies (and (type-eq-proof-validp premise1-proof type2 type3)
                    (type-eq-proof-validp premise2-proof type1 type2))
               (type-eq-proof-validp proof type1 type3))
      :hints (("Goal"
               :expand ((type-eq-proof-validp
                         (type-eq-proof-trans type1 type2 type3
                                              premise2-proof premise1-proof)
                         type1 type3))
               :in-theory (enable type-eq-trans-validp
                                  typep-when-type-eq-proof-validp)))))

  (defruled type-eq-trans-swapped
    (implies (and (type-eq type2 type3)
                  (type-eq type1 type2))
             (type-eq type1 type3))
    :use ((:instance type-eq (type1 type2) (type2 type3))
          (:instance type-eq (type1 type1) (type2 type2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-trans-swapped
                             type1 type2 type3
                             (type-eq-proof type2 type3)
                             (type-eq-proof type1 type2)))
                     (concl.type1 type1)
                     (concl.type2 type3))))

  (defmacro make-type-eq-proof-trans-swapped (&key type1
                                                   type2
                                                   type3
                                                   premise1-proof
                                                   premise2-proof)
    `(type-eq-proof-trans-swapped
      ,type1 ,type2 ,type3 ,premise1-proof ,premise2-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-scalar
  :short "Congruence of type equivalence with respect to
          the element types of scalar array types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an instance of the rule @('array')
     with the empty shape as ispace, on both sides,
     which is equivalent to itself via reflexivity."))

  (define type-eq-proof-cong-scalar (type1
                                     type2
                                     (premise1-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (make-type-eq-proof-array
     :type1 type1
     :type2 type2
     :ispace1 (ispace-shape (shape-dims nil))
     :ispace2 (ispace-shape (shape-dims nil))
     :premise1-proof premise1-proof)

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-cong-scalar
      (implies (type-eq-proof-validp premise1-proof type1 type2)
               (type-eq-proof-validp proof
                                     (type-scalar type1)
                                     (type-scalar type2)))
      :hints
      (("Goal"
        :in-theory (enable* type-equivalence-definition-validp-defs
                            typep-when-type-eq-proof-validp
                            ispace-eq-refl
                            type-scalar)))))

  (defruled type-eq-cong-scalar
    (implies (type-eq type1 type2)
             (type-eq (type-scalar type1) (type-scalar type2)))
    :use ((:instance type-eq (type1 type1) (type2 type2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-cong-scalar
                             type1 type2 (type-eq-proof type1 type2)))
                     (concl.type1 (type-scalar type1))
                     (concl.type2 (type-scalar type2)))))

  (defmacro make-type-eq-proof-cong-scalar (&key type1 type2 premise1-proof)
    `(type-eq-proof-cong-scalar ,type1 ,type2 ,premise1-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-bracket
  :short "Congruence of type equivalence with respect to
          the element types of bracket types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule @('bracket') reduces a bracket type to an array type
     whose ispace is the splice of the ispaces of the bracket type.
     This derived rule rewrites the element type of a bracket type,
     leaving the ispaces unchanged:
     it reduces the bracket type to the array type,
     rewrites the element type via the rule @('array'),
     and reduces the array type back to a bracket type via symmetry,
     chaining the three steps via transitivity."))

  (define type-eq-proof-cong-bracket (type1
                                      type2
                                      ispaces
                                      (premise1-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (b* (((unless (and (typep type1)
                       (typep type2)
                       (ispace-listp ispaces)))
          (type-eq-proof-refl nil))
         (ispace (ispace-shape (shape-splice ispaces))))
      (make-type-eq-proof-trans
       :type1 (type-bracket type1 ispaces)
       :type2 (type-array type1 ispace)
       :type3 (type-bracket type2 ispaces)
       :premise1-proof (make-type-eq-proof-bracket :type type1
                                                   :ispaces ispaces
                                                   :ispace ispace)
       :premise2-proof
       (make-type-eq-proof-trans
        :type1 (type-array type1 ispace)
        :type2 (type-array type2 ispace)
        :type3 (type-bracket type2 ispaces)
        :premise1-proof
        (make-type-eq-proof-array :type1 type1
                                  :type2 type2
                                  :ispace1 ispace
                                  :ispace2 ispace
                                  :premise1-proof premise1-proof)
        :premise2-proof
        (make-type-eq-proof-symm
         :type1 (type-bracket type2 ispaces)
         :type2 (type-array type2 ispace)
         :premise1-proof (make-type-eq-proof-bracket :type type2
                                                     :ispaces ispaces
                                                     :ispace ispace)))))

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-cong-bracket
      (implies (and (ispace-listp ispaces)
                    (type-eq-proof-validp premise1-proof type1 type2))
               (type-eq-proof-validp proof
                                     (type-bracket type1 ispaces)
                                     (type-bracket type2 ispaces)))
      :hints
      (("Goal"
        :in-theory (enable* type-equivalence-definition-validp-defs
                            typep-when-type-eq-proof-validp
                            ispace-eq-refl)))))

  (defruled type-eq-cong-bracket
    (implies (and (ispace-listp ispaces)
                  (type-eq type1 type2))
             (type-eq (type-bracket type1 ispaces)
                      (type-bracket type2 ispaces)))
    :use ((:instance type-eq (type1 type1) (type2 type2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-cong-bracket
                             type1 type2 ispaces (type-eq-proof type1 type2)))
                     (concl.type1 (type-bracket type1 ispaces))
                     (concl.type2 (type-bracket type2 ispaces)))))

  (defmacro make-type-eq-proof-cong-bracket (&key type1
                                                  type2
                                                  ispaces
                                                  premise1-proof)
    `(type-eq-proof-cong-bracket ,type1 ,type2 ,ispaces ,premise1-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-funn-nil
  :short "Congruence of type equivalence with respect to
          the output types of nullary function types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule @('fun0') reduces a nullary function type to its output type.
     This derived rule rewrites the output type of a nullary function type:
     it reduces the nullary function type to its output type,
     rewrites the output type (via the premise),
     and reduces back to a nullary function type via symmetry,
     chaining the three steps via transitivity."))

  (define type-eq-proof-cong-funn-nil (type-out1
                                       type-out2
                                       (premise1-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (b* (((unless (and (typep type-out1)
                       (typep type-out2)))
          (type-eq-proof-refl nil)))
      (make-type-eq-proof-trans
       :type1 (type-funn nil type-out1)
       :type2 type-out1
       :type3 (type-funn nil type-out2)
       :premise1-proof (make-type-eq-proof-fun0 :type-out type-out1)
       :premise2-proof
       (make-type-eq-proof-trans
        :type1 type-out1
        :type2 type-out2
        :type3 (type-funn nil type-out2)
        :premise1-proof premise1-proof
        :premise2-proof
        (make-type-eq-proof-symm
         :type1 (type-funn nil type-out2)
         :type2 type-out2
         :premise1-proof (make-type-eq-proof-fun0 :type-out type-out2)))))

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-cong-funn-nil
      (implies (type-eq-proof-validp premise1-proof type-out1 type-out2)
               (type-eq-proof-validp proof
                                     (type-funn nil type-out1)
                                     (type-funn nil type-out2)))
      :hints
      (("Goal"
        :in-theory (enable* type-equivalence-definition-validp-defs
                            typep-when-type-eq-proof-validp)))))

  (defruled type-eq-cong-funn-nil
    (implies (type-eq type-out1 type-out2)
             (type-eq (type-funn nil type-out1)
                      (type-funn nil type-out2)))
    :use ((:instance type-eq (type1 type-out1) (type2 type-out2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-cong-funn-nil
                             type-out1
                             type-out2
                             (type-eq-proof type-out1 type-out2)))
                     (concl.type1 (type-funn nil type-out1))
                     (concl.type2 (type-funn nil type-out2)))))

  (defmacro make-type-eq-proof-cong-funn-nil (&key type-out1
                                                   type-out2
                                                   premise1-proof)
    `(type-eq-proof-cong-funn-nil ,type-out1 ,type-out2 ,premise1-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-funn1
  :short "Congruence of type equivalence with respect to
          the input and output types of unary n-ary function types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule @('fun1') reduces an n-ary function type with one input type
     to the corresponding unary function type.
     This derived rule rewrites the input and output types:
     it reduces the n-ary function type to the unary function type,
     rewrites the components of the latter via the rule @('fun'),
     and reduces back to an n-ary function type via symmetry,
     chaining the three steps via transitivity."))

  (define type-eq-proof-cong-funn1 (type-in1
                                    type-in2
                                    type-out1
                                    type-out2
                                    (premise1-proof type-eq-proofp)
                                    (premise2-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (b* (((unless (and (typep type-in1)
                       (typep type-in2)
                       (typep type-out1)
                       (typep type-out2)))
          (type-eq-proof-refl nil)))
      (make-type-eq-proof-trans
       :type1 (type-funn (list type-in1) type-out1)
       :type2 (type-fun type-in1 type-out1)
       :type3 (type-funn (list type-in2) type-out2)
       :premise1-proof (make-type-eq-proof-fun1 :type-in type-in1
                                                :type-out type-out1)
       :premise2-proof
       (make-type-eq-proof-trans
        :type1 (type-fun type-in1 type-out1)
        :type2 (type-fun type-in2 type-out2)
        :type3 (type-funn (list type-in2) type-out2)
        :premise1-proof (make-type-eq-proof-fun :type-in1 type-in1
                                                :type-in2 type-in2
                                                :type-out1 type-out1
                                                :type-out2 type-out2
                                                :premise1-proof premise1-proof
                                                :premise2-proof premise2-proof)
        :premise2-proof
        (make-type-eq-proof-symm
         :type1 (type-funn (list type-in2) type-out2)
         :type2 (type-fun type-in2 type-out2)
         :premise1-proof (make-type-eq-proof-fun1 :type-in type-in2
                                                  :type-out type-out2)))))

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-cong-funn1
      (implies (and (type-eq-proof-validp premise1-proof type-in1 type-in2)
                    (type-eq-proof-validp premise2-proof type-out1 type-out2))
               (type-eq-proof-validp proof
                                     (type-funn (list type-in1) type-out1)
                                     (type-funn (list type-in2) type-out2)))
      :hints
      (("Goal"
        :expand ((type-eq-proof-validp
                  (type-eq-proof-fun type-in1 type-in2 type-out1 type-out2
                                     premise1-proof premise2-proof)
                  (type-fun type-in1 type-out1)
                  (type-fun type-in2 type-out2)))
        :in-theory (enable* type-equivalence-definition-validp-defs
                            typep-when-type-eq-proof-validp)))))

  (defruled type-eq-cong-funn1
    (implies (and (type-eq type-in1 type-in2)
                  (type-eq type-out1 type-out2))
             (type-eq (type-funn (list type-in1) type-out1)
                      (type-funn (list type-in2) type-out2)))
    :use ((:instance type-eq (type1 type-in1) (type2 type-in2))
          (:instance type-eq (type1 type-out1) (type2 type-out2))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-cong-funn1
                             type-in1
                             type-in2
                             type-out1
                             type-out2
                             (type-eq-proof type-in1 type-in2)
                             (type-eq-proof type-out1 type-out2)))
                     (concl.type1 (type-funn (list type-in1) type-out1))
                     (concl.type2 (type-funn (list type-in2) type-out2)))))

  (defmacro make-type-eq-proof-cong-funn1 (&key type-in1
                                                type-in2
                                                type-out1
                                                type-out2
                                                premise1-proof
                                                premise2-proof)
    `(type-eq-proof-cong-funn1 ,type-in1 ,type-in2
                               ,type-out1 ,type-out2
                               ,premise1-proof ,premise2-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-funn2m
  :short "Congruence of type equivalence with respect to
          the first input type and the rest of
          n-ary function types with two or more input types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule @('fun2m') reduces an n-ary function type
     with two or more input types to
     a unary function type from the first input type
     to the scalar array type of
     the n-ary function type with the remaining input types.
     This derived rule rewrites the first input type
     and the n-ary function type with the remaining input types
     (the latter via a premise about n-ary function types,
     so that the rule can be applied inductively along the input types):
     it reduces the n-ary function type to the unary function type,
     rewrites the components of the latter via the rule @('fun')
     (the output type via @(tsee type-eq-cong-scalar)),
     and reduces back to an n-ary function type via symmetry,
     chaining the three steps via transitivity.")
   (xdoc::p
    "The remaining input types are a rule variable,
     which must be a non-empty list;
     the proof tree for the rule @('fun2m')
     takes the first of the remaining input types
     and the rest of the remaining input types."))

  (define type-eq-proof-cong-funn2m (type-in1
                                     type-in2
                                     types-in1
                                     types-in2
                                     type-out1
                                     type-out2
                                     (premise1-proof type-eq-proofp)
                                     (premise2-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (b* (((unless (and (typep type-in1)
                       (typep type-in2)
                       (type-listp types-in1)
                       (type-listp types-in2)
                       (consp types-in1)
                       (consp types-in2)
                       (typep type-out1)
                       (typep type-out2)))
          (type-eq-proof-refl nil))
         (rest1 (type-funn types-in1 type-out1))
         (rest2 (type-funn types-in2 type-out2)))
      (make-type-eq-proof-trans
       :type1 (type-funn (cons type-in1 types-in1) type-out1)
       :type2 (type-fun type-in1 (type-scalar rest1))
       :type3 (type-funn (cons type-in2 types-in2) type-out2)
       :premise1-proof (make-type-eq-proof-fun2m :type-in1 type-in1
                                                 :type-in2 (car types-in1)
                                                 :types-in (cdr types-in1)
                                                 :type-out type-out1)
       :premise2-proof
       (make-type-eq-proof-trans
        :type1 (type-fun type-in1 (type-scalar rest1))
        :type2 (type-fun type-in2 (type-scalar rest2))
        :type3 (type-funn (cons type-in2 types-in2) type-out2)
        :premise1-proof
        (make-type-eq-proof-fun
         :type-in1 type-in1
         :type-in2 type-in2
         :type-out1 (type-scalar rest1)
         :type-out2 (type-scalar rest2)
         :premise1-proof premise1-proof
         :premise2-proof (make-type-eq-proof-cong-scalar
                          :type1 rest1
                          :type2 rest2
                          :premise1-proof premise2-proof))
        :premise2-proof
        (make-type-eq-proof-symm
         :type1 (type-funn (cons type-in2 types-in2) type-out2)
         :type2 (type-fun type-in2 (type-scalar rest2))
         :premise1-proof (make-type-eq-proof-fun2m :type-in1 type-in2
                                                   :type-in2 (car types-in2)
                                                   :types-in (cdr types-in2)
                                                   :type-out type-out2)))))

    ///

    (defret type-eq-proof-validp-of-type-eq-proof-cong-funn2m
      (implies (and (type-listp types-in1)
                    (type-listp types-in2)
                    (consp types-in1)
                    (consp types-in2)
                    (typep type-out1)
                    (typep type-out2)
                    (type-eq-proof-validp premise1-proof type-in1 type-in2)
                    (type-eq-proof-validp premise2-proof
                                          (type-funn types-in1 type-out1)
                                          (type-funn types-in2 type-out2)))
               (type-eq-proof-validp proof
                                     (type-funn (cons type-in1 types-in1)
                                                type-out1)
                                     (type-funn (cons type-in2 types-in2)
                                                type-out2)))
      :hints
      (("Goal"
        :expand ((type-eq-proof-validp
                  (type-eq-proof-fun
                   type-in1
                   type-in2
                   (type-scalar (type-funn types-in1 type-out1))
                   (type-scalar (type-funn types-in2 type-out2))
                   premise1-proof
                   (type-eq-proof-cong-scalar (type-funn types-in1 type-out1)
                                              (type-funn types-in2 type-out2)
                                              premise2-proof))
                  (type-fun type-in1
                            (type-scalar (type-funn types-in1 type-out1)))
                  (type-fun type-in2
                            (type-scalar (type-funn types-in2 type-out2)))))
        :in-theory (enable* type-equivalence-definition-validp-defs
                            typep-when-type-eq-proof-validp)))))

  (defruled type-eq-cong-funn2m
    (implies (and (type-listp types-in1)
                  (type-listp types-in2)
                  (consp types-in1)
                  (consp types-in2)
                  (typep type-out1)
                  (typep type-out2)
                  (type-eq type-in1 type-in2)
                  (type-eq (type-funn types-in1 type-out1)
                           (type-funn types-in2 type-out2)))
             (type-eq (type-funn (cons type-in1 types-in1) type-out1)
                      (type-funn (cons type-in2 types-in2) type-out2)))
    :use ((:instance type-eq (type1 type-in1) (type2 type-in2))
          (:instance type-eq
                     (type1 (type-funn types-in1 type-out1))
                     (type2 (type-funn types-in2 type-out2)))
          (:instance type-eq-when-proof-validp
                     (proof (type-eq-proof-cong-funn2m
                             type-in1
                             type-in2
                             types-in1
                             types-in2
                             type-out1
                             type-out2
                             (type-eq-proof type-in1 type-in2)
                             (type-eq-proof (type-funn types-in1 type-out1)
                                            (type-funn types-in2 type-out2))))
                     (concl.type1 (type-funn (cons type-in1 types-in1)
                                             type-out1))
                     (concl.type2 (type-funn (cons type-in2 types-in2)
                                             type-out2)))))

  (defmacro make-type-eq-proof-cong-funn2m (&key type-in1
                                                 type-in2
                                                 types-in1
                                                 types-in2
                                                 type-out1
                                                 type-out2
                                                 premise1-proof
                                                 premise2-proof)
    `(type-eq-proof-cong-funn2m ,type-in1 ,type-in2
                                ,types-in1 ,types-in2
                                ,type-out1 ,type-out2
                                ,premise1-proof ,premise2-proof)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection type-eq-cong-funn
  :short "Congruence of type equivalence with respect to
          all the components of n-ary function types,
          at the level of proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "The derived rules
     @(see type-eq-cong-funn-nil),
     @(see type-eq-cong-funn1), and
     @(see type-eq-cong-funn2m)
     rewrite the components of an n-ary function type one at a time.
     Here we put them together, at the level of proof trees:
     given proof trees for the pairwise equivalence of the input types
     and a proof tree for the equivalence of the output types,
     we construct a proof tree for the equivalence of
     the n-ary function types,
     by chaining instances of @('cong-funn2m') along the input types,
     ending with an instance of @('cong-funn1')
     (or with an instance of @('cong-funn-nil') if there are no input types).
     The lists of proof trees and their validity are formalized by
     @(tsee type-eq-proof-list) and @(tsee type-eq-proof-list-validp).")
   (xdoc::p
    "Since this is at the level of proof trees only,
     there is no corresponding theorem about the predicate:
     there is no predicate for the pairwise equivalence of lists of types."))

  (define type-eq-proof-cong-funn (types-in1
                                   types-in2
                                   (in-proofs type-eq-proof-listp)
                                   type-out1
                                   type-out2
                                   (out-proof type-eq-proofp))
    :returns (proof type-eq-proofp)
    :parents nil
    (cond ((or (not (consp types-in1))
               (not (consp types-in2))
               (not (consp in-proofs)))
           (make-type-eq-proof-cong-funn-nil :type-out1 type-out1
                                             :type-out2 type-out2
                                             :premise1-proof out-proof))
          ((or (not (consp (cdr types-in1)))
               (not (consp (cdr types-in2)))
               (not (consp (cdr in-proofs))))
           (make-type-eq-proof-cong-funn1 :type-in1 (car types-in1)
                                          :type-in2 (car types-in2)
                                          :type-out1 type-out1
                                          :type-out2 type-out2
                                          :premise1-proof (car in-proofs)
                                          :premise2-proof out-proof))
          (t (make-type-eq-proof-cong-funn2m
              :type-in1 (car types-in1)
              :type-in2 (car types-in2)
              :types-in1 (cdr types-in1)
              :types-in2 (cdr types-in2)
              :type-out1 type-out1
              :type-out2 type-out2
              :premise1-proof (car in-proofs)
              :premise2-proof (type-eq-proof-cong-funn (cdr types-in1)
                                                       (cdr types-in2)
                                                       (cdr in-proofs)
                                                       type-out1
                                                       type-out2
                                                       out-proof))))
    :measure (len types-in1)
    :verify-guards :after-returns

    ///

    ;; When the constructor for one input type is used,
    ;; one of the three lists is known to have exactly one element,
    ;; and the other two must be shown to have exactly one element too,
    ;; via the hypotheses on the lengths.
    ;; Expanding the lengths of the two lists of types and of their tails
    ;; provides the needed case splits on whether those lists are empty.

    (defret type-eq-proof-validp-of-type-eq-proof-cong-funn
      (implies (and (type-listp types-in1)
                    (type-listp types-in2)
                    (equal (len types-in1) (len in-proofs))
                    (equal (len types-in2) (len in-proofs))
                    (type-eq-proof-list-validp in-proofs types-in1 types-in2)
                    (type-eq-proof-validp out-proof type-out1 type-out2))
               (type-eq-proof-validp proof
                                     (type-funn types-in1 type-out1)
                                     (type-funn types-in2 type-out2)))
      :hints (("Goal"
               :induct t
               :expand ((len types-in1)
                        (len types-in2)
                        (len (cdr types-in1))
                        (len (cdr types-in2)))
               :in-theory (enable type-eq-proof-list-validp
                                  typep-when-type-eq-proof-validp
                                  len)))))

  (defmacro make-type-eq-proof-cong-funn (&key types-in1
                                               types-in2
                                               in-proofs
                                               type-out1
                                               type-out2
                                               out-proof)
    `(type-eq-proof-cong-funn ,types-in1 ,types-in2 ,in-proofs
                              ,type-out1 ,type-out2 ,out-proof)))
