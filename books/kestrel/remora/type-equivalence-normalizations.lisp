; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "type-equivalence-derived-rules")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence-normalizations
  :parents (static-semantics)
  :short "Normalizations in type equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that the normalization rules realize
     the reductions of the sugar constructs
     claimed in @(see type-equivalence-definition):
     array type variables,
     bracket types,
     n-ary function types,
     and n-ary universal, product, and sum types.
     To do that, we introduce predicates to formalize
     the absence of these constructs,
     and functions to witness the ability to perform the reductions,
     one for each kind of sugar construct, plus their composition,
     similarly to @(see ispace-equivalence-normalizations).")
   (xdoc::p
    "Unlike ispace equivalence,
     the only rules to rewrite inside the bodies of binder types
     are the alpha-conversion congruence rules,
     whose premises involve renamed bodies.
     Constructing proofs for those premises requires
     transporting proofs along variable renamings,
     which we plan to develop separately.
     For now, the predicates do not inspect the bodies of binder types,
     and the witness functions do not rewrite inside them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce noarrayvarp
  :short "Check if there are no array type variables in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :var (type-var-case type.var :atom t :array nil))
   (type :forall t)
   (type :foralln t)
   (type :pi t)
   (type :pin t)
   (type :sigma t)
   (type :sigman t))
  :name ast-noarrayvarp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nobracketp
  :short "Check if there are no bracket types in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :bracket nil)
   (type :forall t)
   (type :foralln t)
   (type :pi t)
   (type :pin t)
   (type :sigma t)
   (type :sigman t))
  :name ast-nobracketp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nofunnp
  :short "Check if there are no n-ary function types in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :funn nil)
   (type :forall t)
   (type :foralln t)
   (type :pi t)
   (type :pin t)
   (type :sigma t)
   (type :sigman t))
  :name ast-nofunnp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce noforallnp
  :short "Check if there are no n-ary universal types in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall t)
   (type :foralln nil)
   (type :pi t)
   (type :pin t)
   (type :sigma t)
   (type :sigman t))
  :name ast-noforallnp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nopinp
  :short "Check if there are no n-ary product types in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall t)
   (type :foralln t)
   (type :pi t)
   (type :pin nil)
   (type :sigma t)
   (type :sigman t))
  :name ast-nopinp)

;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce nosigmanp
  :short "Check if there are no n-ary sum types in types,
          outside the bodies of binder types."
  :types (types)
  :result booleanp
  :default t
  :combine and
  :override
  ((type :forall t)
   (type :foralln t)
   (type :pi t)
   (type :pin t)
   (type :sigma t)
   (type :sigman nil))
  :name ast-nosigmanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-noarrayvar-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without array type variables
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-noarrayvarp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-nobracket-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without bracket types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-nobracketp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-nofunn-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without n-ary function types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-nofunnp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-noforalln-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without n-ary universal types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-noforallnp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-nopin-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without n-ary product types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-nopinp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-nosigman-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to
          one without n-ary sum types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-nosigmanp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;

(define-sk type-eq-to-noarrayvar-nobracket-nonaries-p (type)
  :returns (yes/no booleanp)
  :short "Check whether a type is equivalent to one without
          array type variables,
          bracket types,
          and n-ary function, universal, product, and sum types
          outside the bodies of binder types."
  (exists (type1)
          (and (type-eq type type1)
               (type-noarrayvarp type1)
               (type-nobracketp type1)
               (type-nofunnp type1)
               (type-noforallnp type1)
               (type-nopinp type1)
               (type-nosigmanp type1)))
  :guard-hints (("Goal" :in-theory (enable typep-when-type-eq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines unsugar-array-vars-in-types
  :short "Turn types into equivalent ones
          without array type variables outside the bodies of binder types,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each array type variable is turned into
     the array type of the atom type variable and the shape variable
     with the same name, according to the rule @('array-var').
     The function on lists of types serves to rewrite
     the input types of n-ary function types.")
   (xdoc::p
    "We show that the resulting types are equivalent to the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting types have no array type variables
     outside the bodies of binder types.")
   (xdoc::p
    "We also show that these functions preserve
     the absence of bracket types,
     the absence of n-ary function types,
     and the absence of n-ary universal, product, and sum types,
     which these functions do not affect."))

  (define unsugar-array-vars-in-type ((type typep))
    :returns (mv (new-type typep)
                 (proof type-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-array-vars-in-types)
    :short "Turn a type into an equivalent one
            without array type variables outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (type-case
     type
     :var (type-var-case
           type.var
           :atom (mv (type-var type.var)
                     (type-eq-proof-refl (type-var type.var)))
           :array (b* ((name (type-var-array->name type.var))
                       (new-type (type-array
                                  (type-var (type-var-atom name))
                                  (ispace-shape (shape-var name)))))
                    (mv new-type
                        (type-eq-proof-array-var name))))
     :base (mv (type-base type.type)
               (type-eq-proof-refl (type-base type.type)))
     :array (b* (((mv new-elem proof)
                  (unsugar-array-vars-in-type type.elem)))
              (mv (type-array new-elem type.ispace)
                  (make-type-eq-proof-array
                   :type1 type.elem
                   :type2 new-elem
                   :ispace1 type.ispace
                   :ispace2 type.ispace
                   :premise1-proof proof)))
     :bracket (b* (((mv new-elem proof)
                    (unsugar-array-vars-in-type type.elem)))
                (mv (type-bracket new-elem type.ispaces)
                    (make-type-eq-proof-cong-bracket
                     :type1 type.elem
                     :type2 new-elem
                     :ispaces type.ispaces
                     :premise1-proof proof)))
     :fun (b* (((mv new-in proof-in)
                (unsugar-array-vars-in-type type.in))
               ((mv new-out proof-out)
                (unsugar-array-vars-in-type type.out)))
            (mv (type-fun new-in new-out)
                (make-type-eq-proof-fun
                 :type-in1 type.in
                 :type-in2 new-in
                 :type-out1 type.out
                 :type-out2 new-out
                 :premise1-proof proof-in
                 :premise2-proof proof-out)))
     :funn (b* (((mv new-ins proof-ins)
                 (unsugar-array-vars-in-type-list type.in))
                ((mv new-out proof-out)
                 (unsugar-array-vars-in-type type.out)))
             (mv (type-funn new-ins new-out)
                 (make-type-eq-proof-cong-funn
                  :types-in1 type.in
                  :types-in2 new-ins
                  :type-out1 type.out
                  :type-out2 new-out
                  :premise1-proof proof-ins
                  :premise2-proof proof-out)))
     :forall (mv (type-forall type.param type.body)
                 (type-eq-proof-refl (type-forall type.param type.body)))
     :foralln (mv (type-foralln type.params type.body)
                  (type-eq-proof-refl (type-foralln type.params type.body)))
     :pi (mv (type-pi type.param type.body)
             (type-eq-proof-refl (type-pi type.param type.body)))
     :pin (mv (type-pin type.params type.body)
              (type-eq-proof-refl (type-pin type.params type.body)))
     :sigma (mv (type-sigma type.param type.body)
                (type-eq-proof-refl (type-sigma type.param type.body)))
     :sigman (mv (type-sigman type.params type.body)
                 (type-eq-proof-refl (type-sigman type.params type.body))))
    :measure (type-count type))

  (define unsugar-array-vars-in-type-list ((types type-listp))
    :returns (mv (new-types type-listp)
                 (proof types-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-array-vars-in-types)
    :short "Turn a list of types into an equivalent one
            without array type variables outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp types)) (mv nil (types-eq-proof-refl nil)))
         ((mv new-type proof1) (unsugar-array-vars-in-type (car types)))
         ((mv new-types proof2)
          (unsugar-array-vars-in-type-list (cdr types))))
      (mv (cons new-type new-types)
          (make-types-eq-proof-cong-cons
           :type1 (type-fix (car types))
           :type2 new-type
           :types1 (type-list-fix (cdr types))
           :types2 new-types
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (type-list-count types)

    ///

    (defret len-of-unsugar-array-vars-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable (:induction len))))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unsugar-array-vars-in-types)

  (defret-mutual type-eq-proof-validp-of-unsugar-array-vars-in-types
    (defret type-eq-proof-validp-of-unsugar-array-vars-in-type
      (implies (typep type)
               (type-eq-proof-validp proof type new-type))
      :fn unsugar-array-vars-in-type)
    (defret types-eq-proof-validp-of-unsugar-array-vars-in-type-list
      (implies (type-listp types)
               (types-eq-proof-validp proof types new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable type-eq-proof-validp
                                types-eq-proof-validp
                                type-eq-refl-validp
                                types-eq-refl-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-array-var-validp
                                types-eq-cong-cons-validp
                                ispace-eq-refl))))

  (defret-mutual type-noarrayvarp-of-unsugar-array-vars-in-types
    (defret type-noarrayvarp-of-unsugar-array-vars-in-type
      (type-noarrayvarp new-type)
      :fn unsugar-array-vars-in-type)
    (defret type-list-noarrayvarp-of-unsugar-array-vars-in-type-list
      (type-list-noarrayvarp new-types)
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noarrayvarp-rules))
            '(:expand ((type-noarrayvarp type)
                       (:free (v) (type-noarrayvarp (type-var v)))
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret-mutual type-nobracketp-of-unsugar-array-vars-in-types
    (defret type-nobracketp-of-unsugar-array-vars-in-type
      (implies (type-nobracketp type)
               (type-nobracketp new-type))
      :fn unsugar-array-vars-in-type)
    (defret type-list-nobracketp-of-unsugar-array-vars-in-type-list
      (implies (type-list-nobracketp types)
               (type-list-nobracketp new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nobracketp-rules))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret-mutual type-nofunnp-of-unsugar-array-vars-in-types
    (defret type-nofunnp-of-unsugar-array-vars-in-type
      (implies (type-nofunnp type)
               (type-nofunnp new-type))
      :fn unsugar-array-vars-in-type)
    (defret type-list-nofunnp-of-unsugar-array-vars-in-type-list
      (implies (type-list-nofunnp types)
               (type-list-nofunnp new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nofunnp-rules))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret-mutual type-noforallnp-of-unsugar-array-vars-in-types
    (defret type-noforallnp-of-unsugar-array-vars-in-type
      (implies (type-noforallnp type)
               (type-noforallnp new-type))
      :fn unsugar-array-vars-in-type)
    (defret type-list-noforallnp-of-unsugar-array-vars-in-type-list
      (implies (type-list-noforallnp types)
               (type-list-noforallnp new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noforallnp-rules))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret-mutual type-nopinp-of-unsugar-array-vars-in-types
    (defret type-nopinp-of-unsugar-array-vars-in-type
      (implies (type-nopinp type)
               (type-nopinp new-type))
      :fn unsugar-array-vars-in-type)
    (defret type-list-nopinp-of-unsugar-array-vars-in-type-list
      (implies (type-list-nopinp types)
               (type-list-nopinp new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nopinp-rules))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b)))))))

  (defret-mutual type-nosigmanp-of-unsugar-array-vars-in-types
    (defret type-nosigmanp-of-unsugar-array-vars-in-type
      (implies (type-nosigmanp type)
               (type-nosigmanp new-type))
      :fn unsugar-array-vars-in-type)
    (defret type-list-nosigmanp-of-unsugar-array-vars-in-type-list
      (implies (type-list-nosigmanp types)
               (type-list-nosigmanp new-types))
      :fn unsugar-array-vars-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosigmanp-rules))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines unsugar-brackets-in-types
  :short "Turn types into equivalent ones
          without bracket types outside the bodies of binder types,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each bracket type is turned into
     the array type of the same element type
     and of the splice of the ispaces of the bracket type,
     according to the rule @('bracket');
     the element type is rewritten first,
     via the congruence rule @('array'),
     with the two steps chained via the rule @('trans').
     The function on lists of types serves to rewrite
     the input types of n-ary function types.")
   (xdoc::p
    "We show that the resulting types are equivalent to the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting types have no bracket types
     outside the bodies of binder types.")
   (xdoc::p
    "We also show that these functions preserve
     the absence of array type variables,
     the absence of n-ary function types,
     and the absence of n-ary universal, product, and sum types,
     which these functions do not affect."))

  (define unsugar-brackets-in-type ((type typep))
    :returns (mv (new-type typep)
                 (proof type-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-brackets-in-types)
    :short "Turn a type into an equivalent one
            without bracket types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (type-case
     type
     :var (mv (type-var type.var)
              (type-eq-proof-refl (type-var type.var)))
     :base (mv (type-base type.type)
               (type-eq-proof-refl (type-base type.type)))
     :array (b* (((mv new-elem proof)
                  (unsugar-brackets-in-type type.elem)))
              (mv (type-array new-elem type.ispace)
                  (make-type-eq-proof-array
                   :type1 type.elem
                   :type2 new-elem
                   :ispace1 type.ispace
                   :ispace2 type.ispace
                   :premise1-proof proof)))
     :bracket (b* ((ispace (ispace-shape (shape-splice type.ispaces)))
                   ((mv new-elem proof)
                    (unsugar-brackets-in-type type.elem))
                   (mid-type (type-array type.elem ispace))
                   (new-type (type-array new-elem ispace)))
                (mv new-type
                    (make-type-eq-proof-trans
                     :type1 (type-bracket type.elem type.ispaces)
                     :type2 mid-type
                     :type3 new-type
                     :premise1-proof (make-type-eq-proof-bracket
                                      :type type.elem
                                      :ispaces type.ispaces
                                      :ispace ispace)
                     :premise2-proof (make-type-eq-proof-array
                                      :type1 type.elem
                                      :type2 new-elem
                                      :ispace1 ispace
                                      :ispace2 ispace
                                      :premise1-proof proof))))
     :fun (b* (((mv new-in proof-in)
                (unsugar-brackets-in-type type.in))
               ((mv new-out proof-out)
                (unsugar-brackets-in-type type.out)))
            (mv (type-fun new-in new-out)
                (make-type-eq-proof-fun
                 :type-in1 type.in
                 :type-in2 new-in
                 :type-out1 type.out
                 :type-out2 new-out
                 :premise1-proof proof-in
                 :premise2-proof proof-out)))
     :funn (b* (((mv new-ins proof-ins)
                 (unsugar-brackets-in-type-list type.in))
                ((mv new-out proof-out)
                 (unsugar-brackets-in-type type.out)))
             (mv (type-funn new-ins new-out)
                 (make-type-eq-proof-cong-funn
                  :types-in1 type.in
                  :types-in2 new-ins
                  :type-out1 type.out
                  :type-out2 new-out
                  :premise1-proof proof-ins
                  :premise2-proof proof-out)))
     :forall (mv (type-forall type.param type.body)
                 (type-eq-proof-refl (type-forall type.param type.body)))
     :foralln (mv (type-foralln type.params type.body)
                  (type-eq-proof-refl (type-foralln type.params type.body)))
     :pi (mv (type-pi type.param type.body)
             (type-eq-proof-refl (type-pi type.param type.body)))
     :pin (mv (type-pin type.params type.body)
              (type-eq-proof-refl (type-pin type.params type.body)))
     :sigma (mv (type-sigma type.param type.body)
                (type-eq-proof-refl (type-sigma type.param type.body)))
     :sigman (mv (type-sigman type.params type.body)
                 (type-eq-proof-refl (type-sigman type.params type.body))))
    :measure (type-count type))

  (define unsugar-brackets-in-type-list ((types type-listp))
    :returns (mv (new-types type-listp)
                 (proof types-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-brackets-in-types)
    :short "Turn a list of types into an equivalent one
            without bracket types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp types)) (mv nil (types-eq-proof-refl nil)))
         ((mv new-type proof1) (unsugar-brackets-in-type (car types)))
         ((mv new-types proof2) (unsugar-brackets-in-type-list (cdr types))))
      (mv (cons new-type new-types)
          (make-types-eq-proof-cong-cons
           :type1 (type-fix (car types))
           :type2 new-type
           :types1 (type-list-fix (cdr types))
           :types2 new-types
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (type-list-count types)

    ///

    (defret len-of-unsugar-brackets-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable (:induction len))))))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual unsugar-brackets-in-types)

  (defret-mutual type-eq-proof-validp-of-unsugar-brackets-in-types
    (defret type-eq-proof-validp-of-unsugar-brackets-in-type
      (implies (typep type)
               (type-eq-proof-validp proof type new-type))
      :fn unsugar-brackets-in-type)
    (defret types-eq-proof-validp-of-unsugar-brackets-in-type-list
      (implies (type-listp types)
               (types-eq-proof-validp proof types new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable type-eq-proof-validp
                                types-eq-proof-validp
                                type-eq-refl-validp
                                types-eq-refl-validp
                                type-eq-trans-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-bracket-validp
                                types-eq-cong-cons-validp
                                ispace-eq-refl))))

  (defret-mutual type-nobracketp-of-unsugar-brackets-in-types
    (defret type-nobracketp-of-unsugar-brackets-in-type
      (type-nobracketp new-type)
      :fn unsugar-brackets-in-type)
    (defret type-list-nobracketp-of-unsugar-brackets-in-type-list
      (type-list-nobracketp new-types)
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nobracketp-rules))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret-mutual type-noarrayvarp-of-unsugar-brackets-in-types
    (defret type-noarrayvarp-of-unsugar-brackets-in-type
      (implies (type-noarrayvarp type)
               (type-noarrayvarp new-type))
      :fn unsugar-brackets-in-type)
    (defret type-list-noarrayvarp-of-unsugar-brackets-in-type-list
      (implies (type-list-noarrayvarp types)
               (type-list-noarrayvarp new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noarrayvarp-rules))
            '(:expand ((type-noarrayvarp type)
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret-mutual type-nofunnp-of-unsugar-brackets-in-types
    (defret type-nofunnp-of-unsugar-brackets-in-type
      (implies (type-nofunnp type)
               (type-nofunnp new-type))
      :fn unsugar-brackets-in-type)
    (defret type-list-nofunnp-of-unsugar-brackets-in-type-list
      (implies (type-list-nofunnp types)
               (type-list-nofunnp new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nofunnp-rules))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret-mutual type-noforallnp-of-unsugar-brackets-in-types
    (defret type-noforallnp-of-unsugar-brackets-in-type
      (implies (type-noforallnp type)
               (type-noforallnp new-type))
      :fn unsugar-brackets-in-type)
    (defret type-list-noforallnp-of-unsugar-brackets-in-type-list
      (implies (type-list-noforallnp types)
               (type-list-noforallnp new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noforallnp-rules))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret-mutual type-nopinp-of-unsugar-brackets-in-types
    (defret type-nopinp-of-unsugar-brackets-in-type
      (implies (type-nopinp type)
               (type-nopinp new-type))
      :fn unsugar-brackets-in-type)
    (defret type-list-nopinp-of-unsugar-brackets-in-type-list
      (implies (type-list-nopinp types)
               (type-list-nopinp new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nopinp-rules))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b)))))))

  (defret-mutual type-nosigmanp-of-unsugar-brackets-in-types
    (defret type-nosigmanp-of-unsugar-brackets-in-type
      (implies (type-nosigmanp type)
               (type-nosigmanp new-type))
      :fn unsugar-brackets-in-type)
    (defret type-list-nosigmanp-of-unsugar-brackets-in-type-list
      (implies (type-list-nosigmanp types)
               (type-list-nosigmanp new-types))
      :fn unsugar-brackets-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosigmanp-rules))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unsugar-nary-funs-in-type ((type typep))
  :returns (mv (new-type typep)
               (proof type-eq-proofp))
  :short "Turn a type into an equivalent one
          without n-ary function types outside the bodies of binder types,
          and construct a proof tree demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each n-ary function type is turned into
     a nesting of unary function types:
     a nullary function type is turned into its output type,
     according to the rule @('fun0');
     a function type with exactly one input is turned into
     the unary function type with that input and the same output,
     according to the rule @('fun1');
     and a function type with two or more inputs is turned into
     a unary function type from the first input
     to the scalar array type of
     the function type with the remaining inputs,
     according to the rule @('fun2m').
     The components of the resulting unary function type
     are rewritten via the congruence rule @('fun')
     (the scalar array type via @(tsee type-eq-cong-scalar)),
     with the two steps chained via the rule @('trans').
     Since the function type with the remaining inputs
     is a constructed n-ary function type,
     the recursion on it needs an explicit measure argument.
     Because this function eliminates n-ary function types,
     it does not need to rewrite inside them,
     and thus, unlike the other normalization functions,
     it has no companion function on lists of types.")
   (xdoc::p
    "We show that the resulting type is equivalent to the argument one.
     This is done via the constructed proof tree.")
   (xdoc::p
    "We show that the resulting type has no n-ary function types
     outside the bodies of binder types.")
   (xdoc::p
    "We also show that this function preserves
     the absence of array type variables,
     the absence of bracket types,
     and the absence of n-ary universal, product, and sum types,
     which this function does not affect.")
   (xdoc::p
    "We also show that this function preserves the kind of the type.
     This is needed to verify the guards of this function,
     because the scalar array types built by this function
     require the element types to have the atom kind;
     thus, guard verification is deferred until after that theorem."))
  (type-case
   type
   :var (mv (type-var type.var)
            (type-eq-proof-refl (type-var type.var)))
   :base (mv (type-base type.type)
             (type-eq-proof-refl (type-base type.type)))
   :array (b* (((mv new-elem proof) (unsugar-nary-funs-in-type type.elem)))
            (mv (type-array new-elem type.ispace)
                (make-type-eq-proof-array
                 :type1 type.elem
                 :type2 new-elem
                 :ispace1 type.ispace
                 :ispace2 type.ispace
                 :premise1-proof proof)))
   :bracket (b* (((mv new-elem proof) (unsugar-nary-funs-in-type type.elem)))
              (mv (type-bracket new-elem type.ispaces)
                  (make-type-eq-proof-cong-bracket
                   :type1 type.elem
                   :type2 new-elem
                   :ispaces type.ispaces
                   :premise1-proof proof)))
   :fun (b* (((mv new-in proof-in) (unsugar-nary-funs-in-type type.in))
             ((mv new-out proof-out) (unsugar-nary-funs-in-type type.out)))
          (mv (type-fun new-in new-out)
              (make-type-eq-proof-fun
               :type-in1 type.in
               :type-in2 new-in
               :type-out1 type.out
               :type-out2 new-out
               :premise1-proof proof-in
               :premise2-proof proof-out)))
   :funn
   (b* (((when (endp type.in))
         (b* (((mv new-out proof-out) (unsugar-nary-funs-in-type type.out)))
           (mv new-out
               (make-type-eq-proof-trans
                :type1 (type-funn nil type.out)
                :type2 type.out
                :type3 new-out
                :premise1-proof (type-eq-proof-fun0 type.out)
                :premise2-proof proof-out))))
        (type-in (car type.in))
        ((mv new-in proof-in) (unsugar-nary-funs-in-type type-in))
        ((when (endp (cdr type.in)))
         (b* (((mv new-out proof-out) (unsugar-nary-funs-in-type type.out))
              (mid-type (type-fun type-in type.out))
              (new-type (type-fun new-in new-out)))
           (mv new-type
               (make-type-eq-proof-trans
                :type1 (type-funn type.in type.out)
                :type2 mid-type
                :type3 new-type
                :premise1-proof (make-type-eq-proof-fun1
                                 :type-in type-in
                                 :type-out type.out)
                :premise2-proof (make-type-eq-proof-fun
                                 :type-in1 type-in
                                 :type-in2 new-in
                                 :type-out1 type.out
                                 :type-out2 new-out
                                 :premise1-proof proof-in
                                 :premise2-proof proof-out)))))
        (rest-type (type-funn (cdr type.in) type.out))
        ((mv new-rest proof-rest) (unsugar-nary-funs-in-type rest-type))
        (mid-type (type-fun type-in (type-scalar rest-type)))
        (new-type (type-fun new-in (type-scalar new-rest))))
     (mv new-type
         (make-type-eq-proof-trans
          :type1 (type-funn type.in type.out)
          :type2 mid-type
          :type3 new-type
          :premise1-proof (make-type-eq-proof-fun2m
                           :type-in1 type-in
                           :type-in2 (cadr type.in)
                           :types-in (cddr type.in)
                           :type-out type.out)
          :premise2-proof (make-type-eq-proof-fun
                           :type-in1 type-in
                           :type-in2 new-in
                           :type-out1 (type-scalar rest-type)
                           :type-out2 (type-scalar new-rest)
                           :premise1-proof proof-in
                           :premise2-proof (make-type-eq-proof-cong-scalar
                                            :type1 rest-type
                                            :type2 new-rest
                                            :premise1-proof proof-rest)))))
   :forall (mv (type-forall type.param type.body)
               (type-eq-proof-refl (type-forall type.param type.body)))
   :foralln (mv (type-foralln type.params type.body)
                (type-eq-proof-refl (type-foralln type.params type.body)))
   :pi (mv (type-pi type.param type.body)
           (type-eq-proof-refl (type-pi type.param type.body)))
   :pin (mv (type-pin type.params type.body)
            (type-eq-proof-refl (type-pin type.params type.body)))
   :sigma (mv (type-sigma type.param type.body)
              (type-eq-proof-refl (type-sigma type.param type.body)))
   :sigman (mv (type-sigman type.params type.body)
               (type-eq-proof-refl (type-sigman type.params type.body))))
  :measure (type-count type)
  :hints (("Goal"
           :expand ((type-count type)
                    (type-count (type-funn (cdr (type-funn->in type))
                                           (type-funn->out type)))
                    (type-list-count (type-funn->in type)))))
  :verify-guards nil

  ///

  (defret type-eq-proof-validp-of-unsugar-nary-funs-in-type
    (implies (typep type)
             (type-eq-proof-validp proof type new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable type-eq-proof-validp
                                type-eq-refl-validp
                                type-eq-trans-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-fun0-validp
                                type-eq-fun1-validp
                                type-eq-fun2m-validp
                                ispace-eq-refl))))

  (defret type-atom-kindp-of-unsugar-nary-funs-in-type
    (equal (type-atom-kindp new-type)
           (type-atom-kindp type))
    :hints (("Goal"
             :induct t
             :expand ((type-atom-kindp type)))))

  (verify-guards unsugar-nary-funs-in-type)

  (defret type-nofunnp-of-unsugar-nary-funs-in-type
    (type-nofunnp new-type)
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nofunnp-rules type-scalar))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret type-noarrayvarp-of-unsugar-nary-funs-in-type
    (implies (type-noarrayvarp type)
             (type-noarrayvarp new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-noarrayvarp-rules type-scalar))
            '(:expand ((type-noarrayvarp type)
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret type-nobracketp-of-unsugar-nary-funs-in-type
    (implies (type-nobracketp type)
             (type-nobracketp new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nobracketp-rules type-scalar))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret type-noforallnp-of-unsugar-nary-funs-in-type
    (implies (type-noforallnp type)
             (type-noforallnp new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-noforallnp-rules type-scalar))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret type-nopinp-of-unsugar-nary-funs-in-type
    (implies (type-nopinp type)
             (type-nopinp new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nopinp-rules type-scalar))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b)))))))

  (defret type-nosigmanp-of-unsugar-nary-funs-in-type
    (implies (type-nosigmanp type)
             (type-nosigmanp new-type))
    :hints (("Goal"
             :induct t
             :in-theory (enable* ast-nosigmanp-rules type-scalar))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines unsugar-nary-foralls-in-types
  :short "Turn types into equivalent ones
          without n-ary universal types outside the bodies of binder types,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each n-ary universal type is turned into
     a unary universal type of the first parameter
     whose body is the scalar array type of
     either the unary universal type of the second parameter
     (rule @('forall2'))
     or the n-ary universal type of the remaining parameters
     (rule @('forall3m')).
     Since the resulting universal type is a binder type,
     its body is not rewritten.
     The function on lists of types serves to rewrite
     the input types of n-ary function types.")
   (xdoc::p
    "We show that the resulting types are equivalent to the argument ones.
     This is done via the constructed proof trees.")
   (xdoc::p
    "We show that the resulting types have no n-ary universal types
     outside the bodies of binder types.")
   (xdoc::p
    "We also show that these functions preserve
     the absence of array type variables,
     the absence of bracket types,
     the absence of n-ary function types,
     and the absence of n-ary product and sum types,
     which these functions do not affect."))

  (define unsugar-nary-foralls-in-type ((type typep))
    :returns (mv (new-type typep)
                 (proof type-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-foralls-in-types)
    :short "Turn a type into an equivalent one
            without n-ary universal types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (type-case
     type
     :var (mv (type-var type.var)
              (type-eq-proof-refl (type-var type.var)))
     :base (mv (type-base type.type)
               (type-eq-proof-refl (type-base type.type)))
     :array (b* (((mv new-elem proof)
                  (unsugar-nary-foralls-in-type type.elem)))
              (mv (type-array new-elem type.ispace)
                  (make-type-eq-proof-array
                   :type1 type.elem
                   :type2 new-elem
                   :ispace1 type.ispace
                   :ispace2 type.ispace
                   :premise1-proof proof)))
     :bracket (b* (((mv new-elem proof)
                    (unsugar-nary-foralls-in-type type.elem)))
                (mv (type-bracket new-elem type.ispaces)
                    (make-type-eq-proof-cong-bracket
                     :type1 type.elem
                     :type2 new-elem
                     :ispaces type.ispaces
                     :premise1-proof proof)))
     :fun (b* (((mv new-in proof-in)
                (unsugar-nary-foralls-in-type type.in))
               ((mv new-out proof-out)
                (unsugar-nary-foralls-in-type type.out)))
            (mv (type-fun new-in new-out)
                (make-type-eq-proof-fun
                 :type-in1 type.in
                 :type-in2 new-in
                 :type-out1 type.out
                 :type-out2 new-out
                 :premise1-proof proof-in
                 :premise2-proof proof-out)))
     :funn (b* (((mv new-ins proof-ins)
                 (unsugar-nary-foralls-in-type-list type.in))
                ((mv new-out proof-out)
                 (unsugar-nary-foralls-in-type type.out)))
             (mv (type-funn new-ins new-out)
                 (make-type-eq-proof-cong-funn
                  :types-in1 type.in
                  :types-in2 new-ins
                  :type-out1 type.out
                  :type-out2 new-out
                  :premise1-proof proof-ins
                  :premise2-proof proof-out)))
     :forall (mv (type-forall type.param type.body)
                 (type-eq-proof-refl (type-forall type.param type.body)))
     :foralln (b* ((param1 (car type.params))
                   (param2 (cadr type.params))
                   (params (cddr type.params)))
                (if (endp params)
                    (mv (type-forall param1
                                     (type-scalar
                                      (type-forall param2 type.body)))
                        (make-type-eq-proof-forall2
                         :param1 param1
                         :param2 param2
                         :type type.body))
                  (mv (type-forall
                       param1
                       (type-scalar
                        (type-foralln (cons param2 params) type.body)))
                      (make-type-eq-proof-forall3m
                       :param1 param1
                       :param2 param2
                       :params params
                       :type type.body))))
     :pi (mv (type-pi type.param type.body)
             (type-eq-proof-refl (type-pi type.param type.body)))
     :pin (mv (type-pin type.params type.body)
              (type-eq-proof-refl (type-pin type.params type.body)))
     :sigma (mv (type-sigma type.param type.body)
                (type-eq-proof-refl (type-sigma type.param type.body)))
     :sigman (mv (type-sigman type.params type.body)
                 (type-eq-proof-refl (type-sigman type.params type.body))))
    :measure (type-count type))

  (define unsugar-nary-foralls-in-type-list ((types type-listp))
    :returns (mv (new-types type-listp)
                 (proof types-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-foralls-in-types)
    :short "Turn a list of types into an equivalent one
            without n-ary universal types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp types)) (mv nil (types-eq-proof-refl nil)))
         ((mv new-type proof1) (unsugar-nary-foralls-in-type (car types)))
         ((mv new-types proof2)
          (unsugar-nary-foralls-in-type-list (cdr types))))
      (mv (cons new-type new-types)
          (make-types-eq-proof-cong-cons
           :type1 (type-fix (car types))
           :type2 new-type
           :types1 (type-list-fix (cdr types))
           :types2 new-types
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (type-list-count types)

    ///

    (defret len-of-unsugar-nary-foralls-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable (:induction len))))))

  :verify-guards :after-returns
  :guard-hints (("Goal"
                 :in-theory (enable consp-of-cdr-of-type-foralln->params)))

  ///

  (fty::deffixequiv-mutual unsugar-nary-foralls-in-types)

  (defret-mutual type-eq-proof-validp-of-unsugar-nary-foralls-in-types
    (defret type-eq-proof-validp-of-unsugar-nary-foralls-in-type
      (implies (typep type)
               (type-eq-proof-validp proof type new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret types-eq-proof-validp-of-unsugar-nary-foralls-in-type-list
      (implies (type-listp types)
               (types-eq-proof-validp proof types new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable type-eq-proof-validp
                                types-eq-proof-validp
                                type-eq-refl-validp
                                types-eq-refl-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-forall2-validp
                                type-eq-forall3m-validp
                                types-eq-cong-cons-validp
                                ispace-eq-refl
                                consp-of-cdr-of-type-foralln->params))))

  (defret-mutual type-noforallnp-of-unsugar-nary-foralls-in-types
    (defret type-noforallnp-of-unsugar-nary-foralls-in-type
      (type-noforallnp new-type)
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-noforallnp-of-unsugar-nary-foralls-in-type-list
      (type-list-noforallnp new-types)
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noforallnp-rules))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret-mutual type-noarrayvarp-of-unsugar-nary-foralls-in-types
    (defret type-noarrayvarp-of-unsugar-nary-foralls-in-type
      (implies (type-noarrayvarp type)
               (type-noarrayvarp new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-noarrayvarp-of-unsugar-nary-foralls-in-type-list
      (implies (type-list-noarrayvarp types)
               (type-list-noarrayvarp new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noarrayvarp-rules))
            '(:expand ((type-noarrayvarp type)
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret-mutual type-nobracketp-of-unsugar-nary-foralls-in-types
    (defret type-nobracketp-of-unsugar-nary-foralls-in-type
      (implies (type-nobracketp type)
               (type-nobracketp new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-nobracketp-of-unsugar-nary-foralls-in-type-list
      (implies (type-list-nobracketp types)
               (type-list-nobracketp new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nobracketp-rules))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret-mutual type-nofunnp-of-unsugar-nary-foralls-in-types
    (defret type-nofunnp-of-unsugar-nary-foralls-in-type
      (implies (type-nofunnp type)
               (type-nofunnp new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-nofunnp-of-unsugar-nary-foralls-in-type-list
      (implies (type-list-nofunnp types)
               (type-list-nofunnp new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nofunnp-rules))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret-mutual type-nopinp-of-unsugar-nary-foralls-in-types
    (defret type-nopinp-of-unsugar-nary-foralls-in-type
      (implies (type-nopinp type)
               (type-nopinp new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-nopinp-of-unsugar-nary-foralls-in-type-list
      (implies (type-list-nopinp types)
               (type-list-nopinp new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nopinp-rules))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b)))))))

  (defret-mutual type-nosigmanp-of-unsugar-nary-foralls-in-types
    (defret type-nosigmanp-of-unsugar-nary-foralls-in-type
      (implies (type-nosigmanp type)
               (type-nosigmanp new-type))
      :fn unsugar-nary-foralls-in-type)
    (defret type-list-nosigmanp-of-unsugar-nary-foralls-in-type-list
      (implies (type-list-nosigmanp types)
               (type-list-nosigmanp new-types))
      :fn unsugar-nary-foralls-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosigmanp-rules))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines unsugar-nary-pis-in-types
  :short "Turn types into equivalent ones
          without n-ary product types outside the bodies of binder types,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see unsugar-nary-foralls-in-types),
     with the rules @('pi2') and @('pi3m')."))

  (define unsugar-nary-pis-in-type ((type typep))
    :returns (mv (new-type typep)
                 (proof type-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-pis-in-types)
    :short "Turn a type into an equivalent one
            without n-ary product types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (type-case
     type
     :var (mv (type-var type.var)
              (type-eq-proof-refl (type-var type.var)))
     :base (mv (type-base type.type)
               (type-eq-proof-refl (type-base type.type)))
     :array (b* (((mv new-elem proof) (unsugar-nary-pis-in-type type.elem)))
              (mv (type-array new-elem type.ispace)
                  (make-type-eq-proof-array
                   :type1 type.elem
                   :type2 new-elem
                   :ispace1 type.ispace
                   :ispace2 type.ispace
                   :premise1-proof proof)))
     :bracket (b* (((mv new-elem proof)
                    (unsugar-nary-pis-in-type type.elem)))
                (mv (type-bracket new-elem type.ispaces)
                    (make-type-eq-proof-cong-bracket
                     :type1 type.elem
                     :type2 new-elem
                     :ispaces type.ispaces
                     :premise1-proof proof)))
     :fun (b* (((mv new-in proof-in) (unsugar-nary-pis-in-type type.in))
               ((mv new-out proof-out) (unsugar-nary-pis-in-type type.out)))
            (mv (type-fun new-in new-out)
                (make-type-eq-proof-fun
                 :type-in1 type.in
                 :type-in2 new-in
                 :type-out1 type.out
                 :type-out2 new-out
                 :premise1-proof proof-in
                 :premise2-proof proof-out)))
     :funn (b* (((mv new-ins proof-ins)
                 (unsugar-nary-pis-in-type-list type.in))
                ((mv new-out proof-out)
                 (unsugar-nary-pis-in-type type.out)))
             (mv (type-funn new-ins new-out)
                 (make-type-eq-proof-cong-funn
                  :types-in1 type.in
                  :types-in2 new-ins
                  :type-out1 type.out
                  :type-out2 new-out
                  :premise1-proof proof-ins
                  :premise2-proof proof-out)))
     :forall (mv (type-forall type.param type.body)
                 (type-eq-proof-refl (type-forall type.param type.body)))
     :foralln (mv (type-foralln type.params type.body)
                  (type-eq-proof-refl (type-foralln type.params type.body)))
     :pi (mv (type-pi type.param type.body)
             (type-eq-proof-refl (type-pi type.param type.body)))
     :pin (b* ((param1 (car type.params))
               (param2 (cadr type.params))
               (params (cddr type.params)))
            (if (endp params)
                (mv (type-pi param1
                             (type-scalar (type-pi param2 type.body)))
                    (make-type-eq-proof-pi2
                     :param1 param1
                     :param2 param2
                     :type type.body))
              (mv (type-pi param1
                           (type-scalar
                            (type-pin (cons param2 params) type.body)))
                  (make-type-eq-proof-pi3m
                   :param1 param1
                   :param2 param2
                   :params params
                   :type type.body))))
     :sigma (mv (type-sigma type.param type.body)
                (type-eq-proof-refl (type-sigma type.param type.body)))
     :sigman (mv (type-sigman type.params type.body)
                 (type-eq-proof-refl (type-sigman type.params type.body))))
    :measure (type-count type))

  (define unsugar-nary-pis-in-type-list ((types type-listp))
    :returns (mv (new-types type-listp)
                 (proof types-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-pis-in-types)
    :short "Turn a list of types into an equivalent one
            without n-ary product types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp types)) (mv nil (types-eq-proof-refl nil)))
         ((mv new-type proof1) (unsugar-nary-pis-in-type (car types)))
         ((mv new-types proof2) (unsugar-nary-pis-in-type-list (cdr types))))
      (mv (cons new-type new-types)
          (make-types-eq-proof-cong-cons
           :type1 (type-fix (car types))
           :type2 new-type
           :types1 (type-list-fix (cdr types))
           :types2 new-types
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (type-list-count types)

    ///

    (defret len-of-unsugar-nary-pis-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable (:induction len))))))

  :verify-guards :after-returns
  :guard-hints (("Goal"
                 :in-theory (enable consp-of-cdr-of-type-pin->params)))

  ///

  (fty::deffixequiv-mutual unsugar-nary-pis-in-types)

  (defret-mutual type-eq-proof-validp-of-unsugar-nary-pis-in-types
    (defret type-eq-proof-validp-of-unsugar-nary-pis-in-type
      (implies (typep type)
               (type-eq-proof-validp proof type new-type))
      :fn unsugar-nary-pis-in-type)
    (defret types-eq-proof-validp-of-unsugar-nary-pis-in-type-list
      (implies (type-listp types)
               (types-eq-proof-validp proof types new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable type-eq-proof-validp
                                types-eq-proof-validp
                                type-eq-refl-validp
                                types-eq-refl-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-pi2-validp
                                type-eq-pi3m-validp
                                types-eq-cong-cons-validp
                                ispace-eq-refl
                                consp-of-cdr-of-type-pin->params))))

  (defret-mutual type-nopinp-of-unsugar-nary-pis-in-types
    (defret type-nopinp-of-unsugar-nary-pis-in-type
      (type-nopinp new-type)
      :fn unsugar-nary-pis-in-type)
    (defret type-list-nopinp-of-unsugar-nary-pis-in-type-list
      (type-list-nopinp new-types)
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nopinp-rules))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b)))))))

  (defret-mutual type-noarrayvarp-of-unsugar-nary-pis-in-types
    (defret type-noarrayvarp-of-unsugar-nary-pis-in-type
      (implies (type-noarrayvarp type)
               (type-noarrayvarp new-type))
      :fn unsugar-nary-pis-in-type)
    (defret type-list-noarrayvarp-of-unsugar-nary-pis-in-type-list
      (implies (type-list-noarrayvarp types)
               (type-list-noarrayvarp new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noarrayvarp-rules))
            '(:expand ((type-noarrayvarp type)
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret-mutual type-nobracketp-of-unsugar-nary-pis-in-types
    (defret type-nobracketp-of-unsugar-nary-pis-in-type
      (implies (type-nobracketp type)
               (type-nobracketp new-type))
      :fn unsugar-nary-pis-in-type)
    (defret type-list-nobracketp-of-unsugar-nary-pis-in-type-list
      (implies (type-list-nobracketp types)
               (type-list-nobracketp new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nobracketp-rules))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret-mutual type-nofunnp-of-unsugar-nary-pis-in-types
    (defret type-nofunnp-of-unsugar-nary-pis-in-type
      (implies (type-nofunnp type)
               (type-nofunnp new-type))
      :fn unsugar-nary-pis-in-type)
    (defret type-list-nofunnp-of-unsugar-nary-pis-in-type-list
      (implies (type-list-nofunnp types)
               (type-list-nofunnp new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nofunnp-rules))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret-mutual type-noforallnp-of-unsugar-nary-pis-in-types
    (defret type-noforallnp-of-unsugar-nary-pis-in-type
      (implies (type-noforallnp type)
               (type-noforallnp new-type))
      :fn unsugar-nary-pis-in-type)
    (defret type-list-noforallnp-of-unsugar-nary-pis-in-type-list
      (implies (type-list-noforallnp types)
               (type-list-noforallnp new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noforallnp-rules))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret-mutual type-nosigmanp-of-unsugar-nary-pis-in-types
    (defret type-nosigmanp-of-unsugar-nary-pis-in-type
      (implies (type-nosigmanp type)
               (type-nosigmanp new-type))
      :fn unsugar-nary-pis-in-type)
    (defret type-list-nosigmanp-of-unsugar-nary-pis-in-type-list
      (implies (type-list-nosigmanp types)
               (type-list-nosigmanp new-types))
      :fn unsugar-nary-pis-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosigmanp-rules))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines unsugar-nary-sigmas-in-types
  :short "Turn types into equivalent ones
          without n-ary sum types outside the bodies of binder types,
          and construct proof trees demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(see unsugar-nary-foralls-in-types),
     with the rules @('sigma2') and @('sigma3m')."))

  (define unsugar-nary-sigmas-in-type ((type typep))
    :returns (mv (new-type typep)
                 (proof type-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-sigmas-in-types)
    :short "Turn a type into an equivalent one
            without n-ary sum types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (type-case
     type
     :var (mv (type-var type.var)
              (type-eq-proof-refl (type-var type.var)))
     :base (mv (type-base type.type)
               (type-eq-proof-refl (type-base type.type)))
     :array (b* (((mv new-elem proof)
                  (unsugar-nary-sigmas-in-type type.elem)))
              (mv (type-array new-elem type.ispace)
                  (make-type-eq-proof-array
                   :type1 type.elem
                   :type2 new-elem
                   :ispace1 type.ispace
                   :ispace2 type.ispace
                   :premise1-proof proof)))
     :bracket (b* (((mv new-elem proof)
                    (unsugar-nary-sigmas-in-type type.elem)))
                (mv (type-bracket new-elem type.ispaces)
                    (make-type-eq-proof-cong-bracket
                     :type1 type.elem
                     :type2 new-elem
                     :ispaces type.ispaces
                     :premise1-proof proof)))
     :fun (b* (((mv new-in proof-in)
                (unsugar-nary-sigmas-in-type type.in))
               ((mv new-out proof-out)
                (unsugar-nary-sigmas-in-type type.out)))
            (mv (type-fun new-in new-out)
                (make-type-eq-proof-fun
                 :type-in1 type.in
                 :type-in2 new-in
                 :type-out1 type.out
                 :type-out2 new-out
                 :premise1-proof proof-in
                 :premise2-proof proof-out)))
     :funn (b* (((mv new-ins proof-ins)
                 (unsugar-nary-sigmas-in-type-list type.in))
                ((mv new-out proof-out)
                 (unsugar-nary-sigmas-in-type type.out)))
             (mv (type-funn new-ins new-out)
                 (make-type-eq-proof-cong-funn
                  :types-in1 type.in
                  :types-in2 new-ins
                  :type-out1 type.out
                  :type-out2 new-out
                  :premise1-proof proof-ins
                  :premise2-proof proof-out)))
     :forall (mv (type-forall type.param type.body)
                 (type-eq-proof-refl (type-forall type.param type.body)))
     :foralln (mv (type-foralln type.params type.body)
                  (type-eq-proof-refl (type-foralln type.params type.body)))
     :pi (mv (type-pi type.param type.body)
             (type-eq-proof-refl (type-pi type.param type.body)))
     :pin (mv (type-pin type.params type.body)
              (type-eq-proof-refl (type-pin type.params type.body)))
     :sigma (mv (type-sigma type.param type.body)
                (type-eq-proof-refl (type-sigma type.param type.body)))
     :sigman (b* ((param1 (car type.params))
                  (param2 (cadr type.params))
                  (params (cddr type.params)))
               (if (endp params)
                   (mv (type-sigma param1
                                   (type-scalar
                                    (type-sigma param2 type.body)))
                       (make-type-eq-proof-sigma2
                        :param1 param1
                        :param2 param2
                        :type type.body))
                 (mv (type-sigma
                      param1
                      (type-scalar
                       (type-sigman (cons param2 params) type.body)))
                     (make-type-eq-proof-sigma3m
                      :param1 param1
                      :param2 param2
                      :params params
                      :type type.body)))))
    :measure (type-count type))

  (define unsugar-nary-sigmas-in-type-list ((types type-listp))
    :returns (mv (new-types type-listp)
                 (proof types-eq-proofp))
    :parents (type-equivalence-normalizations unsugar-nary-sigmas-in-types)
    :short "Turn a list of types into an equivalent one
            without n-ary sum types outside the bodies of binder types,
            and construct a proof tree demonstrating the equivalence."
    (b* (((when (endp types)) (mv nil (types-eq-proof-refl nil)))
         ((mv new-type proof1) (unsugar-nary-sigmas-in-type (car types)))
         ((mv new-types proof2)
          (unsugar-nary-sigmas-in-type-list (cdr types))))
      (mv (cons new-type new-types)
          (make-types-eq-proof-cong-cons
           :type1 (type-fix (car types))
           :type2 new-type
           :types1 (type-list-fix (cdr types))
           :types2 new-types
           :premise1-proof proof1
           :premise2-proof proof2)))
    :measure (type-list-count types)

    ///

    (defret len-of-unsugar-nary-sigmas-in-type-list
      (equal (len new-types)
             (len types))
      :hints (("Goal"
               :induct (len types)
               :in-theory (enable (:induction len))))))

  :verify-guards :after-returns
  :guard-hints (("Goal"
                 :in-theory (enable consp-of-cdr-of-type-sigman->params)))

  ///

  (fty::deffixequiv-mutual unsugar-nary-sigmas-in-types)

  (defret-mutual type-eq-proof-validp-of-unsugar-nary-sigmas-in-types
    (defret type-eq-proof-validp-of-unsugar-nary-sigmas-in-type
      (implies (typep type)
               (type-eq-proof-validp proof type new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret types-eq-proof-validp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-listp types)
               (types-eq-proof-validp proof types new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable type-eq-proof-validp
                                types-eq-proof-validp
                                type-eq-refl-validp
                                types-eq-refl-validp
                                type-eq-array-validp
                                type-eq-fun-validp
                                type-eq-sigma2-validp
                                type-eq-sigma3m-validp
                                types-eq-cong-cons-validp
                                ispace-eq-refl
                                consp-of-cdr-of-type-sigman->params))))

  (defret-mutual type-nosigmanp-of-unsugar-nary-sigmas-in-types
    (defret type-nosigmanp-of-unsugar-nary-sigmas-in-type
      (type-nosigmanp new-type)
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-nosigmanp-of-unsugar-nary-sigmas-in-type-list
      (type-list-nosigmanp new-types)
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nosigmanp-rules))
            '(:expand ((type-nosigmanp type)
                       (:free (p b) (type-nosigmanp (type-forall p b)))
                       (:free (p b) (type-nosigmanp (type-foralln p b)))
                       (:free (p b) (type-nosigmanp (type-pi p b)))
                       (:free (p b) (type-nosigmanp (type-pin p b)))
                       (:free (p b) (type-nosigmanp (type-sigma p b)))
                       (:free (p b) (type-nosigmanp (type-sigman p b)))))))

  (defret-mutual type-noarrayvarp-of-unsugar-nary-sigmas-in-types
    (defret type-noarrayvarp-of-unsugar-nary-sigmas-in-type
      (implies (type-noarrayvarp type)
               (type-noarrayvarp new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-noarrayvarp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-list-noarrayvarp types)
               (type-list-noarrayvarp new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noarrayvarp-rules))
            '(:expand ((type-noarrayvarp type)
                       (:free (p b) (type-noarrayvarp (type-forall p b)))
                       (:free (p b) (type-noarrayvarp (type-foralln p b)))
                       (:free (p b) (type-noarrayvarp (type-pi p b)))
                       (:free (p b) (type-noarrayvarp (type-pin p b)))
                       (:free (p b) (type-noarrayvarp (type-sigma p b)))
                       (:free (p b) (type-noarrayvarp (type-sigman p b)))))))

  (defret-mutual type-nobracketp-of-unsugar-nary-sigmas-in-types
    (defret type-nobracketp-of-unsugar-nary-sigmas-in-type
      (implies (type-nobracketp type)
               (type-nobracketp new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-nobracketp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-list-nobracketp types)
               (type-list-nobracketp new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nobracketp-rules))
            '(:expand ((type-nobracketp type)
                       (:free (p b) (type-nobracketp (type-forall p b)))
                       (:free (p b) (type-nobracketp (type-foralln p b)))
                       (:free (p b) (type-nobracketp (type-pi p b)))
                       (:free (p b) (type-nobracketp (type-pin p b)))
                       (:free (p b) (type-nobracketp (type-sigma p b)))
                       (:free (p b) (type-nobracketp (type-sigman p b)))))))

  (defret-mutual type-nofunnp-of-unsugar-nary-sigmas-in-types
    (defret type-nofunnp-of-unsugar-nary-sigmas-in-type
      (implies (type-nofunnp type)
               (type-nofunnp new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-nofunnp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-list-nofunnp types)
               (type-list-nofunnp new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nofunnp-rules))
            '(:expand ((type-nofunnp type)
                       (:free (p b) (type-nofunnp (type-forall p b)))
                       (:free (p b) (type-nofunnp (type-foralln p b)))
                       (:free (p b) (type-nofunnp (type-pi p b)))
                       (:free (p b) (type-nofunnp (type-pin p b)))
                       (:free (p b) (type-nofunnp (type-sigma p b)))
                       (:free (p b) (type-nofunnp (type-sigman p b)))))))

  (defret-mutual type-noforallnp-of-unsugar-nary-sigmas-in-types
    (defret type-noforallnp-of-unsugar-nary-sigmas-in-type
      (implies (type-noforallnp type)
               (type-noforallnp new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-noforallnp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-list-noforallnp types)
               (type-list-noforallnp new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-noforallnp-rules))
            '(:expand ((type-noforallnp type)
                       (:free (p b) (type-noforallnp (type-forall p b)))
                       (:free (p b) (type-noforallnp (type-foralln p b)))
                       (:free (p b) (type-noforallnp (type-pi p b)))
                       (:free (p b) (type-noforallnp (type-pin p b)))
                       (:free (p b) (type-noforallnp (type-sigma p b)))
                       (:free (p b) (type-noforallnp (type-sigman p b)))))))

  (defret-mutual type-nopinp-of-unsugar-nary-sigmas-in-types
    (defret type-nopinp-of-unsugar-nary-sigmas-in-type
      (implies (type-nopinp type)
               (type-nopinp new-type))
      :fn unsugar-nary-sigmas-in-type)
    (defret type-list-nopinp-of-unsugar-nary-sigmas-in-type-list
      (implies (type-list-nopinp types)
               (type-list-nopinp new-types))
      :fn unsugar-nary-sigmas-in-type-list)
    :hints (("Goal"
             :in-theory (enable* ast-nopinp-rules))
            '(:expand ((type-nopinp type)
                       (:free (p b) (type-nopinp (type-forall p b)))
                       (:free (p b) (type-nopinp (type-foralln p b)))
                       (:free (p b) (type-nopinp (type-pi p b)))
                       (:free (p b) (type-nopinp (type-pin p b)))
                       (:free (p b) (type-nopinp (type-sigma p b)))
                       (:free (p b) (type-nopinp (type-sigman p b))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-noarrayvar-p-when-typep
  :short "Every type is equivalent to one
          without array type variables outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of the rule @('array-var'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-noarrayvar-p type))
  :use ((:instance type-eq-to-noarrayvar-p-suff
                   (type1 (mv-nth 0 (unsugar-array-vars-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-array-vars-in-type type)))
                   (concl.type1 type)
                   (concl.type2 (mv-nth 0 (unsugar-array-vars-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-nobracket-p-when-typep
  :short "Every type is equivalent to one
          without bracket types outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of the rule @('bracket'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-nobracket-p type))
  :use ((:instance type-eq-to-nobracket-p-suff
                   (type1 (mv-nth 0 (unsugar-brackets-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-brackets-in-type type)))
                   (concl.type1 type)
                   (concl.type2 (mv-nth 0 (unsugar-brackets-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-nofunn-p-when-typep
  :short "Every type is equivalent to one
          without n-ary function types outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     the rules @('fun0'), @('fun1'), and @('fun2m'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-nofunn-p type))
  :use ((:instance type-eq-to-nofunn-p-suff
                   (type1 (mv-nth 0 (unsugar-nary-funs-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-nary-funs-in-type type)))
                   (concl.type1 type)
                   (concl.type2 (mv-nth 0 (unsugar-nary-funs-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-noforalln-p-when-typep
  :short "Every type is equivalent to one
          without n-ary universal types outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     the rules @('forall2') and @('forall3m'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-noforalln-p type))
  :use ((:instance type-eq-to-noforalln-p-suff
                   (type1 (mv-nth 0 (unsugar-nary-foralls-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-nary-foralls-in-type type)))
                   (concl.type1 type)
                   (concl.type2
                    (mv-nth 0 (unsugar-nary-foralls-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-nopin-p-when-typep
  :short "Every type is equivalent to one
          without n-ary product types outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of the rules @('pi2') and @('pi3m'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-nopin-p type))
  :use ((:instance type-eq-to-nopin-p-suff
                   (type1 (mv-nth 0 (unsugar-nary-pis-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-nary-pis-in-type type)))
                   (concl.type1 type)
                   (concl.type2 (mv-nth 0 (unsugar-nary-pis-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-nosigman-p-when-typep
  :short "Every type is equivalent to one
          without n-ary sum types outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of
     the rules @('sigma2') and @('sigma3m'),
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-nosigman-p type))
  :use ((:instance type-eq-to-nosigman-p-suff
                   (type1 (mv-nth 0 (unsugar-nary-sigmas-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-nary-sigmas-in-type type)))
                   (concl.type1 type)
                   (concl.type2
                    (mv-nth 0 (unsugar-nary-sigmas-in-type type))))))

;;;;;;;;;;;;;;;;;;;;

(define unsugar-in-type ((type typep))
  :returns (mv (new-type typep)
               (proof type-eq-proofp))
  :short "Turn a type into an equivalent one without
          array type variables,
          bracket types,
          and n-ary function, universal, product, and sum types
          outside the bodies of binder types,
          and construct a proof tree demonstrating the equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "This composes the six transformations, in the order:
     eliminate array type variables,
     eliminate bracket types,
     eliminate n-ary function types,
     eliminate n-ary universal types,
     eliminate n-ary product types,
     eliminate n-ary sum types.
     The proof trees of the six transformations
     are chained via the rule @('trans').")
   (xdoc::p
    "Each transformation establishes its own status,
     and preserves the statuses established by the preceding ones;
     thus, the resulting type has all six statuses.
     Any order of the six transformations works,
     because each transformation preserves
     the statuses established by the other five."))
  (b* ((type (type-fix type))
       ((mv type1 proof1) (unsugar-array-vars-in-type type))
       ((mv type2 proof2) (unsugar-brackets-in-type type1))
       ((mv type3 proof3) (unsugar-nary-funs-in-type type2))
       ((mv type4 proof4) (unsugar-nary-foralls-in-type type3))
       ((mv type5 proof5) (unsugar-nary-pis-in-type type4))
       ((mv type6 proof6) (unsugar-nary-sigmas-in-type type5)))
    (mv type6
        (make-type-eq-proof-trans
         :type1 type
         :type2 type1
         :type3 type6
         :premise1-proof proof1
         :premise2-proof
         (make-type-eq-proof-trans
          :type1 type1
          :type2 type2
          :type3 type6
          :premise1-proof proof2
          :premise2-proof
          (make-type-eq-proof-trans
           :type1 type2
           :type2 type3
           :type3 type6
           :premise1-proof proof3
           :premise2-proof
           (make-type-eq-proof-trans
            :type1 type3
            :type2 type4
            :type3 type6
            :premise1-proof proof4
            :premise2-proof
            (make-type-eq-proof-trans
             :type1 type4
             :type2 type5
             :type3 type6
             :premise1-proof proof5
             :premise2-proof proof6)))))))

  ///

  (defret type-eq-proof-validp-of-unsugar-in-type
    (implies (typep type)
             (type-eq-proof-validp proof type new-type))
    :hints (("Goal" :in-theory (enable type-eq-proof-validp
                                       type-eq-trans-validp))))

  (defret type-noarrayvarp-of-unsugar-in-type
    (type-noarrayvarp new-type))

  (defret type-nobracketp-of-unsugar-in-type
    (type-nobracketp new-type))

  (defret type-nofunnp-of-unsugar-in-type
    (type-nofunnp new-type))

  (defret type-noforallnp-of-unsugar-in-type
    (type-noforallnp new-type))

  (defret type-nopinp-of-unsugar-in-type
    (type-nopinp new-type))

  (defret type-nosigmanp-of-unsugar-in-type
    (type-nosigmanp new-type)))

;;;;;;;;;;;;;;;;;;;;

(defruled type-eq-to-noarrayvar-nobracket-nonaries-p-when-typep
  :short "Every type is equivalent to one without
          array type variables,
          bracket types,
          and n-ary function, universal, product, and sum types
          outside the bodies of binder types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This validates the intention of all the normalization rules together,
     described in @(see type-equivalence-definition)."))
  (implies (typep type)
           (type-eq-to-noarrayvar-nobracket-nonaries-p type))
  :use ((:instance type-eq-to-noarrayvar-nobracket-nonaries-p-suff
                   (type1 (mv-nth 0 (unsugar-in-type type))))
        (:instance type-eq-when-proof-validp
                   (proof (mv-nth 1 (unsugar-in-type type)))
                   (concl.type1 type)
                   (concl.type2 (mv-nth 0 (unsugar-in-type type))))))
