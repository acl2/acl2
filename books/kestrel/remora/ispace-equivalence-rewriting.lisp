; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "ispace-equivalence-derived-rules")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rewrite rules in this book are stated on calls of the AST constructors,
; so we keep ground calls of the constructors unevaluated.

(local (in-theory (disable (:e dim-const)
                           (:e dim-add)
                           (:e dim-mul)
                           (:e dim-sub)
                           (:e shape-dims)
                           (:e shape-append)
                           (:e shape-splice))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence-rewriting
  :parents (static-semantics)
  :short "Rewriting modulo ispace equivalence."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates defined in @(see ispace-equivalence)
     only hold on dimensions, shapes, ispaces, and lists thereof
     (see @(see dim-equivalence-holds-only-on-dimensions)
     and @(see shape/ispace-equivalence-holds-only-on-shapes/ispaces)).
     Thus, they are not reflexive on all ACL2 values,
     and they are not equivalence relations in the ACL2 sense.
     Here we introduce versions of those predicates
     that fix their arguments,
     and that are therefore equivalence relations in the ACL2 sense;
     they coincide with the original predicates
     on dimensions, shapes, ispaces, and lists thereof.")
   (xdoc::p
    "The inference rules for reflexivity, symmetry, and transitivity
     amount to the fact that these are equivalence relations.
     We prove ACL2 congruence rules
     for the constructors of dimensions, shapes, ispaces, and lists thereof,
     which correspond to the congruence inference rules.
     We prove rewrite rules that correspond to
     the other inference rules without premises,
     both defining (see @(see ispace-equivalence))
     and derived (see @(see ispace-equivalence-derived-rules)),
     oriented from left to right;
     we also prove additional rewrite rules.
     These let ACL2 rewrite
     a dimension, shape, ispace, or list thereof
     to an equivalent one,
     also when it occurs inside another one:
     a chain of applications of inference rules,
     including the ones for symmetry, transitivity, and congruence,
     is carried out by the rewriter,
     instead of being spelled out as a proof tree or via hints.")
   (xdoc::p
    "The rewrite rules are disabled by default.
     The rule sets @('dim-eq-equiv-rules') and @('shape-eq-equiv-rules')
     collect the rules that are meant to be used together
     to normalize dimensions and shapes;
     the remaining rules are meant to be enabled individually.
     The rules are stated on calls of the AST constructors,
     e.g. @('(dim-const 0)'):
     in order for them to apply to ground calls of the constructors,
     the executable counterparts of the constructors must be disabled."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-eq-equiv ((dim1 dimp) (dim2 dimp))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This fixes the arguments of @('dim-eq') to dimensions.
     It is an equivalence relation in the ACL2 sense,
     which is refined by the equivalence relation of the fixtype,
     and which coincides with @('dim-eq') on dimensions."))
  (dim-eq (dim-fix dim1) (dim-fix dim2))

  ///

  (defequiv dim-eq-equiv
    :hints (("Goal" :in-theory (enable dim-eq-refl
                                       dim-eq-symm!
                                       dim-eq-trans!))))

  (defrefinement dim-equiv dim-eq-equiv
    :hints (("Goal" :in-theory (enable dim-eq-refl))))

  (defruled dim-eq-equiv-when-dim-eq
    (implies (dim-eq dim1 dim2)
             (dim-eq-equiv dim1 dim2))
    :enable dimp-when-dim-eq)

  (defruled dim-eq-when-dim-eq-equiv
    (implies (and (dim-eq-equiv dim1 dim2)
                  (dimp dim1)
                  (dimp dim2))
             (dim-eq dim1 dim2))))

;;;;;;;;;;;;;;;;;;;;

(define dims-eq-equiv ((dims1 dim-listp) (dims2 dim-listp))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-equiv)."))
  (dims-eq (dim-list-fix dims1) (dim-list-fix dims2))

  ///

  (defequiv dims-eq-equiv
    :hints (("Goal" :in-theory (enable dims-eq-refl
                                       dims-eq-symm!
                                       dims-eq-trans!))))

  (defrefinement dim-list-equiv dims-eq-equiv
    :hints (("Goal" :in-theory (enable dims-eq-refl))))

  (defruled dims-eq-equiv-when-dims-eq
    (implies (dims-eq dims1 dims2)
             (dims-eq-equiv dims1 dims2))
    :enable dim-listp-when-dims-eq)

  (defruled dims-eq-when-dims-eq-equiv
    (implies (and (dims-eq-equiv dims1 dims2)
                  (dim-listp dims1)
                  (dim-listp dims2))
             (dims-eq dims1 dims2)))

  (defruled dims-eq-equiv-of-nil-when-not-consp
    (implies (not (consp dims))
             (dims-eq-equiv nil dims))
    :enable (dims-eq-refl
             dim-list-fix)))

;;;;;;;;;;;;;;;;;;;;

(defsection dim-eq-equiv-congruences
  :short "ACL2 congruence rules for the equivalence relations
          induced by the equivalence of dimensions and lists of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These correspond to the congruence inference rules.
     The inference rule for lists
     is split into two ACL2 congruence rules,
     one for each argument of @(tsee cons)."))

  (defcong dim-eq-equiv dims-eq-equiv (cons dim dims) 1
    :hints (("Goal" :in-theory (enable dim-eq-equiv
                                       dims-eq-equiv
                                       dims-eq-cong-cons!
                                       dims-eq-refl))))

  (defcong dims-eq-equiv dims-eq-equiv (cons dim dims) 2
    :hints (("Goal" :in-theory (enable dim-eq-equiv
                                       dims-eq-equiv
                                       dims-eq-cong-cons!
                                       dim-eq-refl))))

  (defcong dims-eq-equiv dim-eq-equiv (dim-add dims) 1
    :hints (("Goal"
             :in-theory (enable dim-eq-equiv
                                dims-eq-equiv)
             :use (:instance dim-eq-cong-add!
                             (dims1 (dim-list-fix dims))
                             (dims2 (dim-list-fix dims-equiv))))))

  (defcong dims-eq-equiv dim-eq-equiv (dim-mul dims) 1
    :hints (("Goal"
             :in-theory (enable dim-eq-equiv
                                dims-eq-equiv)
             :use (:instance dim-eq-cong-mul!
                             (dims1 (dim-list-fix dims))
                             (dims2 (dim-list-fix dims-equiv))))))

  (defcong dims-eq-equiv dim-eq-equiv (dim-sub dims) 1
    :hints (("Goal"
             :in-theory (enable dim-eq-equiv
                                dims-eq-equiv)
             :use (:instance dim-eq-cong-sub!
                             (dims1 (dim-list-fix dims))
                             (dims2 (dim-list-fix dims-equiv)))))))

;;;;;;;;;;;;;;;;;;;;

(defsection dim-eq-equiv-rewrite-rules
  :short "Rewrite rules for the equivalence relation
          induced by the equivalence of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "First, we prove the rules that correspond to
     defining and derived inference rules;
     each has the name of the corresponding theorem about @('dim-eq'),
     with @('dim-eq-equiv') in place of @('dim-eq').
     Since the equivalence relation fixes its arguments,
     these rules have no hypotheses on the types of the variables;
     the natural numbers in the rules about constants are fixed.
     The rules @('add3m') and @('mul3m'),
     which left-associate variadic additions and multiplications,
     and the rule @('add-interchange'),
     which does not normalize additions,
     are not in the rule set @('dim-eq-equiv-rules').")
   (xdoc::p
    "Then, we prove additional rules.
     Since the rules for commutativity
     can only be used when they sort the operands
     (according to the heuristics for permutative rules),
     we add rules to commute the first two operands
     of a right-associated nest of additions or multiplications;
     together with associativity and commutativity,
     they sort the operands of the whole nest.
     Similarly, we add rules to cancel a dimension and its additive inverse
     when followed by another operand in a nest of additions.")
   (xdoc::p
    "The rules @('add-cons') and @('mul-cons') turn
     an addition or multiplication of a list of operands
     with a first operand
     into the binary addition or multiplication of
     the first operand
     and the addition or multiplication of the remaining operands.
     They generalize @('add3m') and @('mul3m'),
     from which they are proved, by induction on the remaining operands,
     with the first operand changing in the induction hypotheses:
     an operation on three or more operands is first left-associated
     and then right-associated.
     They are restricted to the case in which the remaining operands
     are neither none nor exactly one explicit operand:
     otherwise, they would rewrite unary and binary operations forever.")
   (xdoc::p
    "The rule @('mul-of-append') is about
     the multiplication of two appended lists of operands.
     The rule @('mul-interchange') is analogous to @('add-interchange');
     its proof is carried out by the rewriter,
     via the rules that sort the operands of multiplications.")
   (xdoc::p
    "The last rule is about an addition of no operands,
     expressed via a list that is not a @(tsee cons) pair."))

  ;; rules that correspond to defining and derived inference rules:

  (defruled dim-eq-equiv-add0
    (dim-eq-equiv (dim+)
                  (dim-const 0))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-add0))

  (defruled dim-eq-equiv-add1
    (dim-eq-equiv (dim+ dim)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-add1 (dim (dim-fix dim))))

  (defruled dim-eq-equiv-add3m
    (implies (consp dims)
             (dim-eq-equiv (dim-add (list* dim1 dim2 dims))
                           (dim-add (cons (dim+ dim1 dim2) dims))))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-add3m!))

  (defruled dim-eq-equiv-mul0
    (dim-eq-equiv (dim*)
                  (dim-const 1))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-mul0))

  (defruled dim-eq-equiv-mul1
    (dim-eq-equiv (dim* dim)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-mul1 (dim (dim-fix dim))))

  (defruled dim-eq-equiv-mul3m
    (implies (consp dims)
             (dim-eq-equiv (dim-mul (list* dim1 dim2 dims))
                           (dim-mul (cons (dim* dim1 dim2) dims))))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-mul3m!))

  (defruled dim-eq-equiv-sub2m
    (implies (consp dims)
             (dim-eq-equiv (dim-sub (cons dim dims))
                           (dim+ dim (dim- (dim-add dims)))))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-sub2m!))

  (defruled dim-eq-equiv-add-comm
    (dim-eq-equiv (dim+ dim1 dim2)
                  (dim+ dim2 dim1))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-add-comm!))

  (defruled dim-eq-equiv-add-assoc
    (dim-eq-equiv (dim+ (dim+ dim1 dim2) dim3)
                  (dim+ dim1 (dim+ dim2 dim3)))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-add-assoc!))

  (defruled dim-eq-equiv-add-interchange
    (dim-eq-equiv (dim+ (dim+ dim1 dim2) (dim+ dim3 dim4))
                  (dim+ (dim+ dim1 dim3) (dim+ dim2 dim4)))
    :enable dim-eq-equiv
    :use (:instance dim-eq-add-interchange
                    (dim1 (dim-fix dim1))
                    (dim2 (dim-fix dim2))
                    (dim3 (dim-fix dim3))
                    (dim4 (dim-fix dim4))))

  (defruled dim-eq-equiv-add-id
    (dim-eq-equiv (dim+ 0 dim)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-add-id (dim (dim-fix dim))))

  (defruled dim-eq-equiv-add-id-right
    (dim-eq-equiv (dim+ dim 0)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-add-id-right (dim (dim-fix dim))))

  (defruled dim-eq-equiv-add-inv
    (dim-eq-equiv (dim+ dim (dim- dim))
                  (dim-const 0))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-add-inv!))

  (defruled dim-eq-equiv-add-inv-left
    (dim-eq-equiv (dim+ (dim- dim) dim)
                  (dim-const 0))
    :enable dim-eq-equiv
    :use (:instance dim-eq-add-inv-left (dim (dim-fix dim))))

  (defruled dim-eq-equiv-add-const
    (dim-eq-equiv (dim+ (dim-const n1) (dim-const n2))
                  (dim-const (+ (nfix n1) (nfix n2))))
    :enable dim-eq-equiv-when-dim-eq
    :use (:instance dim-eq-add-const (n1 (nfix n1)) (n2 (nfix n2))))

  (defruled dim-eq-equiv-neg-zero
    (dim-eq-equiv (dim- 0)
                  (dim-const 0))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-neg-zero))

  (defruled dim-eq-equiv-neg-neg
    (dim-eq-equiv (dim- (dim- dim))
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-neg-neg (dim (dim-fix dim))))

  (defruled dim-eq-equiv-neg-add
    (dim-eq-equiv (dim- (dim+ dim1 dim2))
                  (dim+ (dim- dim1) (dim- dim2)))
    :enable dim-eq-equiv
    :use (:instance dim-eq-neg-add
                    (dim1 (dim-fix dim1))
                    (dim2 (dim-fix dim2))))

  (defruled dim-eq-equiv-mul-comm
    (dim-eq-equiv (dim* dim1 dim2)
                  (dim* dim2 dim1))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-mul-comm!))

  (defruled dim-eq-equiv-mul-assoc
    (dim-eq-equiv (dim* (dim* dim1 dim2) dim3)
                  (dim* dim1 (dim* dim2 dim3)))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-mul-assoc!))

  (defruled dim-eq-equiv-mul-id
    (dim-eq-equiv (dim* 1 dim)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-mul-id (dim (dim-fix dim))))

  (defruled dim-eq-equiv-mul-id-right
    (dim-eq-equiv (dim* dim 1)
                  dim)
    :enable dim-eq-equiv
    :use (:instance dim-eq-mul-id-right (dim (dim-fix dim))))

  (defruled dim-eq-equiv-mul-zero-left
    (dim-eq-equiv (dim* 0 dim)
                  (dim-const 0))
    :enable dim-eq-equiv
    :use (:instance dim-eq-mul-zero-left (dim (dim-fix dim))))

  (defruled dim-eq-equiv-mul-zero-right
    (dim-eq-equiv (dim* dim 0)
                  (dim-const 0))
    :enable dim-eq-equiv
    :use (:instance dim-eq-mul-zero-right (dim (dim-fix dim))))

  (defruled dim-eq-equiv-mul-const
    (dim-eq-equiv (dim* (dim-const n1) (dim-const n2))
                  (dim-const (* (nfix n1) (nfix n2))))
    :enable dim-eq-equiv-when-dim-eq
    :use (:instance dim-eq-mul-const (n1 (nfix n1)) (n2 (nfix n2))))

  (defruled dim-eq-equiv-distrib
    (dim-eq-equiv (dim* dim (dim+ dim1 dim2))
                  (dim+ (dim* dim dim1) (dim* dim dim2)))
    :enable (dim-eq-equiv-when-dim-eq
             dim-eq-distrib!))

  (defruled dim-eq-equiv-distrib-right
    (dim-eq-equiv (dim* (dim+ dim1 dim2) dim)
                  (dim+ (dim* dim1 dim) (dim* dim2 dim)))
    :enable dim-eq-equiv
    :use (:instance dim-eq-distrib-right
                    (dim (dim-fix dim))
                    (dim1 (dim-fix dim1))
                    (dim2 (dim-fix dim2))))

  (defruled dim-eq-equiv-neg-mul-left
    (dim-eq-equiv (dim* (dim- dim1) dim2)
                  (dim- (dim* dim1 dim2)))
    :enable dim-eq-equiv
    :use (:instance dim-eq-neg-mul-left
                    (dim1 (dim-fix dim1))
                    (dim2 (dim-fix dim2))))

  (defruled dim-eq-equiv-neg-mul-right
    (dim-eq-equiv (dim* dim1 (dim- dim2))
                  (dim- (dim* dim1 dim2)))
    :enable dim-eq-equiv
    :use (:instance dim-eq-neg-mul-right
                    (dim1 (dim-fix dim1))
                    (dim2 (dim-fix dim2))))

  ;; additional rules:

  (defruled dim-eq-equiv-add-comm-2
    (dim-eq-equiv (dim+ dim1 (dim+ dim2 dim3))
                  (dim+ dim2 (dim+ dim1 dim3)))
    :use ((:instance dim-eq-equiv-add-assoc
                     (dim1 dim1) (dim2 dim2) (dim3 dim3))
          (:instance dim-eq-equiv-add-assoc
                     (dim1 dim2) (dim2 dim1) (dim3 dim3))
          (:instance dim-eq-equiv-add-comm
                     (dim1 dim1) (dim2 dim2))))

  (defruled dim-eq-equiv-add-inv-2
    (dim-eq-equiv (dim+ dim1 (dim+ (dim- dim1) dim2))
                  dim2)
    :enable (dim-eq-equiv-add-inv
             dim-eq-equiv-add-id)
    :use (:instance dim-eq-equiv-add-assoc
                    (dim1 dim1) (dim2 (dim- dim1)) (dim3 dim2)))

  (defruled dim-eq-equiv-add-inv-left-2
    (dim-eq-equiv (dim+ (dim- dim1) (dim+ dim1 dim2))
                  dim2)
    :enable (dim-eq-equiv-add-inv-left
             dim-eq-equiv-add-id)
    :use (:instance dim-eq-equiv-add-assoc
                    (dim1 (dim- dim1)) (dim2 dim1) (dim3 dim2)))

  (defruled dim-eq-equiv-mul-comm-2
    (dim-eq-equiv (dim* dim1 (dim* dim2 dim3))
                  (dim* dim2 (dim* dim1 dim3)))
    :use ((:instance dim-eq-equiv-mul-assoc
                     (dim1 dim1) (dim2 dim2) (dim3 dim3))
          (:instance dim-eq-equiv-mul-assoc
                     (dim1 dim2) (dim2 dim1) (dim3 dim3))
          (:instance dim-eq-equiv-mul-comm
                     (dim1 dim1) (dim2 dim2))))

  (local
   (defun dim-add/mul-cons-induct (dim dims)
     (declare (irrelevant dim))
     (cond ((not (consp dims)) nil)
           ((not (consp (cdr dims))) nil)
           (t (list (dim-add/mul-cons-induct (dim+ dim (car dims))
                                             (cdr dims))
                    (dim-add/mul-cons-induct (dim* dim (car dims))
                                             (cdr dims))
                    (dim-add/mul-cons-induct (car dims)
                                             (cdr dims)))))))

  (defruled dim-eq-equiv-add-cons
    (implies (syntaxp (not (or (equal dims ''nil)
                               (and (consp dims)
                                    (eq (car dims) 'cons)
                                    (equal (caddr dims) ''nil)))))
             (dim-eq-equiv (dim-add (cons dim dims))
                           (dim+ dim (dim-add dims))))
    :use (:instance lemma (dims (dim-list-fix dims)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims)
                (dim-eq-equiv (dim-add (cons dim dims))
                              (dim+ dim (dim-add dims))))
       :induct (dim-add/mul-cons-induct dim dims)
       :enable (dim-eq-equiv-add0
                dim-eq-equiv-add1
                dim-eq-equiv-add3m
                dim-eq-equiv-add-assoc
                dim-eq-equiv-add-id-right))))

  (defruled dim-eq-equiv-mul-cons
    (implies (syntaxp (not (or (equal dims ''nil)
                               (and (consp dims)
                                    (eq (car dims) 'cons)
                                    (equal (caddr dims) ''nil)))))
             (dim-eq-equiv (dim-mul (cons dim dims))
                           (dim* dim (dim-mul dims))))
    :use (:instance lemma (dims (dim-list-fix dims)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims)
                (dim-eq-equiv (dim-mul (cons dim dims))
                              (dim* dim (dim-mul dims))))
       :induct (dim-add/mul-cons-induct dim dims)
       :enable (dim-eq-equiv-mul0
                dim-eq-equiv-mul1
                dim-eq-equiv-mul3m
                dim-eq-equiv-mul-assoc
                dim-eq-equiv-mul-id-right))))

  (defruled dim-eq-equiv-mul-of-append
    (dim-eq-equiv (dim-mul (append dims1 dims2))
                  (dim* (dim-mul dims1) (dim-mul dims2)))
    :use (:instance lemma (dims1 (dim-list-fix dims1)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims1)
                (dim-eq-equiv (dim-mul (append dims1 dims2))
                              (dim* (dim-mul dims1) (dim-mul dims2))))
       :induct t
       :enable (append
                dim-eq-equiv-mul0
                dim-eq-equiv-mul-cons
                dim-eq-equiv-mul-assoc
                dim-eq-equiv-mul-id))))

  (defruled dim-eq-equiv-mul-interchange
    (dim-eq-equiv (dim* (dim* dim1 dim2) (dim* dim3 dim4))
                  (dim* (dim* dim1 dim3) (dim* dim2 dim4)))
    :enable (dim-eq-equiv-mul-assoc
             dim-eq-equiv-mul-comm-2))

  (defruled dim-eq-equiv-add-when-not-consp
    (implies (not (consp dims))
             (dim-eq-equiv (dim-add dims)
                           (dim-const 0)))
    :enable dim-eq-equiv-add0
    :use ((:instance dims-eq-equiv-implies-dim-eq-equiv-dim-add-1
                     (dims-equiv nil))
          dims-eq-equiv-of-nil-when-not-consp))

  ;; rule set:

  (acl2::def-ruleset dim-eq-equiv-rules
    '(dim-eq-equiv-add0
      dim-eq-equiv-add1
      dim-eq-equiv-mul0
      dim-eq-equiv-mul1
      dim-eq-equiv-sub2m
      dim-eq-equiv-add-comm
      dim-eq-equiv-add-comm-2
      dim-eq-equiv-add-assoc
      dim-eq-equiv-add-id
      dim-eq-equiv-add-id-right
      dim-eq-equiv-add-inv
      dim-eq-equiv-add-inv-left
      dim-eq-equiv-add-inv-2
      dim-eq-equiv-add-inv-left-2
      dim-eq-equiv-add-const
      dim-eq-equiv-neg-zero
      dim-eq-equiv-neg-neg
      dim-eq-equiv-neg-add
      dim-eq-equiv-mul-comm
      dim-eq-equiv-mul-comm-2
      dim-eq-equiv-mul-assoc
      dim-eq-equiv-mul-id
      dim-eq-equiv-mul-id-right
      dim-eq-equiv-mul-zero-left
      dim-eq-equiv-mul-zero-right
      dim-eq-equiv-mul-const
      dim-eq-equiv-distrib
      dim-eq-equiv-distrib-right
      dim-eq-equiv-neg-mul-left
      dim-eq-equiv-neg-mul-right)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-eq-equiv ((shape1 shapep) (shape2 shapep))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-equiv)."))
  (shape-eq (shape-fix shape1) (shape-fix shape2))

  ///

  (defequiv shape-eq-equiv
    :hints (("Goal" :in-theory (enable shape-eq-refl
                                       shape-eq-symm!
                                       shape-eq-trans!))))

  (defrefinement shape-equiv shape-eq-equiv
    :hints (("Goal" :in-theory (enable shape-eq-refl))))

  (defruled shape-eq-equiv-when-shape-eq
    (implies (shape-eq shape1 shape2)
             (shape-eq-equiv shape1 shape2))
    :enable shapep-when-shape-eq)

  (defruled shape-eq-when-shape-eq-equiv
    (implies (and (shape-eq-equiv shape1 shape2)
                  (shapep shape1)
                  (shapep shape2))
             (shape-eq shape1 shape2))))

;;;;;;;;;;;;;;;;;;;;

(define shapes-eq-equiv ((shapes1 shape-listp) (shapes2 shape-listp))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of lists of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-equiv)."))
  (shapes-eq (shape-list-fix shapes1) (shape-list-fix shapes2))

  ///

  (defequiv shapes-eq-equiv
    :hints (("Goal" :in-theory (enable shapes-eq-refl
                                       shapes-eq-symm!
                                       shapes-eq-trans!))))

  (defrefinement shape-list-equiv shapes-eq-equiv
    :hints (("Goal" :in-theory (enable shapes-eq-refl))))

  (defruled shapes-eq-equiv-when-shapes-eq
    (implies (shapes-eq shapes1 shapes2)
             (shapes-eq-equiv shapes1 shapes2))
    :enable shape-listp-when-shapes-eq)

  (defruled shapes-eq-when-shapes-eq-equiv
    (implies (and (shapes-eq-equiv shapes1 shapes2)
                  (shape-listp shapes1)
                  (shape-listp shapes2))
             (shapes-eq shapes1 shapes2)))

  (defruled shapes-eq-equiv-of-nil-when-not-consp
    (implies (not (consp shapes))
             (shapes-eq-equiv nil shapes))
    :enable (shapes-eq-refl
             shape-list-fix)))

;;;;;;;;;;;;;;;;;;;;

(define ispace-eq-equiv ((ispace1 ispacep) (ispace2 ispacep))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-equiv)."))
  (ispace-eq (ispace-fix ispace1) (ispace-fix ispace2))

  ///

  (defequiv ispace-eq-equiv
    :hints (("Goal" :in-theory (enable ispace-eq-refl
                                       ispace-eq-symm!
                                       ispace-eq-trans!))))

  (defrefinement ispace-equiv ispace-eq-equiv
    :hints (("Goal" :in-theory (enable ispace-eq-refl))))

  (defruled ispace-eq-equiv-when-ispace-eq
    (implies (ispace-eq ispace1 ispace2)
             (ispace-eq-equiv ispace1 ispace2))
    :enable ispacep-when-ispace-eq)

  (defruled ispace-eq-when-ispace-eq-equiv
    (implies (and (ispace-eq-equiv ispace1 ispace2)
                  (ispacep ispace1)
                  (ispacep ispace2))
             (ispace-eq ispace1 ispace2))))

;;;;;;;;;;;;;;;;;;;;

(define ispaces-eq-equiv ((ispaces1 ispace-listp) (ispaces2 ispace-listp))
  :returns (yes/no booleanp)
  :short "Equivalence relation on ACL2 values
          induced by the equivalence of lists of ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee dim-eq-equiv)."))
  (ispaces-eq (ispace-list-fix ispaces1) (ispace-list-fix ispaces2))

  ///

  (defequiv ispaces-eq-equiv
    :hints (("Goal" :in-theory (enable ispaces-eq-refl
                                       ispaces-eq-symm!
                                       ispaces-eq-trans!))))

  (defrefinement ispace-list-equiv ispaces-eq-equiv
    :hints (("Goal" :in-theory (enable ispaces-eq-refl))))

  (defruled ispaces-eq-equiv-when-ispaces-eq
    (implies (ispaces-eq ispaces1 ispaces2)
             (ispaces-eq-equiv ispaces1 ispaces2))
    :enable ispace-listp-when-ispaces-eq)

  (defruled ispaces-eq-when-ispaces-eq-equiv
    (implies (and (ispaces-eq-equiv ispaces1 ispaces2)
                  (ispace-listp ispaces1)
                  (ispace-listp ispaces2))
             (ispaces-eq ispaces1 ispaces2)))

  (defruled ispaces-eq-equiv-of-nil-when-not-consp
    (implies (not (consp ispaces))
             (ispaces-eq-equiv nil ispaces))
    :enable (ispaces-eq-refl
             ispace-list-fix)))

;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-eq-equiv-congruences
  :short "ACL2 congruence rules for the equivalence relations
          induced by the equivalence of
          shapes, ispaces, and lists thereof."
  :long
  (xdoc::topstring
   (xdoc::p
    "These correspond to the congruence inference rules.
     Each of the two inference rules for lists
     is split into two ACL2 congruence rules,
     one for each argument of @(tsee cons)."))

  (defcong shape-eq-equiv shapes-eq-equiv (cons shape shapes) 1
    :hints (("Goal" :in-theory (enable shape-eq-equiv
                                       shapes-eq-equiv
                                       shapes-eq-cong-cons!
                                       shapes-eq-refl))))

  (defcong shapes-eq-equiv shapes-eq-equiv (cons shape shapes) 2
    :hints (("Goal" :in-theory (enable shape-eq-equiv
                                       shapes-eq-equiv
                                       shapes-eq-cong-cons!
                                       shape-eq-refl))))

  (defcong ispace-eq-equiv ispaces-eq-equiv (cons ispace ispaces) 1
    :hints (("Goal" :in-theory (enable ispace-eq-equiv
                                       ispaces-eq-equiv
                                       ispaces-eq-cong-cons!
                                       ispaces-eq-refl))))

  (defcong ispaces-eq-equiv ispaces-eq-equiv (cons ispace ispaces) 2
    :hints (("Goal" :in-theory (enable ispace-eq-equiv
                                       ispaces-eq-equiv
                                       ispaces-eq-cong-cons!
                                       ispace-eq-refl))))

  (defcong dims-eq-equiv shape-eq-equiv (shape-dims dims) 1
    :hints (("Goal"
             :in-theory (enable shape-eq-equiv
                                dims-eq-equiv)
             :use (:instance shape-eq-cong-dims!
                             (dims1 (dim-list-fix dims))
                             (dims2 (dim-list-fix dims-equiv))))))

  (defcong shapes-eq-equiv shape-eq-equiv (shape-append shapes) 1
    :hints (("Goal"
             :in-theory (enable shape-eq-equiv
                                shapes-eq-equiv)
             :use (:instance shape-eq-cong-append!
                             (shapes1 (shape-list-fix shapes))
                             (shapes2 (shape-list-fix shapes-equiv))))))

  (defcong ispaces-eq-equiv shape-eq-equiv (shape-splice ispaces) 1
    :hints (("Goal"
             :in-theory (enable shape-eq-equiv
                                ispaces-eq-equiv)
             :use (:instance shape-eq-cong-splice!
                             (ispaces1 (ispace-list-fix ispaces))
                             (ispaces2 (ispace-list-fix ispaces-equiv))))))

  (defcong dim-eq-equiv ispace-eq-equiv (ispace-dim dim) 1
    :hints (("Goal"
             :in-theory (enable ispace-eq-equiv
                                dim-eq-equiv)
             :use (:instance ispace-eq-cong-dim!
                             (dim1 (dim-fix dim))
                             (dim2 (dim-fix dim-equiv))))))

  (defcong shape-eq-equiv ispace-eq-equiv (ispace-shape shape) 1
    :hints (("Goal"
             :in-theory (enable ispace-eq-equiv
                                shape-eq-equiv)
             :use (:instance ispace-eq-cong-shape!
                             (shape1 (shape-fix shape))
                             (shape2 (shape-fix shape-equiv)))))))

;;;;;;;;;;;;;;;;;;;;

(defsection shape/ispace-eq-equiv-rewrite-rules
  :short "Rewrite rules for the equivalence relations
          induced by the equivalence of shapes and ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "First, we prove the rules that correspond to
     defining inference rules;
     each has the name of the corresponding theorem
     about @('shape-eq') or @('ispace-eq'),
     with @('shape-eq-equiv') or @('ispace-eq-equiv')
     in place of @('shape-eq') or @('ispace-eq').
     The rules for splices are expressed in terms of
     the kind of the first ispace,
     instead of a constructor of ispaces,
     so that they also apply when the kind of the ispace is known
     but the ispace is not a call of a constructor;
     the same holds for the rule that relates
     a dimension ispace and a singleton shape ispace,
     which is oriented from right to left.
     The rule @('append3m'),
     which left-associates variadic concatenations,
     and the rule about dimension ispaces,
     are not in the rule set @('shape-eq-equiv-rules').")
   (xdoc::p
    "Then, we prove additional rules.
     The rules @('dims-cons'), @('append-cons'), and @('splice-cons')
     turn a shape built from
     a list of dimensions, shapes, or ispaces with a first element
     into the binary concatenation of
     the shape built from the first element
     and the shape built from the remaining elements;
     they are restricted, similarly to the analogous rules for dimensions
     (see @(see dim-eq-equiv-rewrite-rules)),
     so that they do not rewrite forever.
     The rule @('append-cons') generalizes @('append3m'),
     from which it is proved
     like the analogous rules for dimensions.
     The rule @('dims-cons') extends @('dims2m')
     to the case of a single dimension.
     The rule @('splice-cons') is uniform over the kinds of ispaces.")
   (xdoc::p
    "The rule @('append-of-append') is about
     the concatenation of two appended lists of shapes.")
   (xdoc::p
    "The last three rules are about shapes built from
     no dimensions, shapes, or ispaces,
     expressed via lists that are not @(tsee cons) pairs.
     The one for concatenations is restricted to
     the case in which the list is not explicitly @('nil'):
     otherwise, it would rewrite the empty concatenation to itself forever."))

  ;; rules that correspond to defining inference rules:

  (defruled shape-eq-equiv-dims0
    (shape-eq-equiv (shp)
                    (shp++))
    :enable (shape-eq-equiv-when-shape-eq
             shape-eq-dims0))

  (defruled shape-eq-equiv-dims2m
    (implies (consp dims)
             (shape-eq-equiv (shape-dims (cons dim dims))
                             (shp++ (shp dim) (shape-dims dims))))
    :enable (shape-eq-equiv-when-shape-eq
             shape-eq-dims2m!))

  (defruled shape-eq-equiv-append1
    (shape-eq-equiv (shp++ shape)
                    shape)
    :enable shape-eq-equiv
    :use (:instance shape-eq-append1 (shape (shape-fix shape))))

  (defruled shape-eq-equiv-append3m
    (implies (consp shapes)
             (shape-eq-equiv (shape-append (list* shape1 shape2 shapes))
                             (shape-append (cons (shp++ shape1 shape2)
                                                 shapes))))
    :enable (shape-eq-equiv-when-shape-eq
             shape-eq-append3m!))

  (defruled shape-eq-equiv-splice0
    (shape-eq-equiv (shp[])
                    (shp++))
    :enable (shape-eq-equiv-when-shape-eq
             shape-eq-splice0))

  (defruled shape-eq-equiv-splice1m-dim
    (implies (ispace-case ispace :dim)
             (shape-eq-equiv (shape-splice (cons ispace ispaces))
                             (shp++ (shp (ispace-dim->dim ispace))
                                    (shape-splice ispaces))))
    :enable shape-eq-equiv-when-shape-eq
    :use (:instance shape-eq-splice1m-dim! (dim (ispace-dim->dim ispace))))

  (defruled shape-eq-equiv-splice1m-shape
    (implies (ispace-case ispace :shape)
             (shape-eq-equiv (shape-splice (cons ispace ispaces))
                             (shp++ (ispace-shape->shape ispace)
                                    (shape-splice ispaces))))
    :enable shape-eq-equiv-when-shape-eq
    :use (:instance shape-eq-splice1m-shape!
                    (shape (ispace-shape->shape ispace))))

  (defruled shape-eq-equiv-append-assoc
    (shape-eq-equiv (shp++ (shp++ shape1 shape2) shape3)
                    (shp++ shape1 (shp++ shape2 shape3)))
    :enable (shape-eq-equiv-when-shape-eq
             shape-eq-append-assoc!))

  (defruled shape-eq-equiv-append-id-left
    (shape-eq-equiv (shp++ (shp++) shape)
                    shape)
    :enable shape-eq-equiv
    :use (:instance shape-eq-append-id-left (shape (shape-fix shape))))

  (defruled shape-eq-equiv-append-id-right
    (shape-eq-equiv (shp++ shape (shp++))
                    shape)
    :enable shape-eq-equiv
    :use (:instance shape-eq-append-id-right (shape (shape-fix shape))))

  (defruled ispace-eq-equiv-ispace-dim-shape
    (implies (ispace-case ispace :dim)
             (ispace-eq-equiv (ispace-shape (shp (ispace-dim->dim ispace)))
                              ispace))
    :enable (ispace-eq-equiv
             ispace-eq-symm!)
    :use (:instance ispace-eq-ispace-dim-shape!
                    (dim (ispace-dim->dim ispace))))

  ;; additional rules:

  (defruled shape-eq-equiv-dims-cons
    (implies (syntaxp (not (equal dims ''nil)))
             (shape-eq-equiv (shape-dims (cons dim dims))
                             (shp++ (shp dim) (shape-dims dims))))
    :use (:instance lemma (dims (dim-list-fix dims)))
    :prep-lemmas
    ((defruled lemma
       (implies (dim-listp dims)
                (shape-eq-equiv (shape-dims (cons dim dims))
                                (shp++ (shp dim) (shape-dims dims))))
       :cases ((consp dims))
       :enable (shape-eq-equiv-dims0
                shape-eq-equiv-dims2m
                shape-eq-equiv-append-id-right))))

  (local
   (defun shape-append-cons-induct (shape shapes)
     (declare (irrelevant shape))
     (cond ((not (consp shapes)) nil)
           ((not (consp (cdr shapes))) nil)
           (t (list (shape-append-cons-induct (shp++ shape (car shapes))
                                              (cdr shapes))
                    (shape-append-cons-induct (car shapes)
                                              (cdr shapes)))))))

  (defruled shape-eq-equiv-append-cons
    (implies (syntaxp (not (or (equal shapes ''nil)
                               (and (consp shapes)
                                    (eq (car shapes) 'cons)
                                    (equal (caddr shapes) ''nil)))))
             (shape-eq-equiv (shape-append (cons shape shapes))
                             (shp++ shape (shape-append shapes))))
    :use (:instance lemma (shapes (shape-list-fix shapes)))
    :prep-lemmas
    ((defruled lemma
       (implies (shape-listp shapes)
                (shape-eq-equiv (shape-append (cons shape shapes))
                                (shp++ shape (shape-append shapes))))
       :induct (shape-append-cons-induct shape shapes)
       :enable (shape-eq-equiv-append1
                shape-eq-equiv-append3m
                shape-eq-equiv-append-assoc
                shape-eq-equiv-append-id-right))))

  (defruled shape-eq-equiv-splice-cons
    (implies (syntaxp (not (equal ispaces ''nil)))
             (shape-eq-equiv (shape-splice (cons ispace ispaces))
                             (shp++ (shape-splice (list ispace))
                                    (shape-splice ispaces))))
    :use (:instance ispace-kind-possibilities (x ispace))
    :enable (shape-eq-equiv-splice0
             shape-eq-equiv-splice1m-dim
             shape-eq-equiv-splice1m-shape
             shape-eq-equiv-append-id-right))

  (defruled shape-eq-equiv-append-of-append
    (shape-eq-equiv (shape-append (append shapes1 shapes2))
                    (shp++ (shape-append shapes1) (shape-append shapes2)))
    :use (:instance lemma (shapes1 (shape-list-fix shapes1)))
    :prep-lemmas
    ((defruled lemma
       (implies (shape-listp shapes1)
                (shape-eq-equiv (shape-append (append shapes1 shapes2))
                                (shp++ (shape-append shapes1)
                                       (shape-append shapes2))))
       :induct t
       :enable (append
                shape-eq-equiv-append-cons
                shape-eq-equiv-append-assoc
                shape-eq-equiv-append-id-left))))

  (defruled shape-eq-equiv-dims-when-not-consp
    (implies (not (consp dims))
             (shape-eq-equiv (shape-dims dims)
                             (shp++)))
    :enable shape-eq-equiv-dims0
    :use ((:instance dims-eq-equiv-implies-shape-eq-equiv-shape-dims-1
                     (dims-equiv nil))
          dims-eq-equiv-of-nil-when-not-consp))

  (defruled shape-eq-equiv-append-when-not-consp
    (implies (and (syntaxp (not (equal shapes ''nil)))
                  (not (consp shapes)))
             (shape-eq-equiv (shape-append shapes)
                             (shp++)))
    :use ((:instance shapes-eq-equiv-implies-shape-eq-equiv-shape-append-1
                     (shapes-equiv nil))
          shapes-eq-equiv-of-nil-when-not-consp))

  (defruled shape-eq-equiv-splice-when-not-consp
    (implies (not (consp ispaces))
             (shape-eq-equiv (shape-splice ispaces)
                             (shp++)))
    :enable shape-eq-equiv-splice0
    :use ((:instance ispaces-eq-equiv-implies-shape-eq-equiv-shape-splice-1
                     (ispaces-equiv nil))
          ispaces-eq-equiv-of-nil-when-not-consp))

  ;; rule set:

  (acl2::def-ruleset shape-eq-equiv-rules
    '(shape-eq-equiv-dims0
      shape-eq-equiv-dims2m
      shape-eq-equiv-append1
      shape-eq-equiv-splice0
      shape-eq-equiv-splice1m-dim
      shape-eq-equiv-splice1m-shape
      shape-eq-equiv-append-assoc
      shape-eq-equiv-append-id-left
      shape-eq-equiv-append-id-right)))
