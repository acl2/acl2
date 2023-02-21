; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-deep")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proof-support
  :parents (prime-field-constraint-systems)
  :short "Proof support for PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCSes representing specific gadgets can be reasoned about
     (to prove properties of them, such as compliance to specifications)
     using either the shallowly or deeply embedded semantics.
     Both work fine for the case of fixed, completely defined PFCSes.
     However, to reason about parameterized families of PFCSes,
     such as a gadget to decompose a number into a varying number of bits
     (where the number of bits is a parameter),
     or even more simply a gadget parameterized over
     the choice of names of its variables,
     the deeply embedded semantics ie needed.")
   (xdoc::p
    "The reason is that we can define an ACL2 function
     that takes the parameters as inputs
     and returns the corresponding gadget in PFCS abstract syntax,
     whose properties we can then prove,
     universally quantified over the parameters
     (possibly with some restrictions on the parameters).
     This is only possible in the deeply embedded semantics,
     which treats the PFCS abstract syntax explicitly.
     In contrast, the shallowly embedded semantics
     turns fixed instances of PFCS abstract syntax into ACL2 predicates,
     without an easy way to parameterize them.
     It may be possible to extend the shallowly embedded semantics
     to recognize and take into account certain forms of parameterized PFCS,
     or even extend PFCS with forms of parameterization.
     It may be also possible to define ACL2 functions
     that generate both PFCS abstract syntax and associated proofs,
     based on the kind of parameters mentioned above.
     But for now,
     with PFCS and their shallowly embedded semantics being what they are,
     the deeply embedded semantics must be used
     to reason about parameterized PFCSes.")
   (xdoc::p
    "However, the (deeply embedded) semantics of PFCSes is somewhat complicated,
     defined in terms of
     existentially quantified proof trees and their execution.
     The reason for that complication is discussed
     in @(see semantics-deeply-embedded).
     The complication extends to attempts to reason about PFCSes
     (whether parameterized or not)
     directly in terms of the defined semantics.")
   (xdoc::p
    "Fortunately, it should be possible to prove rules
     that facilitate reasoning with the deeply embedded semantics.
     These rules let us avoid dealing explcitly with proof trees.
     These rules are work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-proof-tree-when-constraint-equal
  :short "Characterization of a proof tree for an equality constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "If running a proof tree is successful
     and returns an assertion for an equality constraint,
     then the proof tree must be one for an equality,
     and its components (assignment and expressions)
     must coincide with the ones from the assertion.")
   (xdoc::p
    "This is used to prove @(tsee constraint-satp-of-equal)."))
  (b* ((outcome (exec-proof-tree ptree defs p)))
    (implies
     (proof-outcome-case outcome :assertion)
     (b* ((asser (proof-outcome-assertion->get outcome))
          (asg (assertion->asg asser))
          (constr (assertion->constr asser)))
       (implies (constraint-case constr :equal)
                (and (proof-tree-case ptree :equal)
                     (equal (proof-tree-equal->asg ptree)
                            asg)
                     (equal (proof-tree-equal->left ptree)
                            (constraint-equal->left constr))
                     (equal (proof-tree-equal->right ptree)
                            (constraint-equal->right constr))
                     (equal (eval-expr (constraint-equal->left constr) asg p)
                            (eval-expr (constraint-equal->right constr) asg p))
                     (eval-expr (constraint-equal->left constr) asg p))))))
  :expand ((exec-proof-tree ptree defs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-proof-tree-when-constraint-relation
  :short "Characterization of a proof tree for a relation constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "If running a proof tree is successful
     and returns an assertion for a relation constraint,
     then the proof tree must be one for a relation application,
     and it has to satisfy a number of other requirements,
     explicated in this theorem.")
   (xdoc::p
    "This is used to prove @(tsee constraint-satp-of-relation."))
  (b* ((outcome (exec-proof-tree ptree defs p))
       (asser (proof-outcome-assertion->get outcome))
       (asg (assertion->asg asser))
       (constr (assertion->constr asser))
       (name (constraint-relation->name constr))
       (args (constraint-relation->args constr))
       (def (lookup-definition name defs))
       (para (definition->para def))
       (body (definition->body def))
       ((mv okp vals) (eval-expr-list args asg p))
       (asgext (proof-tree-relation->asgext ptree))
       (outcome-sub (exec-proof-tree-list
                     (proof-tree-relation->sub ptree) defs p))
       (asser-sub (proof-list-outcome-assertions->get outcome-sub)))
    (implies (and (proof-outcome-case outcome :assertion)
                  (constraint-case constr :relation))
             (and (proof-tree-case ptree :relation)
                  (equal (proof-tree-relation->asg ptree) asg)
                  (equal (proof-tree-relation->name ptree) name)
                  (equal (proof-tree-relation->args ptree) args)
                  def
                  okp
                  (equal (len para) (len vals))
                  (assignment-for-prime-p asgext p)
                  (omap::submap (omap::from-lists para vals) asgext)
                  (proof-list-outcome-case outcome-sub :assertions)
                  (equal (assertion-list->asg-list asser-sub)
                         (repeat (len body) asgext))
                  (equal (assertion-list->constr-list asser-sub)
                         body))))
  :expand ((exec-proof-tree ptree defs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-satp-of-equal
  :short "Proof rule for equality constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the satisfaction of an equality constraint
     reduces to the two expressions being equal and non-erroneous.")
   (xdoc::p
    "This rule lets us dispense with the existentially quantified proof tree
     for the common case of equality constraints."))
  (implies (and (assignment-for-prime-p asg p)
                (constraint-case constr :equal))
           (iff (constraint-satp constr defs asg p)
                (b* ((left (constraint-equal->left constr))
                     (right (constraint-equal->right constr)))
                  (and (equal (eval-expr left asg p)
                              (eval-expr right asg p))
                       (eval-expr left asg p)))))
  :use (only-if-direction if-direction)

  :prep-lemmas
  ((defruled only-if-direction
     (implies (constraint-case constr :equal)
              (b* ((left (constraint-equal->left constr))
                   (right (constraint-equal->right constr)))
                (implies (constraint-satp constr defs asg p)
                         (and (equal (eval-expr left asg p)
                                     (eval-expr right asg p))
                              (eval-expr left asg p)))))
     :enable constraint-satp
     :use (:instance exec-proof-tree-when-constraint-equal
           (ptree (constraint-satp-witness constr defs asg p))))

   (defruled if-direction
     (implies (and (assignment-for-prime-p asg p)
                   (constraint-case constr :equal))
              (b* ((left (constraint-equal->left constr))
                   (right (constraint-equal->right constr)))
                (implies (and (equal (eval-expr left asg p)
                                     (eval-expr right asg p))
                              (eval-expr left asg p))
                         (constraint-satp constr defs asg p))))
     :use (:instance constraint-satp-suff
           (ptree (make-proof-tree-equal
                   :asg asg
                   :left (constraint-equal->left constr)
                   :right (constraint-equal->right constr))))
     :enable exec-proof-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-relation-satp ((name symbolp)
                                     (args expression-listp)
                                     (defs definition-listp)
                                     (asg assignmentp)
                                     (p primep))
  :guard (assignment-for-prime-p asg p)
  :returns (yes/no booleanp)
  :short "Satisfaction of a relation constraint,
          expressed without proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like an alternative definition of @(tsee constraint-satp)
     for the case in which the constraint is an application of a relation.
     We prove below its equivalence to @(tsee constraint-satp).")
   (xdoc::p
    "This is a simpler definition,
     because it does not directly involve the execution of proof trees.
     It says that the relation application is satisfied
     exactly when there exists an assignment
     that extends the one binding the relation's parameters
     to the values of the arguments,
     and that satisfies all the relation's constraints."))
  (exists
   (asgext)
   (and (assignmentp asgext)
        (assignment-for-prime-p asgext p)
        (b* ((def (lookup-definition name defs)))
          (and def
               (b* (((definition def) def))
                 (and (equal (len args) (len def.para))
                      (b* (((mv okp vals) (eval-expr-list args asg p)))
                        (and okp
                             (omap::submap (omap::from-lists def.para vals)
                                           asgext)
                             (constraint-list-satp def.body
                                                   defs
                                                   asgext
                                                   p))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-satp-of-relation
  :short "Proof rule for relation application constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the satisfaction of a relation application constraint
     reduces to @(tsee constraint-relation-satp).")
   (xdoc::p
    "This rule lets us dispense with the existentially quantified proof tree,
     limiting the existential quantification to the extended assignment
     in @(tsee constraint-relation-satp).
     Some existential quantification is unavoidable in general,
     but the one for the extended assignment
     is simpler to handle than the one for the whole proof tree."))
  (implies (and (assignmentp asg)
                (assignment-for-prime-p asg p)
                (constraint-case constr :relation))
           (equal (constraint-satp constr defs asg p)
                  (constraint-relation-satp (constraint-relation->name constr)
                                            (constraint-relation->args constr)
                                            defs
                                            asg
                                            p)))
  :use (only-if-direction if-direction)

  :prep-lemmas

  ((defruled only-if-direction
     (implies (and (assignmentp asg)
                   (assignment-for-prime-p asg p)
                   (constraint-case constr :relation))
              (implies (constraint-satp constr defs asg p)
                       (constraint-relation-satp
                        (constraint-relation->name constr)
                        (constraint-relation->args constr)
                        defs
                        asg
                        p)))
     :enable constraint-satp
     :use ((:instance exec-proof-tree-when-constraint-relation
                      (ptree (constraint-satp-witness constr defs asg p)))
           (:instance constraint-relation-satp-suff
                      (name (constraint-relation->name constr))
                      (args (constraint-relation->args constr))
                      (asg (proof-tree-relation->asg
                            (constraint-satp-witness constr defs asg p)))
                      (asgext (proof-tree-relation->asgext
                               (constraint-satp-witness constr defs asg p))))
           (:instance constraint-list-satp-suff
                      (constrs (definition->body
                                 (lookup-definition
                                  (constraint-relation->name constr) defs)))
                      (asg (proof-tree-relation->asgext
                            (constraint-satp-witness constr defs asg p)))
                      (ptrees (proof-tree-relation->sub
                               (constraint-satp-witness constr defs asg p))))))

   (defruled if-direction
     (implies (and (assignmentp asg)
                   (assignment-for-prime-p asg p)
                   (constraint-case constr :relation))
              (implies (constraint-relation-satp
                        (constraint-relation->name constr)
                        (constraint-relation->args constr)
                        defs
                        asg
                        p)
                       (constraint-satp constr defs asg p)))
     :enable (constraint-relation-satp
              constraint-list-satp
              exec-proof-tree)
     :use (:instance constraint-satp-suff
                     (ptree (make-proof-tree-relation
                             :asg asg
                             :name (constraint-relation->name constr)
                             :args (constraint-relation->args constr)
                             :sub (constraint-list-satp-witness
                                   (definition->body
                                     (lookup-definition
                                      (constraint-relation->name constr) defs))
                                   defs
                                   (constraint-relation-satp-witness
                                    (constraint-relation->name constr)
                                    (constraint-relation->args constr)
                                    defs asg p)
                                   p)
                             :asgext (constraint-relation-satp-witness
                                      (constraint-relation->name constr)
                                      (constraint-relation->args constr)
                                      defs asg p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-atom
  :short "Proof rule for the empty list of constraints
          expressed as any atom."
  :long
  (xdoc::topstring
   (xdoc::p
    "The empty list of constraints is always satisfied.
     Indeed, lists of constraints are conjunctions.")
   (xdoc::p
    "Here we phrase the rule in terms of @(tsee atom)
     so that it is more generally applicable to proving other rules
     without having to require the list of constraints
     to be a true list (of constraints).
     The rule @(tsee constraint-list-satp-of-nil) is a specialized version
     for the case of an empty list expressed as @('nil')."))
  (implies (atom constrs)
           (constraint-list-satp constrs defs asg p))
  :enable (exec-proof-tree-list
           assertion-list-from)
  :use (:instance constraint-list-satp-suff (ptrees nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-nil
  :short "Proof rule for the empty list of constraint."
  (constraint-list-satp nil defs asg p)
  :enable constraint-list-satp-of-atom)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-cons
  :short "Proof rule for a @(tsee cons) list of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "The satisfaction of a @(tsee cons) list of constraints
     reduces to the satisfaction of the two constituents
     (the first constraint and the remaining list).")
   (xdoc::p
    "This is a key proof rule to decompose
     the satisfaction of lists of constraints
     into the satisfaction of their constituent constraints."))
  (equal (constraint-list-satp (cons constr constrs) defs asg p)
         (and (constraint-satp constr defs asg p)
              (constraint-list-satp constrs defs asg p)))
  :use (only-if-direction if-direction)

  :prep-lemmas

  ((defruled only-if-direction
     (implies (constraint-list-satp (cons constr constrs) defs asg p)
              (and (constraint-satp constr defs asg p)
                   (constraint-list-satp constrs defs asg p)))
     :expand ((constraint-list-satp (cons constr constrs) defs asg p)
              (exec-proof-tree-list (constraint-list-satp-witness
                                     (cons constr constrs) defs asg p)
                                    defs
                                    p))
     :cases ((consp (constraint-list-satp-witness
                     (cons constr constrs) defs asg p)))
     :use ((:instance constraint-satp-suff
                      (ptree (car (constraint-list-satp-witness
                                   (cons constr constrs) defs asg p))))
           (:instance constraint-list-satp-suff
                      (ptrees (cdr (constraint-list-satp-witness
                                    (cons constr constrs) defs asg p)))))
     :enable (exec-proof-tree-list
              assertion-list-from))

   (defruled if-direction
     (implies (and (constraint-satp constr defs asg p)
                   (constraint-list-satp constrs defs asg p))
              (constraint-list-satp (cons constr constrs) defs asg p))
     :expand ((constraint-satp constr defs asg p)
              (constraint-list-satp constrs defs asg p))
     :use (:instance constraint-list-satp-suff
                     (ptrees
                      (cons (constraint-satp-witness constr defs asg p)
                            (constraint-list-satp-witness constrs defs asg p)))
                     (constrs (cons constr constrs)))
     :enable (exec-proof-tree-list
              assertion-list-from))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-append
  (equal (constraint-list-satp (append constrs1 constrs2) defs asg p)
         (and (constraint-list-satp constrs1 defs asg p)
              (constraint-list-satp constrs2 defs asg p)))
  :enable (constraint-list-satp-of-cons
           constraint-list-satp-of-atom))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-rev
  (equal (constraint-list-satp (rev constrs) defs asg p)
         (constraint-list-satp constrs defs asg p))
  :enable (rev
           constraint-list-satp-of-atom
           constraint-list-satp-of-cons
           constraint-list-satp-of-append))
