; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics")

(local (include-book "oset-lib-ext"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proof-support
  :parents (pfcs)
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
     the deeply embedded semantics is needed.")
   (xdoc::p
    "The reason is that we can define an ACL2 function
     that takes the parameters as inputs
     and returns the corresponding gadget in PFCS abstract syntax,
     whose properties we can then prove,
     universally quantified over the aforementioned parameters
     (possibly with some restrictions on the parameters).
     This is only possible in the deeply embedded semantics,
     which treats the PFCS abstract syntax explicitly.
     In contrast, the shallowly embedded semantics
     turns fixed instances of PFCS abstract syntax into ACL2 predicates,
     without an easy way to parameterize them.
     It may be possible to extend the shallowly embedded semantics
     to recognize and take into account certain forms of parameterized PFCSes,
     or even extend PFCSes with forms of parameterization.
     It may be also possible to define ACL2 functions
     that generate both PFCS abstract syntax and associated proofs,
     based on the kind of parameters mentioned above.
     But for now,
     with PFCSes and their shallowly embedded semantics being what they are,
     the deeply embedded semantics must be used
     to reason about parameterized PFCSes.")
   (xdoc::p
    "However, the (deeply embedded) semantics of PFCSes is somewhat complicated,
     defined in terms of
     existentially quantified proof trees and their execution.
     The reason for that complication is discussed in @(see semantics).
     The complication burdens the task to reason about PFCSes
     (whether parameterized or not)
     directly in terms of the deeply embedded semantics.")
   (xdoc::p
    "Therefore, here we provide functions and theorems (rules)
     to facilitate reasoning with the deeply embedded semantics.
     These let us dispense with explicitly dealing with proof trees,
     and instead have essentially alternative definitions
     of semantic predicates like @(tsee constraint-satp)
     that are expressed in simpler terms than
     via existentially quantified proof trees.
     (These alternative definitions could not be used as actual definitions,
     because of the recursion and existential quantification issues
     discussed in @(see semantics).)")
   (xdoc::p
    "Currently we provide the following forms of proof support:")
   (xdoc::ul
    (xdoc::li
     "A rule @(tsee constraint-satp-of-equal),
      to rewrite @(tsee constraint-satp) over an equality constraint
      to an alternative definition @(tsee constraint-equal-satp),
      which is directly expressed in terms of
      the two expressions being equal and non-erroneous.")
    (xdoc::li
     "A rule @(tsee constraint-satp-of-relation),
      to rewrite @(tsee constraint-satp) over a relation application constraint
      to an alternative definition @(tsee constraint-relation-satp),
      which is directly expressed in terms of
      the satisfaction of the suitably instantiated body of the relation.")
    (xdoc::li
     "Rules that decompose @(tsee constraint-list-satp)
      into @(tsee constraint-satp) of the elements,
      specifically @(tsee constraint-list-satp-of-cons)
      and @(tsee constraint-list-satp-of-append),
      along with rules @(tsee constraint-list-satp-of-nil)
      and @(tsee constraint-list-satp-of-atom)
      to resolve empty lists of constraints as alwasy satisfied.
      We also have a rule @(tsee constraint-list-satp-of-rev)
      that simplifies @(tsee rev) away,
      since constraint satisfaction is not ordered-dependent.")
    (xdoc::li
     "A rule that turns @(tsee constraint-satp) of a relation constraint
      into @(tsee definition-satp) of the relation
      and of the values that the arguments evaluate to.
      This is useful for compositional proofs of PFCSes,
      because by reducing the satisfaction of an inner relation call,
      performed in the body of an outer relation,
      to the satisfaction of the definition of the inner relation,
      one can use properties proved about the inner relation
      to prove properties about the outer relation."))
   (xdoc::p
    "More proof rules may be added here in the future,
     but it should be clear from the list above
     that we already have rules to cover
     both kinds of single constraints
     as well as lists of constraints."))
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
                     (natp (eval-expr
                            (constraint-equal->left constr) asg p)))))))
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
    "This is used to prove @(tsee constraint-satp-of-relation)."))
  (b* ((outcome (exec-proof-tree ptree defs p))
       (asser (proof-outcome-assertion->get outcome))
       (asg (assertion->asg asser))
       (constr (assertion->constr asser))
       (name (constraint-relation->name constr))
       (args (constraint-relation->args constr))
       (def (lookup-definition name defs))
       (para (definition->para def))
       (body (definition->body def))
       (vals (eval-expr-list args asg p))
       (asgfree (proof-tree-relation->asgfree ptree))
       (asgpara (omap::from-lists para vals))
       (outcome-sub (exec-proof-tree-list
                     (proof-tree-relation->sub ptree) defs p))
       (asser-sub (proof-list-outcome-assertions->get outcome-sub))
       (asgsub (omap::update* asgfree asgpara)))
    (implies (and (proof-outcome-case outcome :assertion)
                  (constraint-case constr :relation))
             (and (proof-tree-case ptree :relation)
                  (equal (proof-tree-relation->asg ptree) asg)
                  (equal (proof-tree-relation->name ptree) name)
                  (equal (proof-tree-relation->args ptree) args)
                  def
                  (nat-listp vals)
                  (equal (len para) (len vals))
                  (assignment-wfp asgfree p)
                  (equal (omap::keys asgfree)
                         (definition-free-vars def))
                  (proof-list-outcome-case outcome-sub :assertions)
                  (equal (assertion-list->asg-list asser-sub)
                         (repeat (len body) asgsub))
                  (equal (assertion-list->constr-list asser-sub)
                         body))))
  :expand ((exec-proof-tree ptree defs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-equal-satp ((left expressionp)
                               (right expressionp)
                               (asg assignmentp)
                               (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Satisfaction of an equality constraint,
          expressed without proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an alternative definition of @(tsee constraint-satp)
     for the case in which the constrains is an equality.
     We prove in @(tsee constraint-satp-of-equal)
     its equivalence to @(tsee constraint-satp).")
   (xdoc::p
    "This is a simpler definition,
     because it does not directly involve the execution of proof trees.
     It says that the equality is satisfied
     exactly when the two expressions are equal and non-erroneous."))
  (and (natp (eval-expr left asg p))
       (equal (eval-expr left asg p)
              (eval-expr right asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-satp-of-equal
  :short "Proof rule for equality constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This says that the satisfaction of an equality constraint
     reduces to the two expressions being equal and non-erroneous.")
   (xdoc::p
    "This rule lets us dispense with the existentially quantified proof tree
     for the case of equality constraints."))
  (implies (and (assignment-wfp asg p)
                (constraint-case constr :equal))
           (equal (constraint-satp constr defs asg p)
                  (constraint-equal-satp (constraint-equal->left constr)
                                         (constraint-equal->right constr)
                                         asg
                                         p)))
  :use (only-if-direction if-direction)

  :prep-lemmas
  ((defruled only-if-direction
     (implies (constraint-case constr :equal)
              (implies (constraint-satp constr defs asg p)
                       (constraint-equal-satp (constraint-equal->left constr)
                                              (constraint-equal->right constr)
                                              asg
                                              p)))
     :enable (constraint-satp
              constraint-equal-satp)
     :use (:instance exec-proof-tree-when-constraint-equal
                     (ptree (constraint-satp-witness constr defs asg p))))

   (defruled if-direction
     (implies (and (assignment-wfp asg p)
                   (constraint-case constr :equal))
              (implies (constraint-equal-satp (constraint-equal->left constr)
                                              (constraint-equal->right constr)
                                              asg
                                              p)
                       (constraint-satp constr defs asg p)))
     :enable (exec-proof-tree
              constraint-equal-satp)
     :use (:instance constraint-satp-suff
                     (ptree (make-proof-tree-equal
                             :asg asg
                             :left (constraint-equal->left constr)
                             :right (constraint-equal->right constr)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk constraint-relation-satp ((name stringp)
                                     (args expression-listp)
                                     (defs definition-listp)
                                     (asg assignmentp)
                                     (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Satisfaction of a relation constraint,
          expressed without proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an alternative definition of @(tsee constraint-satp)
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
   (asgfree)
   (and (assignmentp asgfree)
        (assignment-wfp asgfree p)
        (b* ((def (lookup-definition name defs)))
          (and def
               (b* (((definition def) def))
                 (and (equal (len args) (len def.para))
                      (b* ((vals (eval-expr-list args asg p)))
                        (and (nat-listp vals)
                             (b* ((asg-para-vals (omap::from-lists def.para
                                                                   vals)))
                               (and (equal (omap::keys asgfree)
                                           (definition-free-vars def))
                                    (b* ((asg-sub (omap::update*
                                                   asgfree
                                                   asg-para-vals)))
                                      (constraint-list-satp def.body
                                                            defs
                                                            asg-sub
                                                            p))))))))))))
  :guard-hints (("Goal" :in-theory (enable acl2::not-reserrp-when-nat-listp))))

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
                (assignment-wfp asg p)
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
                   (assignment-wfp asg p)
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
                      (asgfree (proof-tree-relation->asgfree
                                (constraint-satp-witness constr defs asg p))))
           (:instance constraint-list-satp-suff
                      (constrs (definition->body
                                 (lookup-definition
                                  (constraint-relation->name constr) defs)))
                      (asg (omap::update*
                            (proof-tree-relation->asgfree
                             (constraint-satp-witness constr defs asg p))
                            (omap::from-lists
                             (definition->para
                               (lookup-definition
                                (constraint-relation->name constr) defs))
                             (eval-expr-list
                              (proof-tree-relation->args
                               (constraint-satp-witness constr defs asg p))
                              (proof-tree-relation->asg
                               (constraint-satp-witness constr defs asg p))
                              p))))
                      (ptrees (proof-tree-relation->sub
                               (constraint-satp-witness constr defs asg p))))))

   (defruled if-direction
     (implies (and (assignmentp asg)
                   (assignment-wfp asg p)
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
              exec-proof-tree
              nfix
              min)
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
                                   (omap::update*
                                    (constraint-relation-satp-witness
                                     (constraint-relation->name constr)
                                     (constraint-relation->args constr)
                                     defs asg p)
                                    (omap::from-lists
                                     (definition->para
                                       (lookup-definition
                                        (constraint-relation->name constr)
                                        defs))
                                     (eval-expr-list
                                      (constraint-relation->args constr)
                                      asg p)))
                                   p)
                             :asgfree (constraint-relation-satp-witness
                                       (constraint-relation->name constr)
                                       (constraint-relation->args constr)
                                       defs asg p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-relation-nofreevars-satp ((name stringp)
                                             (args expression-listp)
                                             (defs definition-listp)
                                             (asg assignmentp)
                                             (p primep))
  :guard (assignment-wfp asg p)
  :returns (yes/no booleanp)
  :short "Satisfaction of a relation constraint without free variables,
          expressed without proof trees."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialized version of @(tsee constraint-relation-satp),
     applicable when the definition of the relation has no free variables.
     In this case, we can avoid the existential quantification."))
  (b* ((def (lookup-definition name defs)))
    (and def
         (set::emptyp (definition-free-vars def))
         (b* (((definition def) def))
           (and (equal (len args) (len def.para))
                (b* ((vals (eval-expr-list args asg p)))
                  (and (nat-listp vals)
                       (b* ((asg-para-vals (omap::from-lists def.para vals)))
                         (constraint-list-satp def.body
                                               defs
                                               asg-para-vals
                                               p))))))))
  :guard-hints (("Goal" :in-theory (enable acl2::not-reserrp-when-nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-satp-of-relation-when-nofreevars
  :short "Proof rule for relation application constraints,
          for the case in which the relation has no free variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialized version of @(tsee constraint-satp-of-relation),
     applicable when the definition of the relation has no free variables.
     In this case, we can rewrite the satisfaction to
     the function @(tsee constraint-relation-nofreevars-satp),
     which avoids the existential quantification."))
  (implies (and (assignmentp asg)
                (assignment-wfp asg p)
                (constraint-case constr :relation))
           (b* ((name (constraint-relation->name constr))
                (args (constraint-relation->args constr))
                (def (lookup-definition name defs)))
             (implies (and def
                           (set::emptyp (definition-free-vars def)))
                      (equal (constraint-satp constr defs asg p)
                             (constraint-relation-nofreevars-satp name
                                                                  args
                                                                  defs
                                                                  asg
                                                                  p)))))
  :use (only-if-direction if-direction)

  :prep-lemmas

  ((defrule only-if-direction
     (implies (and (assignmentp asg)
                   (assignment-wfp asg p)
                   (constraint-case constr :relation))
              (b* ((name (constraint-relation->name constr))
                   (args (constraint-relation->args constr))
                   (def (lookup-definition name defs)))
                (implies (and def
                              (set::emptyp (definition-free-vars def)))
                         (implies (constraint-satp constr defs asg p)
                                  (constraint-relation-nofreevars-satp name
                                                                       args
                                                                       defs
                                                                       asg
                                                                       p)))))
     :rule-classes nil
     :enable (constraint-satp-of-relation
              constraint-relation-satp
              constraint-relation-nofreevars-satp
              set::emptyp
              omap::keys-iff-not-emptyp))

   (defrule if-direction
     (implies (and (assignmentp asg)
                   (assignment-wfp asg p)
                   (constraint-case constr :relation))
              (b* ((name (constraint-relation->name constr))
                   (args (constraint-relation->args constr))
                   (def (lookup-definition name defs)))
                (implies (and def
                              (set::emptyp (definition-free-vars def)))
                         (implies (constraint-relation-nofreevars-satp name
                                                                       args
                                                                       defs
                                                                       asg
                                                                       p)
                                  (constraint-satp constr defs asg p)))))
     :rule-classes nil
     :enable (constraint-relation-nofreevars-satp
              constraint-satp-of-relation
              definition-free-vars
              set::not-difference-when-subset)
     :use (:instance constraint-relation-satp-suff
                     (name (constraint-relation->name constr))
                     (args (constraint-relation->args constr))
                     (asgfree nil)))))

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
              assertion-list-from
              len))

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
              assertion-list-from
              len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-append
  :short "Proof rule for the concatenation of lists of constraints."
  (equal (constraint-list-satp (append constrs1 constrs2) defs asg p)
         (and (constraint-list-satp constrs1 defs asg p)
              (constraint-list-satp constrs2 defs asg p)))
  :induct t
  :enable (append
           constraint-list-satp-of-cons
           constraint-list-satp-of-atom))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-list-satp-of-rev
  :short "Proof rule for a reversed list of constraints."
  (equal (constraint-list-satp (rev constrs) defs asg p)
         (constraint-list-satp constrs defs asg p))
  :induct t
  :enable (rev
           constraint-list-satp-of-atom
           constraint-list-satp-of-cons
           constraint-list-satp-of-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled constraint-satp-to-definition-satp
  :short "Proof rule to turn relation constraint satisfaction
          to definition satisfaction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is useful for compostional reasoning,
     as mentioned in @(see proof-support)."))
  (implies (and (primep p)
                (assignmentp asg)
                (assignment-wfp asg p)
                (constraint-case constr :relation)
                (no-duplicatesp-equal (definition->para
                                        (lookup-definition
                                         (constraint-relation->name constr)
                                         defs))))
           (b* ((vals (eval-expr-list (constraint-relation->args constr)
                                      asg
                                      p)))
             (implies (not (reserrp vals))
                      (equal (constraint-satp constr defs asg p)
                             (definition-satp
                               (constraint-relation->name constr)
                               defs
                               vals
                               p)))))
  :use (only-if-part if-part)

  :prep-lemmas

  ((defruled only-if-part
     (implies (and (primep p)
                   (assignmentp asg)
                   (assignment-wfp asg p)
                   (constraint-case constr :relation)
                   (no-duplicatesp-equal (definition->para
                                          (lookup-definition
                                           (constraint-relation->name constr)
                                           defs))))
              (b* ((vals (eval-expr-list (constraint-relation->args constr)
                                         asg
                                         p)))
                (implies (not (reserrp vals))
                         (implies (constraint-satp constr defs asg p)
                                  (definition-satp
                                    (constraint-relation->name constr)
                                    defs
                                    vals
                                    p)))))
     :enable (constraint-satp-of-relation
              definition-satp
              eval-expr-list-of-expression-var-list-and-omap-from-lists)
     :expand (constraint-relation-satp (constraint-relation->name constr)
                                       (constraint-relation->args constr)
                                       defs asg p)
     :use (:instance constraint-relation-satp-suff
                     (name (constraint-relation->name constr))
                     (args (expression-var-list
                            (definition->para (lookup-definition
                                               (constraint-relation->name constr)
                                               defs))))
                     (defs defs)
                     (asg (omap::from-lists
                           (definition->para (lookup-definition
                                              (constraint-relation->name constr)
                                              defs))
                           (eval-expr-list (constraint-relation->args constr)
                                           asg p)))
                     (asgfree (constraint-relation-satp-witness
                               (constraint-relation->name constr)
                               (constraint-relation->args constr)
                               defs asg p))))

   (defruled if-part
     (implies (and (primep p)
                   (assignmentp asg)
                   (assignment-wfp asg p)
                   (constraint-case constr :relation)
                   (no-duplicatesp-equal (definition->para
                                          (lookup-definition
                                           (constraint-relation->name constr)
                                           defs))))
              (b* ((vals (eval-expr-list (constraint-relation->args constr)
                                         asg
                                         p)))
                (implies (not (reserrp vals))
                         (implies (definition-satp
                                    (constraint-relation->name constr)
                                    defs
                                    vals
                                    p)
                                  (constraint-satp constr defs asg p)))))
     :enable (constraint-satp-of-relation
              definition-satp
              acl2::nat-listp-when-nat-list-resultp-and-not-reserrp
              eval-expr-list-of-expression-var-list-and-omap-from-lists)
     :expand (constraint-relation-satp
              (constraint-relation->name constr)
              (expression-var-list
               (definition->para (lookup-definition
                                  (constraint-relation->name constr)
                                  defs)))
              defs
              (omap::from-lists
               (definition->para (lookup-definition
                                  (constraint-relation->name constr)
                                  defs))
               (eval-expr-list (constraint-relation->args constr)
                               asg p))
              p)
     :use (:instance constraint-relation-satp-suff
                     (name (constraint-relation->name constr))
                     (args (constraint-relation->args constr))
                     (defs defs)
                     (asg asg)
                     (asgfree (constraint-relation-satp-witness
                               (constraint-relation->name constr)
                               (expression-var-list
                                (definition->para
                                  (lookup-definition
                                   (constraint-relation->name constr)
                                   defs)))
                               defs
                               (omap::from-lists
                                (definition->para
                                  (lookup-definition
                                   (constraint-relation->name constr)
                                   defs))
                                (eval-expr-list
                                 (constraint-relation->args constr)
                                 asg
                                 p))
                               p))))))
