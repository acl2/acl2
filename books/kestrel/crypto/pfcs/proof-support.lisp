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

(local (in-theory (disable primep)))

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
     needs the deeply embedded semantics.
     The reason is that we can define an ACL2 function
     that takes the parameters as inputs
     and returns the corresponding gadget in PFCS abstract syntax,
     whose properties we can then prove,
     universally quantified over the parameters
     (perhaps with some restrictions on the parameters).
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
     and returns an assertion for a single list of constraints,
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
           (b* ((left (constraint-equal->left constr))
                (right (constraint-equal->right constr)))
             (iff (constraint-satp asg constr defs p)
                  (and (equal (eval-expr left asg p)
                              (eval-expr right asg p))
                       (eval-expr left asg p)))))
  :use (only-if-direction if-direction)

  :prep-lemmas
  ((defruled only-if-direction
     (implies (constraint-case constr :equal)
              (b* ((left (constraint-equal->left constr))
                   (right (constraint-equal->right constr)))
                (implies (constraint-satp asg constr defs p)
                         (and (equal (eval-expr left asg p)
                                     (eval-expr right asg p))
                              (eval-expr left asg p)))))
     :enable constraint-satp
     :use (:instance exec-proof-tree-when-constraint-equal
           (ptree (constraint-satp-witness asg constr defs p))))

   (defruled if-direction
     (implies (and (assignment-for-prime-p asg p)
                   (constraint-case constr :equal))
              (b* ((left (constraint-equal->left constr))
                   (right (constraint-equal->right constr)))
                (implies (and (equal (eval-expr left asg p)
                                     (eval-expr right asg p))
                              (eval-expr left asg p))
                         (constraint-satp asg constr defs p))))
     :use (:instance constraint-satp-suff
           (ptree (make-proof-tree-equal
                   :asg asg
                   :left (constraint-equal->left constr)
                   :right (constraint-equal->right constr))))
     :enable exec-proof-tree)))
