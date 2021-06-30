; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ well-formedness
  :parents (prime-field-constraint-systems)
  :short "Well-formedness of PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constraint in a PFCS that is not an equality,
     i.e. that is an application of a named relation to some expressions,
     must reference a relation that is defined in the PFCS,
     and the number of argument expressions
     must match the number of parameters of the named relation.
     No two distinct relations in a PFCS may have the same name.
     The parameters of a named relation definition must be unique.")
   (xdoc::p
    "All these well-formedness conditions are formalized here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-definition ((name symbolp) (sys systemp))
  :returns (def? definition-optionp)
  :short "Look up a definition in a system of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the system has a definition for the given name,
     return that definition.
     Otherwise return @('nil').")
   (xdoc::p
    "We return the first definition found for that name.
     In a well-formed system of constraints,
     there is at most a definition for each name,
     and thus returning the first one found is also the only one."))
  (b* (((when (endp sys)) nil)
       (def (car sys))
       ((when (eq (definition->name def)
                  (symbol-fix name)))
        (definition-fix def)))
    (lookup-definition name (cdr sys)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-wfp ((constr constraintp) (sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a constraint is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "An equality is always well-formed.
     An application of a named relation to some expressions is well-formed iff
     the relation is defined in the system
     and the number of argument expressions is the same as
     the number of formal parameters."))
  (constraint-case
   constr
   :equal t
   :relation (b* ((def? (lookup-definition constr.name sys)))
               (and (definitionp def?)
                    (= (len constr.args)
                       (len (definition->para def?))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-list-wfp ((constrs constraint-listp) (sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a list of constraints is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of constraints is well-formed iff
     all the constraints are well-formed."))
  (or (endp constrs)
      (and (constraint-wfp (car constrs) sys)
           (constraint-list-wfp (cdr constrs) sys)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-wfp ((def definitionp) (sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a definition is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is checked with respect to the system (i.e. definitions)
     that precedes the definition being checked
     in a larger system that includes the definition.
     That is, this predicate holds when the definition
     can be used to extend the system.
     See @(tsee system-wfp).")
   (xdoc::p
    "A definition is well-formed iff
     its constraints are all well-formed,
     its parameters are distinct,
     and the relation being defined is not already defined."))
  (b* (((definition def) def))
    (and (not (lookup-definition def.name sys))
         (no-duplicatesp-eq def.para)
         (constraint-list-wfp def.body sys)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-wfp ((sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a system is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The empty system is well-formed,
     and every well-formed system can be extended
     by adding a definition that is well-formed in that system.
     To iterate through the list more easily,
     we use an auxiliary function that operates on the reversed system."))
  (system-wfp-aux (rev (system-fix sys)))
  :prepwork
  ((define system-wfp-aux ((rev-sys systemp))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp rev-sys)
         (and (system-wfp-aux (cdr rev-sys))
              (definition-wfp (car rev-sys) (cdr rev-sys))))
     :hooks (:fix)))
  :hooks (:fix))
