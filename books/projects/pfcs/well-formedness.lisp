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

(include-book "abstract-syntax-operations")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ well-formedness
  :parents (pfcs)
  :short "Well-formedness of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A constraint that is not an equality,
     i.e. that is an application of a named relation to some expressions,
     must reference a defined relation,
     and the number of argument expressions
     must match the number of parameters of the named relation.
     No two distinct relations may have the same name.
     The parameters of a named relation definition must be unique.")
   (xdoc::p
    "All these well-formedness conditions are formalized here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-wfp ((constr constraintp) (defs definition-listp))
  :returns (yes/no booleanp)
  :short "Check if a constraint is well-formed,
          with respect to a list of relation definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "An equality is always well-formed.
     An application of a named relation to some expressions is well-formed iff
     the relation is defined in the list of defined relations
     and the number of argument expressions is the same as
     the number of formal parameters."))
  (constraint-case
   constr
   :equal t
   :relation (b* ((def? (lookup-definition constr.name defs)))
               (and (definitionp def?)
                    (= (len constr.args)
                       (len (definition->para def?))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define constraint-list-wfp ((constrs constraint-listp) (defs definition-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of constraints is well-formed,
          with respect to a list of relation definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of constraints is well-formed iff
     all the constraints are well-formed."))
  (or (endp constrs)
      (and (constraint-wfp (car constrs) defs)
           (constraint-list-wfp (cdr constrs) defs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-wfp ((def definitionp) (defs definition-listp))
  :returns (yes/no booleanp)
  :short "Check if a definition is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is checked with respect to definitions
     that precede the definition being checked
     in a larger list that includes the definition.
     That is, this predicate holds when the definition
     can be used to extend the list.
     See @(tsee definition-list-wfp).")
   (xdoc::p
    "A definition is well-formed iff
     its constraints are all well-formed,
     its parameters are distinct,
     and the relation being defined is not already defined."))
  (b* (((definition def) def))
    (and (not (lookup-definition def.name defs))
         (no-duplicatesp-equal def.para)
         (constraint-list-wfp def.body defs)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definition-list-wfp ((defs definition-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of definitions is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The empty list of definitions is well-formed,
     and every well-formed list of definitions can be extended
     by adding a definition that is well-formed with respect to that list.
     To iterate through the list more naturally,
     we use an auxiliary function that operates on the reversed list."))
  (definition-list-wfp-aux (rev defs))
  :prepwork
  ((define definition-list-wfp-aux ((rev-defs definition-listp))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp rev-defs)
         (and (definition-list-wfp-aux (cdr rev-defs))
              (definition-wfp (car rev-defs) (cdr rev-defs))))
     :hooks (:fix)))
  ///
  (fty::deffixequiv definition-list-wfp
    :hints (("Goal" :in-theory (enable rev-of-definition-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-wfp ((sys systemp))
  :returns (yes/no booleanp)
  :short "Check if a system is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list of definitions must be well-formed,
     and the list of constraints must be well-formed
     with respect to the list of definitions."))
  (b* (((system sys) sys))
    (and (definition-list-wfp sys.definitions)
         (constraint-list-wfp sys.constraints sys.definitions)))
  :hooks (:fix))
