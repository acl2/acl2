#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(include-book "defdoc")

(def::doc RULE-SETS

  :one-liner "Machinery for organizing and versioning dynamic
sets of rules"

  :details (docstring (\n)
"  ACL2 enables users to define named collections of rules,
"(docref"theories")", that can be used in conjunction with
"(docref"in-theory")" events to manage the theory state of ACL2.
Defining a theory, however, requires that all of the rules in the
theory be known at the point at which the theory is defined.

  RULE-SETS enable users to define named collections of rules 
(RULE-SETS) and to incrementally modify that collection as necessary
to maintain a desired theory philosophy.

  Each rule set is associated with a particular set name as well as a
collection of versions.  Set names and versions may be any eqlablep
object.  For example, the rule set:

  `(zed . alpha)

  Refers to the alpha version of rule set zed.

  Rule sets are expected to have applications in both theory
management and library development.  

  Library developers will want to use rule sets to isolate different
proof styles as well as different classes of rules.  It seems unlikely
that one would want to version rule classes used in this style unless,
perhaps, it were to support a proof methodology such as phased
rewriting.

  Libraries themselves should be associated with umbrella rule classes
that cover all of the crucial functions and theories developed within
the library.  Here, versioning is the key to robust proof development
in the face of library extensions.  When a library is released, it
should be done so under a specific version tag.  Subsequent extensions
of that library should be performed under different version tags.

  Library rule classes should be orthoganal to methodological rule
classes.

  It is possible to classify a given rule under several different rule
classes.  Every classified rule is classified under a specific library
(by default).  It may also be classified under one or more
methodological rule classes.

  "(docref"def::rule-set")"

"))

(def::doc def::rule-set

  :one-liner "A macro for defining a new rule set"

  :details (docstring (\n)

"New rule sets can be defined using def::rule-set."))

