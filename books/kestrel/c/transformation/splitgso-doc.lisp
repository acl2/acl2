; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ splitgso
  :parents (transformation-tools)
  :short "A transformation to split a global struct object."
  :long
  (xdoc::topstring
    (xdoc::evmac-section-intro
      (xdoc::p
        "This transformation targets a global struct object, i.e. a file-scope
         object, that has a struct type.  The transformation splits it into two
         objects, of two new struct types, each with a subset of the original
         struct members, which are divided between the two new struct types
         (and objects).  Member access expressions are replaced with new access
         expressions with the original object replaced with one of the new
         objects.  The transformation will fail if the original object appears
         in any other sorts of expressions.")
      (xdoc::p
        "We only aim to preserve functional equivalence (up to the obvious
         isomorphism of data representation between the original and split
         struct objects) between the original and transformed programs. No
         consideration is given to performance, which may be affected by
         padding, locality, etc."))
   (xdoc::evmac-section-form
     (xdoc::codeblock
       "(splitgso const-old"
       "          const-new"
       "          :object-name       ..."
       "          :split-members     ..."
       "          :object-filepath   ... ; optional"
       "          :new-object1       ... ; optional"
       "          :new-object2       ... ; optional"
       "          :new-type1         ... ; optional"
       "          :new-type2         ... ; optional"
       "  )"
      ))
   (xdoc::evmac-section-inputs
     (xdoc::desc
       "@('const-old')"
       (xdoc::p
         "Specifies the code to be transformed.")
       (xdoc::p
         "This must be a symbol that names an existing ACL2 constant
          that contains a  validated translation unit ensemble,
          i.e. a value of type @(tsee transunit-ensemble)
          resulting from "
         (xdoc::seetopic "c$::validator" "validation")
         ", and in particular containing "
         (xdoc::seetopic "c$::validation-information" "validation information")
         ". This constant could result from @(tsee c$::input-files),
          or from some other "
         (xdoc::seetopic "transformation-tools" "transformation")
         "."))
     (xdoc::desc
       "@('const-new')"
       (xdoc::p
         "Specifies the name of the constant for the transformed code.")
       (xdoc::p
         "This must be a symbol that is valid name for a new ACL2 constant."))
     (xdoc::desc
       "@(':object-name') &mdash; no default"
       (xdoc::p
         "A string denoting the identifier of the global struct object to
          split."))
     (xdoc::desc
       "@(':split-members') &mdash; no default"
       (xdoc::p
         "A string list denoting the identifiers representing the fields of the
          original struct type which should be \"split\" out into a new
          struct."))
     (xdoc::desc
       "@(':object-filepath') &mdash; optional"
       (xdoc::p
         "A string denoting the filepath of a translation unit. This is
          required when the target struct object has internal linkage in order
          to disambiguate the @(':object-name') argument."))
     (xdoc::desc
       "@(':new-object1') &mdash; optional"
       (xdoc::p
         "A string denoting the name of the first new struct object to be
          created. This object will possess the fields which are "
         (xdoc::i "not")
         " split out (i.e. not listed in the @(':split-members') argument).")
       (xdoc::p
         "If this argument is omitted, a fresh name will be inferred."))
     (xdoc::desc
       "@(':new-object2') &mdash; optional"
       (xdoc::p
         "A string denoting the name of the second new struct object to be
          created. This object will possess the fields which "
         (xdoc::i "are")
         " split out (i.e. listed in the @(':split-members') argument).")
       (xdoc::p
         "If this argument is omitted, a fresh name will be inferred."))
     (xdoc::desc
       "@(':new-type1') &mdash; optional"
       (xdoc::p
         "A string denoting the tag of the first new struct type to be
          created. This struct type will possess the fields which are "
         (xdoc::i "not")
         " split out (i.e. not listed in the @(':split-members') argument).")
       (xdoc::p
         "This represents the type of @(':new-object1').")
       (xdoc::p
         "If this argument is omitted, a fresh name will be inferred."))
     (xdoc::desc
       "@(':new-type2') &mdash; optional"
       (xdoc::p
         "A string denoting the tag of the second new struct type to be
          created. This struct type will possess the fields which "
         (xdoc::i "are")
         " split out (i.e. listed in the @(':split-members') argument).")
       (xdoc::p
         "This represents the type of @(':new-object2').")
       (xdoc::p
         "If this argument is omitted, a fresh name will be inferred.")))
   (xdoc::section
     "Constraints on the Input Code"
     (xdoc::ul
       (xdoc::li "The global struct object cannot occur in certain expressions
                  we deem \"illegal\". These are expressions which might
                  threaten the soundness of the transformation if they were
                  permitted. Any expression which includes a reference to the
                  global struct object which is not a member access is
                  considered illegal.")
       (xdoc::li "A member access of the global struct object cannot occur in
                  certain contexts. In particular, you cannot take the address
                  of the member access expression or the @('sizeof') the member
                  access; such expressions are illegal.")))
   (xdoc::section
     "Current Limitations"
     (xdoc::p
       "The following are temporary limitations which will hopefully be removed
        in the future with improvements to the implementation.")
    (xdoc::ul
     (xdoc::li "Fields in a struct type declaration must not share a type
                specification (e.g., @('int x, y;') is currently unsupported,
                where @('int x; int y;') <i>is</i> supported)")
     (xdoc::li "Similarly, struct object declarations must not share a type
                specification (e.g. @('struct myStruct foo, bar;') is currently
                unsupported, while @('struct myStruct foo; struct myStuct
                bar;') is allowed.)")
     (xdoc::li "The names of the new struct objects and their types are not yet
                checked for uniqueness/shadowing."))))
  :order-subtopics t)
