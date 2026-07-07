; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ struct-type-split
  :parents (transformation-tools)
  :short "A C-to-C transformation to split a struct type."
  :long
  (xdoc::topstring
   (xdoc::evmac-section-intro
    (xdoc::p
     "This transformation targets a struct type, identified by its tag.
      The transformation splits it into two struct types:
      the \"left\" struct type keeps the original tag
      and the members not selected for splitting,
      while the new \"right\" struct type receives a new tag
      and the selected members.
      Objects of the struct type are split into two objects accordingly,
      with declarations, initializers, and member access expressions
      routed to the appropriate side.
      Members of other struct types that have it (possibly behind pointers)
      as their type are likewise split in place into a left and a right member,
      while the containing struct types are otherwise left unchanged.
      Struct types with the same tag in other translation units
      which are compatible with the targeted struct type
      are also split, consistently,
      so that corresponding objects in different translation units
      (e.g. declarations of the same external object)
      receive the same new names.")
    (xdoc::p
     "We only aim to preserve functional equivalence (up to the obvious
      isomorphism of data representation between the original and split
      struct types) between the original and transformed programs. No
      consideration is given to performance, which may be affected by
      padding, locality, etc."))
   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(struct-type-split const-old"
     "                   const-new"
     "                   :struct-tag    ..."
     "                   :right-members ..."
     "                   :filepath      ... ; optional"
     "                   :new-tag       ... ; optional"
     "                   :print-warnings ... ; default t"
     "  )"
     ))
   (xdoc::evmac-section-inputs
    (xdoc::desc
     "@('const-old')"
     (xdoc::p
      "Specifies the code to be transformed.")
     (xdoc::p
      "This must be a symbol that names an existing ACL2 constant
       that contains a validated code ensemble,
       i.e. a value of type @(tsee code-ensemble)
       whose translation ensemble results from "
      (xdoc::seetopic "c$::validator" "validation")
      ", and in particular containing "
      (xdoc::seetopic "c$::validation-annotations" "validation information")
      ". This constant could result from @(tsee c$::input-files),
      or from some other "
      (xdoc::seetopic "transformation-tools" "transformation")
      "."))
    (xdoc::desc
     "@('const-new')"
     (xdoc::p
      "Specifies the name of the constant for the transformed code.")
     (xdoc::p
      "This must be a symbol that is valid name for a new ACL2 constant.")
     (xdoc::p
      "The transformed code is re-validated by the transformation,
       so its validation information is refreshed
       and may be used further."))
    (xdoc::desc
     "@(':struct-tag') &mdash; no default"
     (xdoc::p
      "A string denoting the tag of the struct type to split.
       The struct type must be defined at file scope."))
    (xdoc::desc
     "@(':right-members') &mdash; no default"
     (xdoc::p
      "A non-empty string list denoting the members of the struct type
       which should be split out into the new right struct type.
       The remaining members stay in the left struct type,
       which keeps the original tag."))
    (xdoc::desc
     "@(':filepath') &mdash; optional"
     (xdoc::p
      "A string denoting the filepath of a translation unit,
       in which the struct type denoted by @(':struct-tag')
       is to be found.
       This may be used to disambiguate the @(':struct-tag') argument
       when incompatible struct types in different translation units
       share the tag.
       If this argument is omitted, the first translation unit
       with a struct type with the given tag at file scope is used."))
    (xdoc::desc
     "@(':new-tag') &mdash; optional"
     (xdoc::p
      "A string denoting the tag of the new right struct type.
       A fresh tag is derived from it if it is not already fresh.")
     (xdoc::p
      "If this argument is omitted,
       a fresh tag is derived from the original tag."))
    (xdoc::desc
     "@(':print-warnings') &mdash; default @('t')"
     (xdoc::p
      "A boolean indicating whether warnings encountered
       during the transformation should be printed.")))
   (xdoc::section
    "Constraints on the Input Code"
    (xdoc::ul
     (xdoc::li
      "The struct type may appear in the type of
       an object, parameter, or type name
       only as the struct type itself, possibly behind pointers.
       Function parameters of such types are supported,
       and are split in place,
       in function definitions, function declarations, and call sites.
       The struct type may not appear in an array type
       or a function return type;
       such occurrences are detected and reported as errors.")
     (xdoc::li
      "A member of another struct type whose type is splittable
       (the struct type itself, possibly behind pointers) is supported:
       each such member is split in place into a left and a right member,
       in the definition of the containing struct type
       and in its initializers and member access expressions.
       The containing struct type may be tagged or untagged
       (e.g. defined via a typedef),
       and the member may be promoted from an anonymous struct member,
       in which case the split members are registered under,
       and promoted into, the enclosing struct type.
       A struct type that contains the split struct type only transitively,
       through a member of another struct type,
       is left unchanged.
       The struct type may not, however,
       be a member of a union type
       (whether directly or as an anonymous union member),
       or be a member of itself (i.e. be self-referential);
       such occurrences are detected and reported as errors.")
     (xdoc::li
      "Typedefs whose denoted type is splittable
       (the struct type itself, possibly behind pointers) are supported.
       Each such typedef is split into a parallel right typedef
       of the corresponding right type,
       and uses of the typedef name are split accordingly.
       For example, @('typedef struct foo *foo_p;') yields a right typedef
       @('typedef struct foo_right *foo_p_0;'),
       and a use @('foo_p x;') is split into @('foo_p x;') and @('foo_p_0 x_0;').
       Typedef chains are handled as well.")
     (xdoc::li
      "Typedefs whose denoted type is splittable
       (the struct type itself, possibly behind pointers) are supported.
       Each such typedef is split into a parallel right typedef
       of the corresponding right type,
       and uses of the typedef name are split accordingly.
       For example, @('typedef struct foo *foo_p;') yields a right typedef
       @('typedef struct foo_right *foo_p_0;'),
       and a use @('foo_p x;') is split into @('foo_p x;') and @('foo_p_0 x_0;').
       Typedef chains are handled as well.")
     (xdoc::li
      "The struct type must not appear in certain expression contexts,
       such as @('sizeof') and @('_Alignof') expressions;
       such occurrences are detected and reported as errors.")
     (xdoc::li
      "Unnamed members (e.g. anonymous bit-fields
       and anonymous structs/unions)
       always stay in the left struct type,
       since they cannot be listed
       in the @(':right-members') input,
       which assigns members to the right struct type by name.")
     (xdoc::li
      "Initializers that are split apart must be pure
       (i.e. side-effect-free),
       since splitting reorders and, for split members, duplicates them.
       This applies to the initializer lists of the struct type itself,
       and to the initializers of members of splittable type
       in other struct types.
       Initializers which are split apart
       are given explicit member designations,
       since the implicit positional order
       is not preserved by the split.")
     (xdoc::li
      "The code ensemble must use the C17 standard;
       this is checked by the transformation.
       The transformation assumes that at most one struct type
       per translation unit is subject to the split,
       namely the one denoted by the tag at file scope.
       This is consistent with C17,
       in which struct types declared in different scopes
       of the same translation unit are never compatible.
       It is not generally sufficient for C23,
       in which struct types in different scopes
       of the same translation unit may be compatible.")))
   (xdoc::section
    "Current Limitations"
    (xdoc::p
     "The following are temporary limitations which will hopefully be removed
      in the future with improvements to the implementation.")
    (xdoc::ul
     (xdoc::li
      "The transformation checks that expressions requiring lvalues
       (the operands of the address and increment/decrement operators,
       and the left operands of assignments)
       are still lvalues after transformation.
       However, this check relies on a syntactic overapproximation of lvalues
       (see @(tsee c$::expr-syntactic-lvalue-p)).
       For instance, a generic selection is considered an lvalue
       when any of its possible result expressions is an lvalue,
       even if the result expression actually selected
       is rewritten by the transformation into a non-lvalue.
       Consequently, the transformation may in rare cases
       produce invalid code which violates the lvalue requirements,
       without reporting an error.")
     (xdoc::li
      "Compatible struct types in other translation units
       are detected only at file scope.
       A struct type declared in a block scope
       of another translation unit
       may be compatible with the split struct type,
       but it is not detected or split.
       Code using such a type to interoperate with split objects
       (e.g. a block-scope @('extern') declaration of a split object)
       would be silently invalidated by the transformation.")
     (xdoc::li
      "Assembler constructs and attribute parameters are not transformed;
       a warning is printed when they are encountered.")
     (xdoc::li
      "Preprocessing constructs preserved in the abstract syntax
       (e.g. @('#include') directives) are not supported."))))
  :order-subtopics t)
