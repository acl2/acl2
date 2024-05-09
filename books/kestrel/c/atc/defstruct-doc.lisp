; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defstruct

  :parents (atc-shallow-embedding)

  :short "Define a shallowly embedded structure type."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Since C structure types are user-defined,
      we provide this macro to define
      a shallowly embedded ACL2 representation of a C structure type.
      The user must call this macro
      to introduce the structure types that the C code must use.
      The macro specifies the name and the members,
      where each member is specified by a name and a type.
      The macro records the information about the structure type in a table,
      and generates functions to operate on the structure type,
      along with some theorems.")

    (xdoc::p
     "C code shallowly embedded in ACL2 can use
      the generated recognizers @('struct-<tag>-p') in guards
      to specify structure types for parameters;
      if wrapped in @(tsee star), they specify "
     (xdoc::seetopic "pointer-types" "pointer types")
     " to structure types.")

    (xdoc::p
     "Currently this macro only supports certain types
      for the members of the structure type.
      We plan to extend this macro to support more member types."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defstruct name"
     "           (name1 type1)"
     "           (name2 type2)"
     "           ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name of the structure type.")
     (xdoc::p
      "It must be a symbol whose @(tsee symbol-name) is a "
      (xdoc::seetopic "portable-ascii-identifiers"
                      "portable ASCII identifier")
      " that is distinct from the @(tsee symbol-name)s of structure types
       introduced by previous successful calls of @('defstruct').")
     (xdoc::p
      "This symbol name is the tag of the structure type [C:6.7.2.3].")
     (xdoc::p
      "In the rest of this documentation page,
       let @('<tag>') be the @(tsee symbol-name) of this input."))

    (xdoc::desc
     "@('name1'), @('name2'), ..."
     (xdoc::p
      "Names of the members of the structure type.")
     (xdoc::p
      "Each must be a symbol whose @(tsee symbol-name) is a "
      (xdoc::seetopic "portable-ascii-identifiers"
                      "portable ASCII identifier")
      " that is distinct from the @(tsee symbol-name)s
       of all the other member names in the @('defstruct').")
     (xdoc::p
      "There must be at least one member (name)."))

    (xdoc::desc
     "@('type1'), @('type2'), ..."
     (xdoc::p
      "Types of the members of the structure type.")
     (xdoc::p
      "Each must be one of")
     (xdoc::ul
      (xdoc::li "@('schar')")
      (xdoc::li "@('uchar')")
      (xdoc::li "@('sshort')")
      (xdoc::li "@('ushort')")
      (xdoc::li "@('sint')")
      (xdoc::li "@('uint')")
      (xdoc::li "@('slong')")
      (xdoc::li "@('ulong')")
      (xdoc::li "@('sllong')")
      (xdoc::li "@('ullong')")
      (xdoc::li "@('(schar <size?>)')")
      (xdoc::li "@('(uchar <size?>)')")
      (xdoc::li "@('(sshort <size?>)')")
      (xdoc::li "@('(ushort <size?>)')")
      (xdoc::li "@('(sint <size?>)')")
      (xdoc::li "@('(uint <size?>)')")
      (xdoc::li "@('(slong <size?>)')")
      (xdoc::li "@('(ulong <size?>)')")
      (xdoc::li "@('(sllong <size?>)')")
      (xdoc::li "@('(ullong <size?>)')"))
     (xdoc::p
      "where @('<size?>') is an optional positive integer
       which, if present, must not exceed @(tsee ullong-max).
       The first ten specify C integer types:
       each is the name of an ACL2 fixtype that models a C integer type,
       and specifies the corresponding C integer type.
       The other ten specify C integer array types:
       each consists of
       the name of an ACL2 fixtype that models a C integer type,
       which specifies the element type of the array type,
       and an optional positive integer;
       if present, the positive integer specifies the size of the array type;
       if absent, the array type has unspecified size.
       The positive integer may be absent only if the member is the last one,
       in which case it represents a flexible array member [C:6.7.2.1/18];
       in this case, there must be at least another member.
       The aforementioned upper bound on the size
       is so that the size of the array type
       is representable as a C integer constant.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('struct-<tag>-p')"
     (xdoc::p
      "Recognizer of the values of the structure type."))

    (xdoc::desc
     "@('struct-<tag>-fix')"
     (xdoc::p
      "Fixer of the values of the structure type."))

    (xdoc::desc
     "@('struct-<tag>')"
     (xdoc::p
      "Fixtype of the values of the structure type."))

    (xdoc::desc
     "@('struct-<tag>')"
     (xdoc::p
      "Constructor of the values of the structure type.")
     (xdoc::p
      "This has the same name as the fixtype (see above),
       but it belongs to a different name space (functions vs. fixtypes).")
     (xdoc::p
      "The constructor has the form")
     (xdoc::codeblock
      "(define struct-<tag> ((<name1> <pred1>) (<name2> <pred2>) ...)"
      "  :guard (and ... (equal (len <namei>) <sizei>) ...)"
      "  :returns (struct struct-<tag>-p"
      "                   :hyp (and ... (equal (len <namei>) <sizei>) ...))"
      "  ...)")
     (xdoc::p
      "where there is exactly a parameter for each member,
       with the same and in the same order,
       whose type @('<pred1>'), @('<pred2>'), etc.
       is (i) the recognizer of the integer type if the member has integer type
       or (ii) the recognizer of lists of the element integer type
       if the member has array type.
       Furthermore, the additional guard in @(':guard') consists of
       a length constraint for each array member of array type:
       for an array with a size,
       the length constraint is an equality between
       the @(tsee len) of the parameter and the positive integer length;
       for an array without a size (i.e. a flexible array member),
       the length constraint is just @(tsee consp) of the parameter.
       The return theorem of the constructor has
       exactly all the length equality constraints as hypotheses
       (it does not have the @(tsee consp) constraint
       for the flexible array member, if any."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>')"
     (xdoc::p
      "Reader for a member of the structure type.")
     (xdoc::p
      "There is one such reader for every member whose name is @('<member>').")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member> ((struct struct-<tag>-p))"
      "  :returns (value <typei>p)"
      "  ...)")
     (xdoc::p
      "where @('<typei>p') is the recognizer of the type corresponding to
       the @('typei') that specifies the type of the member."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>')"
     (xdoc::p
      "Writer for a member of the structure type.")
     (xdoc::p
      "There is one such writer for every member whose name is @('<member>').")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member> ((value <typei>p)"
      "                                     (struct struct-<tag>-p))"
      "  ;; :guard present if <typei>p is <type>-arrayp:"
      "  :guard (equal (<type>-array-length value) ...)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<typei>p') is the recognizer of the type corresponding to
       the @('typei') that specifies the type of the member.
       If the member has array type,
       the @(':guard') constrains the length of @('value')
       to be the one of the member."))

    (xdoc::desc
     "@('struct-<tag>-<member>-length')"
     (xdoc::p
      "Length of the flexible array member.")
     (xdoc::p
      "This is generated if the last member of the structure type
       has an array type of unspecified size,
       i.e. the structure type has a flexible array member.")
     (xdoc::p
      "The function has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-length ((struct struct-<tag>-p))"
      "  :returns (len natp)"
      "  ...)"))

    (xdoc::desc
     "@('struct-<tag>-<member>-index-okp')"
     (xdoc::p
      "Index checker for an array member of the structure type.")
     (xdoc::p
      "There is one such checker for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "If the array type of the member has a specified size,
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index cintegerp))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "If the array type of the member does not have a specified size
       (which may be only the case for the last member,
       if it is a flexible array member),
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index cintegerp)"
      "                                         (struct struct-<tag>-p))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "In either form,
       this function checks if the C integer index is
       within the range of the array.
       If the length of the array is known
       (specified by the @('<size?>')
       in the @('<typei>') that specifies the type of the member),
       the checker only needs the index.
       For the flexible array member (if present),
       we also need the structure as an additional argument,
       from which the flexible array member size is obtained
       and used to check the index against it."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>-element')"
     (xdoc::p
      "Reader for an element of an array member of the structure type,
       using a C integer as index.")
     (xdoc::p
      "There is one such reader for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member>-element ((index cintegerp)"
      "                                            (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-index-okp index ...)"
      "  :returns (value <elemtype>p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where the @('...') in the @(':guard') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The reader reads an element of the array member,
       not the whole array member."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>-element')"
     (xdoc::p
      "Writer for an array member of the structure type,
       using a C integer as index.")
     (xdoc::p
      "There is one such writer for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member>-element ((index cintegerp)"
      "                                             (value <elemtype>p)"
      "                                             (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-index-okp index ...)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where the @('...') in the @(':guard') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The writer writes an element of the array member,
       not the whole array member."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>-list')"
     (xdoc::p
      "Reader for all the elements of an array member of the structure type,
       where the elements are returned as a list (not an array).")
     (xdoc::p
      "There is one such reader for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member>-list ((struct struct-<tag>-p))"
      "  :returns (values <elemtype>-listp)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>-listp') is the recognizer of
       lists of the integer element type of
       the @('typei') that specifies the type of the member."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>-list')"
     (xdoc::p
      "Writer for all the elements of an array member of the structure type,
       where the elements are passed as a list (not an array).")
     (xdoc::p
      "There is one such writer for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member>-list ((value <elemtype>-listp)"
      "                                         (struct struct-<tag>-p))"
      "  :guard (equal (len values) ...)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>-listp') is the recognizer of
       lists of the integer element type of
       the @('typei') that specifies the type of the member,
       and the @('...') in the @(':guard') is
       either the positive integer size of the array
       if the array member has a known size,
       or the term @('(len (struct-<tag>-read-<member>-list struct))')
       if the array member is a flexible one.")))))
