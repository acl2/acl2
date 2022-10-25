; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
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
      if wrapped in @(tsee pointer), they specify "
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
      (xdoc::li "@('(schar <pos?>)')")
      (xdoc::li "@('(uchar <pos?>)')")
      (xdoc::li "@('(sshort <pos?>)')")
      (xdoc::li "@('(ushort <pos?>)')")
      (xdoc::li "@('(sint <pos?>)')")
      (xdoc::li "@('(uint <pos?>)')")
      (xdoc::li "@('(slong <pos?>)')")
      (xdoc::li "@('(ulong <pos?>)')")
      (xdoc::li "@('(sllong <pos?>)')")
      (xdoc::li "@('(ullong <pos?>)')"))
     (xdoc::p
      "where @('<pos?>') is an optional positive integer
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
       in which case it represents a flexible array member [C:6.7.2.1/18].
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
     "@('struct-<tag>-read-<member>')"
     (xdoc::p
      "Reader for an integer member of the structure type.")
     (xdoc::p
      "There is one such reader for every member
       whose name is @('<member>')
       and whose type is an integer type.")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member> ((struct struct-<tag>-p))"
      "  :returns (value <typei>p)"
      "  ...)")
     (xdoc::p
      "where @('<typei>p') is the recognizer of
       the integer type corresponding to
       the @('typei') that specifies the type of the member."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>')"
     (xdoc::p
      "Writer for an integer member of the structure type.")
     (xdoc::p
      "There is one such writer for every member
       whose name is @('<member>')
       and whose type is an integer type.")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member> ((value <typei>p)"
      "                                     (struct struct-<tag>-p))"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<typei>p') is the recognizer of
       the integer type corresponding to
       the @('typei') that specifies the type of the member."))

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
      "ACL2 integer index checker for an array member of the structure type.")
     (xdoc::p
      "There is one such checker for every member
       whose name is @('<member>')
       ans whose type is an array type.")
     (xdoc::p
      "If the array type of the member has a specified size,
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index integerp))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "If the array type of the member does not have a specified size
       (which may be only the case for the last member,
       if it is a flexible array member),
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index integerp)"
      "                                         (struct struct-<tag>-p))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "In either form,
       this function checks if the index is
       within the range of the array.
       If the length of the array is known
       (specified by the @('<pos?>')
       in the @('<typei>') that specifies the type of the member),
       the checker only needs the integer.
       For the flexible array member (if present),
       we also need the structure has an additional argument,
       from which the flexible array member size is obtained
       and used to check the index against it.")
     (xdoc::p
      "This checker is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::desc
     "@('struct-<tag>-<member>-<type>-index-okp')"
     (xdoc::p
      "C integer index checker for an array member of the structure type.")
     (xdoc::p
      "There is one such checker for every member
       whose name is @('<member>')
       and whose type is an array type,
       and for every choice of an integer type @('<type>') for the index.")
     (xdoc::p
      "If the array type of the member has a specified size,
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-<type>-index-okp ((index <type>p))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "If the array type of the member does not have a specified size
       (which may be only the case for the last member,
       if it is a flexible array member),
       the checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index <type>p)"
      "                                         (struct struct-<tag>-p))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "This function checks if the index is
       within the range of the array.
       If the length of the array is known
       (specified by the @('<pos?>')
       in the @('<typei>') that specifies the type of the member),
       the checker only needs the integer.
       For the flexible array member (if present),
       we also need the structure has an additional argument,
       from which the flexible array member size is obtained
       and used to check the index against it.")
     (xdoc::p
      "This checker converts the C integer index to an ACL2 integer index
       and calls the checker @('struct-<tag>-<member>-index-okp') above."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>')"
     (xdoc::p
      "Reader for an array member of the structure type,
       using an ACL2 integer as index.")
     (xdoc::p
      "There is one such reader for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member> ((index integerp)"
      "                                    (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-index-okp index ...)"
      "  :returns (value <elemtype>p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where @('...') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The reader reads an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This reader is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>-<type>')"
     (xdoc::p
      "Reader for an array member of the structure type,
       using a C integer as an index.")
     (xdoc::p
      "There is one such reader for every member
       whose name is @('<member>')
       and whose type is an array type,
       and for every choice of an integer type @('<type>') for the index.")
     (xdoc::p
      "The reader has the form")
     (xdoc::codeblock
      "(define struct-<tag>-read-<member>-<type> ((index <type>p)"
      "                                           (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-<type>-index-okp index ...)"
      "  :returns (value <elemtype>p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where @('...') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The reader reads an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This reader converts the C integer index to an ACL2 integer index
       and calls the reader @('struct-<tag>-read-<member>') above."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>')"
     (xdoc::p
      "Writer for an array member of the structure type,
       using an ACL2 integer as index.")
     (xdoc::p
      "There is one such writer for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member> ((index integerp)"
      "                                     (value <elemtype>p)"
      "                                     (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-index-okp index ...)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where @('...') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The writer writes an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This writer is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::desc
     "@('struct-<tag>-write-<member>-<type>')"
     (xdoc::p
      "Writer for an array member of the structure type,
       using a C integer as index.")
     (xdoc::p
      "There is one such writer for every member
       whose name is @('<member>')
       and whose type is an array type,
       and for every choice of an integer type @('<type>') for the index.")
     (xdoc::p
      "The writer has the form")
     (xdoc::codeblock
      "(define struct-<tag>-write-<member>-<type> ((index <type>p)"
      "                                            (value <elemtype>p)"
      "                                            (struct struct-<tag>-p))"
      "  :guard (struct-<tag>-<member>-<type>-index-okp index ...)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member,
       and where @('...') is
       either @('struct') if the member is a flexible array member
       or nothing otherwise.
       The writer writes an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This writer converts the C integer index to an ACL2 integer index
       and calls the writer @('struct-<tag>-write-<member>') above.")))))
