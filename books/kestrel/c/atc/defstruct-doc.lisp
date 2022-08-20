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
      more precisely, pointers to structure types, for now.
      That is, similarly to arrays, structures are in the heap,
      and pointers to them are passed to the represented C functions,
      which may side-effect those structures via the member writers,
      which represent assignments to structure members
      accessed via the C @('->') operator (not the @('.') operator).
      Structures may also be passed around by value in C,
      but initially we support only passing by pointer.
      Note that C arrays may only be passed by pointers, in effect,
      as arrays are not first-class entities in C,
      but merely collections of contiguous objects,
      normally accessed via pointers
      to the first object of the collections.")

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
      "This is the tag of the structure type [C:6.7.2.3].")
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
      (xdoc::li "@('(schar <pos>)')")
      (xdoc::li "@('(uchar <pos>)')")
      (xdoc::li "@('(sshort <pos>)')")
      (xdoc::li "@('(ushort <pos>)')")
      (xdoc::li "@('(sint <pos>)')")
      (xdoc::li "@('(uint <pos>)')")
      (xdoc::li "@('(slong <pos>)')")
      (xdoc::li "@('(ulong <pos>)')")
      (xdoc::li "@('(sllong <pos>)')")
      (xdoc::li "@('(ullong <pos>)')"))
     (xdoc::p
      "where @('<pos>') is a positive integer not exceeding @(tsee ullong-max).
       The first ten specify C integer types:
       each is the name of an ACL2 fixtype that models a C integer type,
       and specifies the corresponding C integer type.
       The other ten specify C integer array types:
       each consists of
       the name of an ACL2 fixtype that models a C integer type,
       which specifies the element type of the array type,
       and a positive integer,
       which specifies the size of the array type.
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
     "@('struct-<tag>-<member>-index-okp')"
     (xdoc::p
      "ACL2 integer index checker for an array member of the structure type.")
     (xdoc::p
      "There is one such checker for every member
       whose name is @('<member>')
       and whose type is an array type.")
     (xdoc::p
      "The checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-index-okp ((index integerp))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "This function checks if the index is
       within the range of the array.
       Since the length of the array is known
       (specified by the @('<pos>')
       in the @('<typei>') that specifies the type of the member),
       the checker only takes the integer.
       This checker is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::desc
     "@('struct-<tag>-<member>-<type>index-okp')"
     (xdoc::p
      "C integer index checker for an array member of the structure type.")
     (xdoc::p
      "There is one such checker for every member
       whose name is @('<member>')
       and whose type is an array type,
       and for every choice of an integer type @('<type>') for the index.")
     (xdoc::p
      "The checker has the form")
     (xdoc::codeblock
      "(define struct-<tag>-<member>-<type>-index-okp ((index <type>p))"
      "  :returns (yes/no booleanp)"
      "  ...)")
     (xdoc::p
      "This function checks if the index is
       within the range of the array.
       Since the length of the array is known
       (specified by the @('<pos>')
       in the @('<typei>') that specifies the type of the member),
       the checker only takes the integer.
       This checker converts the C integer index to an ACL2 integer index
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
      "  :guard (struct-<tag>-<member>-index-okp index)"
      "  :returns (value <elemtype>p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member.
       The reader reads an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This reader is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::desc
     "@('struct-<tag>-read-<member>-<type>')"
     (xdoc::p
      "Reader for an array member of the structure type.")
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
      "  :guard (struct-<tag>-<member>-<type>-index-okp index)"
      "  :returns (value <elemtype>p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member.
       The reader reads an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This reader converts the C integer index to an ACL2 integer index
       and calls the reader @('struct-<tag>-read-<member>') above."))

    (xdoc::p
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
      "  :guard (struct-<tag>-<member>-index-okp index)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member.
       The writer writes an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This writer is used by the ones that operate on
       indices of C integer types below."))

    (xdoc::p
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
      "  :guard (struct-<tag>-<member>-<type>-index-okp index)"
      "  :returns (new-struct struct-<tag>-p)"
      "  ...)")
     (xdoc::p
      "where @('<elemtype>p') is the recognizer of
       the integer element type of
       the @('typei') that specifies the type of the member.
       The writer writes an element of the array member,
       not the whole array member.")
     (xdoc::p
      "This writer converts the C integer index to an ACL2 integer index
       and calls the writer @('struct-<tag>-write-<member>') above.")))))
