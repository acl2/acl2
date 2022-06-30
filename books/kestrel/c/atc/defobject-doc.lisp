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

(defxdoc defobject

  :parents (atc-shallow-embedding)

  :short "Define a shallowly embedded external object."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "A more colloquial term for this is `global variable',
      i.e. a variable declared at the top level of a file,
      as opposed to a local variable, which is declared in a block.
      In more technical terms,
      a C translation unit consists of
      a sequence of external declarations [C:6.9],
      where an external declaration is
      either a function definition [C:6.9.1]
      or a declaration [C:6.7],
      where the latter may define an object [C:6.9.2].
      Thus, a global variable is introduced as
      an external object definition.")

    (xdoc::p
     "This macro defines an external C object shallowly embedded in ACL2.
      The macro specifies the name, type, and initializer.
      The macro stores this information in a table,
      and generates a recognizer for the possible values of the object.
      A shallowly embedded C function that accesses the object
      is represented by an ACL2 function with a parameter
      that has the same name as the object
      and whose guard says that the parameter
      satisfies the generated recognizer.
      While the parameter has to be explicit in purely functional ACL2,
      the C function has no corresponding parameter,
      and instead accesses the object directly by name,
      since the object is in scope.
      The macro also generates a nullary function
      that returns the initial value of the object.")

    (xdoc::p
     "Currently this macro only supports objects of integer array types,
      but we plan to extend support to more types."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defobject name"
     "           :type ..."
     "           :init ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name of the externally defined object.")
     (xdoc::p
      "It must be a symbol whose @(tsee symbol-name) is
       a portable ASCII identifier as defined in @(tsee atc),
       that is distinct from the @(tsee symbol-name)s of objects
       introduced by previous successful calls of @('defobject')."))

    (xdoc::desc
     "@(':type') &mdash; no default"
     (xdoc::p
      "Type of the externally defined object.")
     (xdoc::p
      "It must be one of")
     (xdoc::ul
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
       Each of these represents an integer array type with the specified size,
       where the limit on the size is so that
       it can be represented by a C integer constant."))

    (xdoc::desc
     "@(':init') &mdash; no default"
     (xdoc::p
      "Initializer of the externally defined object.")
     (xdoc::p
      "It must be a list of length @('<pos>')
       of constant expression terms returning @('T'),
       where @('T') is the integer type specified in the @(':type') input
       (i.e. the element type of the array),
       and where the notion of constant expression term returning @('T')
       is defined below.
       This list represents an array initializer [C:6.7.9].")
     (xdoc::p
      "The terms must be guard-verifiable.
       This requirement is checked implicitly
       by generating the @('object-<name>-init') function
       (see the `"
      xdoc::*evmac-section-generated-title*
      "' section below)
       via an event that requires its guard verification.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Constant Expression Terms"

    (xdoc::p
     "This is a restricted version of the notion of
      pure expression terms defined in @(tsee atc).
      A pure expression term is an ACL2 term that represent
      a C pure expression that may involve variables.
      A constant expression term is an ACL2 term that represents
      a C constant expressions [C:6.6],
      which does not involve variables.
      Since there are no variables involved,
      the notion of constant expression term is defined
      without reference to any ACL2 function @('fn'),
      unlike the notion of pure expression term in @(tsee atc).")

    (xdoc::p
     "A <i>constant expression term returning</i> @('T'),
      where @('T') is a non-@('void') C type,
      is inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A call of a function @('<type>-<base>-const') on a quoted integer,
       when @('<type>') is among"
      (xdoc::ul
       (xdoc::li "@('sint')")
       (xdoc::li "@('uint')")
       (xdoc::li "@('slong')")
       (xdoc::li "@('ulong')")
       (xdoc::li "@('sllong')")
       (xdoc::li "@('ullong')"))
      "@('<base>') is among"
      (xdoc::ul
       (xdoc::li "@('dec')")
       (xdoc::li "@('oct')")
       (xdoc::li "@('hex')"))
      "@('T') is the C type corresponding to @('<type>')
       and the quoted integer is non-negative and in the range of @('T').
       This represents a C integer constant
       of the C type indicated by the name of the function,
       expressed in decimal, octal, or hexadecimal base.")
     (xdoc::li
      "A call of a function @('<op>-<type>') on
       a constant expression term returning @('U'),
       when @('<op>') is among"
      (xdoc::ul
       (xdoc::li "@('plus')")
       (xdoc::li "@('minus')")
       (xdoc::li "@('bitnot')")
       (xdoc::li "@('lognot')"))
      "@('<type>') is among"
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
       (xdoc::li "@('ullong')"))
      "@('T') is the C type corresponding to
       the return type of @('<op>-<type>')
       and @('U') is the C type corresponding to @('<type>').
       This represents the C operator indicated by the name of the function
       applied to a value of the type indicated by the name of the function.
       The guard verification requirement ensures that
       the operator yields a well-defined result.
       These functions covers all the C unary operators
       (using the nomenclature in [C]).")
     (xdoc::li
      "A call of a function @('<op>-<type1>-<type2>')
       on constant expression terms returning @('U') and @('V'),
       when @('<op>') is among"
      (xdoc::ul
       (xdoc::li "@('add')")
       (xdoc::li "@('sub')")
       (xdoc::li "@('mul')")
       (xdoc::li "@('div')")
       (xdoc::li "@('rem')")
       (xdoc::li "@('shl')")
       (xdoc::li "@('shr')")
       (xdoc::li "@('lt')")
       (xdoc::li "@('gt')")
       (xdoc::li "@('le')")
       (xdoc::li "@('ge')")
       (xdoc::li "@('eq')")
       (xdoc::li "@('ne')")
       (xdoc::li "@('bitand')")
       (xdoc::li "@('bitxor')")
       (xdoc::li "@('bitior')"))
      "@('<type1>') and @('<type2>') are among"
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
       (xdoc::li "@('ullong')"))
      "@('T') is the C type corresponding to
       the return type of @('<op>-<type1>-<type2>'),
       @('U') is the C type corresponding to @('<type1>'), and
       @('V') is the C type corresponding to @('<type2>').
       This represents the C operator indicated by the name of the function
       applied to values of the types indicated by the name of the function.
       The guard verification requirement ensures that
       the operator yields a well-defined result.
       These functions covers all the C strict pure binary operators;
       the non-strict operators @('&&') and @('||'),
       and the non-pure operators @('='), @('+='), etc.,
       are represented differently.")
     (xdoc::li
      "A call of a function @('<type1>-from-<type2>')
       on a constant expression term returning @('U'),
       when @('<type1>') and @('<type2>') are among"
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
       (xdoc::li "@('ullong')"))
      "and also differ from each other,
       @('T') is the C type corresponding to @('<type1>')
       and @('U') is the C type corresponding to @('<type2>').
       This represents
       a cast to the type indicated by the first part of the function name.
       The guard verification requirement ensures that
       the conversion yields a well-defined result.
       Even though conversions
       happen automatically in certain circumstances in C,
       these functions always represent explicit casts;
       implict conversions are represented implicitly,
       e.g. via the function for a unary operator
       that promotes the operand.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('object-<name>-p')"
     (xdoc::p
      "Recognizer of the possible values of the externally defined object.")
     (xdoc::p
      "This is defined as")
     (xdoc::codeblock
      "(defun object-<name>-p (x)"
      "  (and (<type>-arrayp x)"
      "       (equal (<type>-array-length x) <pos>)))")
     (xdoc::p
      "where @('<name>') is the name of the object
       specified in the @('name') input
       and @('<type>') is the integer fixtype name
       specified in the @(':type') input.
       The recognizer @('object-<name>-p') is
       in the same package as the @('name') input.
       The function is in logic mode and guard-verified;
       its guard verification is always expected to succeed."))

    (xdoc::desc
     "@('object-<name>-init')"
     (xdoc::p
      "Nullary function that returns the initializing value
       of the externally defined object.")
     (xdoc::p
      "This is defined as")
     (xdoc::codeblock
      "(defun object-<name>-init ()"
      "  (<type>-array-of (list <term1> <term2> ...)))")
     (xdoc::p
      "where @('<name>') is the name of the object
       specified in the @('name') input,
       @('<type>') is the integer fixtype name
       specified in the @(':type') input,
       and @('<term1>'), @('<term2>'), etc.
       are the terms in the list in the @(':init') input.
       The nullary function @('object-<name>-init') is
       in the same package as the @('name') input.
       The function is in logic mode and guard-verified:
       its guard verification checks some of the requirements
       on the @(':init') input mentioned in the `"
      xdoc::*evmac-section-inputs-title*
      "' section above.")))))
