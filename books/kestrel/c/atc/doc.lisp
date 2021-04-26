; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atc

  :parents (c)

  :short "ATC (<b>A</b>CL2 <b>T</b>o <b>C</b>),
          a C code generator for ACL2."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This manual page contains user-level reference documentation for ATC.
      Usera who are new to ATC should start with the "
     (xdoc::seetopic "atc-tutorial" "tutorial")
     ", which provides user-level pedagogical information
      on how ATC works and how to use ATC effectively.")

    (xdoc::p
     "This manual page refers to the official C standard
      in the manner explained in "
     (xdoc::seetopic "c" "the top-level XDOC topic of this C library")
     "."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(atc fn1 ... fn"
     "     :output-file ...  ; no default"
     "     :proofs      ...  ; default t"
     "     :const-name  ...  ; default :auto"
     "     :print       ...  ; default :result"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('fn1'), ..., @('fnp')"
     (xdoc::p
      "Names of target ACL2 functions to translate to C.")
     (xdoc::p
      "Each @('fni') must be a symbol that names a function
       that satisfies the conditions discussed in the section
       `Representation of C Code in ACL2'."))

    (xdoc::desc
     "@(':output-file') &mdash; no default"
     (xdoc::p
      "Path of the file where the generated C code goes.")
     (xdoc::p
      "This must be an ACL2 string that is a file path.
       The path may be absolute,
       or relative to
       the " (xdoc::seetopic "cbd" "current working directory") ".")
     (xdoc::p
      "The directory must exist.
       The file may or may not exist:
       if it does not exist, it is created;
       if it exists, it is overwritten.
       The file must include a @('.c') extension."))

    (xdoc::desc
     "@(':proofs') &mdash; default @('t')"
     (xdoc::p
      "Specifies whether proofs should be generated or not.")
     (xdoc::p
      "This must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to generate proofs.")
      (xdoc::li
       "@('nil'), to not generate proofs."))
     (xdoc::p
      "While it is obviously recommended to generate proofs,
       setting this to @('nil') may be useful
       in case proof generation is (temporarily) broken."))

    (xdoc::desc
     "@(':const-name') &mdash; default @(':auto')"
     (xdoc::p
      "Name of the generated ACL2 named constant
       that holds the abstract syntax tree of the generated C program.")
     (xdoc::p
      "This must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('*program*')
        in the @('\"C\"') package.")
      (xdoc::li
       "Any other symbol, to use as the name of the constant."))
     (xdoc::p
      "This input must be absent if @(':proofs') is @('nil').
       The named constant is generated only if @(':proofs') is @('t').")
     (xdoc::p
      "In the rest of this documentation page,
       let @('*program*') be the symbol specified by this input,
       if applicable (i.e. when @(':proofs') is @('t'))."))

    (xdoc::evmac-input-print atc))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Representation of C Code in ACL2"

    (xdoc::p
     "For now ATC supports the ACL2 representation of
      a single C translation unit (which goes into the generated file).
      This translation unit consists of one or more C function definitions.")

    (xdoc::p
     "Each C function definition is represented by an ACL2 function definition.
      These are the target ACL2 functions @('fni') passed as inputs.
      The order of the C functions in the translation unit is the same as
      the order of the inputs @('fn1'), ..., @('fnp').")

    (xdoc::p
     "The name of the symbol @('fni')
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      The name of the symbol is used as
      the name of the corresponding C function.
      Therefore, the target functions must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).")

    (xdoc::p
     "The name of each symbol that is a formal parameter of each @('fni')
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      The names of these symbols are used as
      the names of the formal parameters of the corresponding C function,
      in the same order.
      Therefore, the formal parameters of each @('fni')
      must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).")

    (xdoc::p
     "The guard of each @('fni') must include,
      for every formal parameter @('x'),
      a conjunct of one of the following forms,
      which determines the C type of
      the corresponding parameter of the C function:")
    (xdoc::ul
     (xdoc::li
      "@('(scharp x)'), representing @('signed char').")
     (xdoc::li
      "@('(ucharp x)'), representing @('unsigned char').")
     (xdoc::li
      "@('(sshortp x)'), representing @('signed short').")
     (xdoc::li
      "@('(ushortp x)'), representing @('unsigned short').")
     (xdoc::li
      "@('(sintp x)'), representing @('signed int').")
     (xdoc::li
      "@('(uintp x)'), representing @('unsigned int').")
     (xdoc::li
      "@('(slongp x)'), representing @('signed long').")
     (xdoc::li
      "@('(ulongp x)'), representing @('unsigned long').")
     (xdoc::li
      "@('(sllongp x)'), representing @('signed long long').")
     (xdoc::li
      "@('(ullongp x)'), representing @('unsigned long long').")
     (xdoc::li
      "@('(uchar-arrayp x)'), representing @('unsigned char *')."))
    (xdoc::p
     "The conjuncts may be at any level of nesting,
      but must be easily extractable by flattening
      the @(tsee and) structure of the (translated) guard term.
      The rest of the guard (i.e. other than the conjuncts above)
      is not explicitly represented in the C code.")

    (xdoc::p
     "The return type of the C function corresponding to @('fni')
      is automatically determined from the body.
      The restrictions on the body, given below,
      make the determination of the return type possible in all cases.")

    (xdoc::p
     "Each function @('fni') must be in logic mode and guard-verified.
      Its "
     (xdoc::seetopic "acl2::function-definedness" "unnormalized body")
     " must be a statement term;
      this notion is defined below, along with the notions of
      C-valued terms,
      pure C-valued terms,
      and boolean terms.")

    (xdoc::p
     "A <i>statement term</i> is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A C-valued term.
       That is, a C-valued term is also a statement term.
       This represents a C @('return') statement
       whose expression is represented by the same term,
       viewed as a C-valued term.")
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test that is a boolean term and
       (ii) branches that are statement terms.
       This represents a C @('if') conditional statement
       whose test expression is represented by the test term
       and whose branch blocks are represented by the branch terms.")
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test of the form @('(mbt ...)') or @('(mbt$ ...)'),
       (ii) a `then' branch that is a statement term, and
       (iii) an `else' branch that may be any ACL2 term.
       This represents the same C code represented by the `then' branch.
       Both the test and the `else' branch are ignored;
       the reason is that ATC generates C code under guard assumptions.
       In translated terms,
       @('(mbt x)') is
       @('(return-last \'acl2::mbe1-raw \'t x)'), and
       @('(mbt$ x)') is
       @('(return-last \'acl2::mbe1-raw \'t (if x \'t \'nil))');
       these are the patterns that ATC looks for.")
     (xdoc::li
      "A term of the form @('(let ((var term)) body)'),
       where @('var') is a portable ASCII C identifier
       as defined in Section `Portable ASCII C Identifiers' below,
       @('term') is a C-valued term,
       and @('body') is a statement term.
       The C type of @('term') must not be a pointer type.
       This @(tsee let) represents one of the following:"
      (xdoc::ul
       (xdoc::li
        "A declaration of a C local variable represented by @('var'),
         initialized with the C expression represented by @('term'),
         and followed by the C code represented by @('body').
         The C type of the variable is determined from the initializer.
         The symbol name of @('var') must be distinct from
         the symbol names of all the other ACL2 variables in scope
         (function parameters and variables bound in enclosing @(tsee let)s).")
       (xdoc::li
        "An assignment to the C local variable or function parameter
         represented by @('var'),
         with the C expression represented by @('term'),
         and followed by the C code represented by @('body').
         This @(tsee let) must be in the scope of
         an ACL2 variable with the same symbol @('var');
         while the @('var') in this @(tsee let)
         is distinct from and shadows the one in scope in ACL2,
         it represents the same variable in C.
         In this case, the value bound to the outer @('var') must have
         the same C type as the value bound to the inner @('var').
         However, there must be no @(tsee if) ``between''
         this @(tsee let) and
         either the one of the outer @('var')
         (if @('var') is a local variable)
         or the start of the function body
         (if @('var') is a function parameter),
         i.e. the two variables must be in the same C scope
         (as represented in ACL2)."))
      "The two situations are distinguished by whether
       there is no outer @('var') in scope,
       in which case the @(tsee let) represents a declaration,
       or there is one (subject to the scope restriction above),
       in which case the @(tsee let) represents an assignment.
       In any case, the @(tsee let) must have exactly one variable.
       In translated terms,
       @('(let ((var term)) body)') is @('((lambda (var) body) term)');
       this is the pattern that ATC looks for."))

    (xdoc::p
     "A <i>C-valued term</i> is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A pure C-valued term.")
     (xdoc::li
      "A call of a target function @('fnj'), with @('j < i'),
       on pure C-valued terms.
       The restriction @('j < i') means that
       no (direct or indirect) recursion is allowed
       and the target functions must be specified
       in a topological order of their call graph.
       This represents a call of the corresponding C function."))

    (xdoc::p
     "A <i>pure C-valued term</i> is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A formal parameter of the function.
       This represents the corresponding C formal parameter,
       as an expression.")
     (xdoc::li
      "A variable introduced by @(tsee let) (as described above).
       This represents the corresponding C local variable,
       as an expression.")
     (xdoc::li
      "A call of a function @('<type>-const') on a quoted integer,
       where @('<type>') is among"
      (xdoc::ul
       (xdoc::li "@('sint')")
       (xdoc::li "@('uint')")
       (xdoc::li "@('slong')")
       (xdoc::li "@('ulong')")
       (xdoc::li "@('sllong')")
       (xdoc::li "@('ullong')"))
      "This represents a C integer constants
       of the C type indicated by the name of the function.
       The guard verification requirement ensures that
       the quoted integer is non-negative and within the range of the type.")
     (xdoc::li
      "A call of a function @('<op>-<type>') on a pure C-valued term,
       where @('<op>') is among"
      (xdoc::ul
       (xdoc::li "@('plus')")
       (xdoc::li "@('minus')")
       (xdoc::li "@('bitnot')")
       (xdoc::li "@('lognot')"))
      "and @('<type>') is among"
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
      "This represents the C operator indicated by the name of the function
       applied to a value of the type indicated by the name of the function.
       The guard verification requirement ensures that
       the operator is always applied to values of the right type
       and yields a well-defined result.
       These functions covers all the C unary operators
       (using the nomenclature in [C]).")
     (xdoc::li
      "A call of a function @('<op>-<type1>-<type2>') on pure C-valued terms,
       where @('<op>') is among"
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
      "and @('<type1>') and @('<type2>') are among"
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
      "This represents
       the corresponding C operator indicated by the name of the function
       applied to values of the types indicated by the name of the function.
       The guard verification requirement ensures that
       the operator is always applied to values of the right types
       and yields a well-defined result.
       These functions covers all the C strict pure binary operators;
       the non-strict operators @('&&') and @('||'),
       and the non-pure operatos @('='), @('+='), etc.,
       are represented differently.")
     (xdoc::li
      "A call of a function @('<type1>-from-<type2>')
       on a pure C-valued term,
       where @('<type1>') and @('<type2>') are among"
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
      "and also differ from each other.
       This represents
       a cast to the type indicated by the first part of the function name.
       The guard verification requirement ensures that
       the conversion is always applied to
       a value of the type indicated by the last part of the function name
       and yields a well-defined result.
       Even though conversions
       happen automatically in certain circumstances in C,
       these functions always represent explicit casts;
       implict conversions are represented implicitly,
       e.g. via the function for a unary operator that promoteds the operand.")
     (xdoc::li
      "A call of @(tsee uchar-array-read-sint) on C-valued terms.
       This represents an array subscripting expression.")
     (xdoc::li
      "A call of @(tsee sint01) on a boolean term.
       This converts a boolean term
       to a pure C-valued term.")
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test that is a boolean term and
       (ii) branches that are pure C-valued terms.
       This represents a C @('?:') conditional expression
       whose test expression is represented by the test term
       and whose branch expressions are represented by the branch terms.")
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test of the form @('(mbt ...)') or @('(mbt$ ...)'),
       (ii) a `then' branch that is a pure C-valued term, and
       (iii) an `else' branch that may be any ACL2 term.
       This represents the same C code represented by the `then' branch.
       Both the test and the `else' branch are ignored;
       the reason is that ATC generates C code under guard assumptions.
       In translated terms,
       @('(mbt x)') is
       @('(return-last \'acl2::mbe1-raw \'t x)'), and
       @('(mbt$ x)') is
       @('(return-last \'acl2::mbe1-raw \'t (if x \'t \'nil))');
       these are the patterns that ATC looks for."))

    (xdoc::p
     "A <i>boolean term</i> is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A call of a function @('<type>-nonzerop')
       on a pure C-valued term,
       where @('<type>') is among"
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
      "This converts a pure C-valued term
       to a boolean term.")
     (xdoc::li
      "A call of one of the following functions and macros
       on boolean terms:"
      (xdoc::ul
       (xdoc::li "@(tsee not)")
       (xdoc::li "@(tsee and)")
       (xdoc::li "@(tsee or)"))
      "The first one is a function, while the other two are macros.
       This represents the corresponding C logical operator
       (negation @('!'), conjunction @('&&'), disjunction @('||'));
       conjunction and disjunctions are represented non-strictly.
       In translated terms, @('(and x y)') and @('(or x y)') are
       @('(if x y \'nil)') and @('(if x x y)'):
       these are the patterns that ATC looks for."))

    (xdoc::p
     "Statement terms represent C statements,
      while C-valued and boolean terms represent C expressions.
      The boolean terms return ACL2 boolean values,
      while the statement (including C-valued) terms return
      ACL2 values that represent C values:
      the distinction between these two kinds of terms
      stems from the need to represent C's non-strictness in ACL2:
      C's non-strict constructs are
      @('if') statements,
      @('?:') expressions,
      @('&&') expressions, and
      @('||') expressions;
      ACL2's only non-strict construct is @(tsee if)
      (which the macros @(tsee and) and @(tsee or) expand to, see above).
      Pure C-valued terms
      represent C expressions without side effects;
      C function calls may be side-effect-free,
      but in general we do not consider them pure,
      so they are represented by C-valued terms
      that are not pure C-valued terms.
      Boolean terms are always pure;
      so they do not need the explicit designation `pure'
      because they are the only boolean terms handled by ATC.")

    (xdoc::p
     "The above restrictions imply that @('fni') returns a single result,
      i.e. not an @(tsee mv) result.
      By construction, this result has an easily inferred C type.")

    (xdoc::p
     "The body of the C function represented by each @('fni')
      is the compound statement consisting of
      the block items (i.e. statements and declarations)
      represented by the ACL2 function's body
      (which is a statement term).")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Portable ASCII C Identifiers"

     (xdoc::p
      "A portable ASCII C identifier is
       a non-empty sequence of ASCII characters that:")
     (xdoc::ul
      (xdoc::li
       "Consists of only
        the 26 uppercase Latin letters,
        the 26 lowercase Latin letters,
        the 10 numeric digits,
        and the underscore.")
      (xdoc::li
       "Starts with a letter or underscore.")
      (xdoc::li
       "Differs from all the C keywords, which are"
       (xdoc::codeblock
        "auto       extern     short      while"
        "break      float      signed     _Alignas"
        "case       for        sizeof     _Alignof"
        "char       goto       static     _Atomic"
        "const      if         struct     _Bool"
        "continue   inline     switch     _Complex"
        "default    int        typedef    _Generic"
        "do         long       union      _Imaginary"
        "double     register   unsigned   _Noreturn"
        "else       restrict   void       _Static_assert"
        "enum       return     volatile   _Thread_local")))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Constant"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defconst *program* ...)")
     (xdoc::p
      "where @('...') is the abstract syntax tree of
       the generated C translation unit,
       which ATC also pretty-prints and writes
       to the file specified by the @(':output-file') input."))
     (xdoc::p
      "If the @(':proofs') input is @('nil'),
       this constant is not generated.")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Theorems"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defthm *program*-well-formed ...)")
     (xdoc::p
      "where @('...') is an assertion about @('*program*') stating that
       the generated (abstract syntax tree of the) translation unit
       is statically well-formed,
       i.e. it compiles according to [C].")
     (xdoc::p
      "If the @(':proofs') input is @('nil'),
       this theorem is not generated.")

     (xdoc::p
      "For each target function @('fn'), ATC generates an event")
     (xdoc::codeblock
      "(defthm *program*-fn-correct ...)")
     (xdoc::p
      "where @('...') is an assertion about @('fn') and @('*program*')
       stating that,
       under the guard of @('fn'),
       executing the C dynamic semantics on
       the C function generated from @('fn')
       yields the same result as the function @('fn').
       That is,
       the C function is functionally equivalent to the ACL2 function.")
     (xdoc::p
      "If the @(':proofs') input is @('nil'),
       this theorem is not generated.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Generated C Code"

    (xdoc::p
     "ATC generates a single C file that contains
      a translation unit that contains
      a C function for each target ACL2 function @('fni'),
      as explained in Section `Representation of C Code in ACL2'.")

    (xdoc::p
     "The guard verification requirement stated earlier for each @('fni')
      implies that the generated C operations
      never exhibit undefined behavior,
      provided that they are called with values
      whose ACL2 counterparts satisfy the guard of @('fni').")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Compiling and Running the C Code"

     (xdoc::p
      "The generated C code can be compiled and run as any other C code.
       For instance, one can use @('gcc') on macOS or Linux.")

     (xdoc::p
      "Just compiling the generated C file may result in an error
       due to the lack of a @('main') function in the file.
       The code generated by ATC is meant to be called by external C code,
       where presumably a @('main') function will exist.
       To test the generated code,
       one can write a separate C file with a @('main') function,
       and compile both files together.
       By default, an executable @('a.out') will be generated
       (if using @('gcc') on macOS or Linux).")

     (xdoc::p
      "The directory @('[books]/kestrel/c/atc/tests')
       contains some examples of C code generation
       and handwritten C code to test the generated code.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Redundancy"

    (xdoc::p
     "A call of @('atc') is redundant if an only if
      it is identical to a previous successful call of @('atc')."))))
