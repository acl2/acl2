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
      Users who are new to ATC should start with the "
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
       `Representation of C Code in ACL2'.")
     (xdoc::p
      "These function names must be all distinct.")
     (xdoc::p
      "There must be at least one target function."))

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
       The file name must include a @('.c') extension."))

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
      These are
      the non-recursive target ACL2 functions @('fni') passed as inputs;
      the recursive target ACL2 functions @('fni') passed as inputs
      represent loops in the C functions instead, as explained below.
      The order of the C functions in the translation unit is the same as
      the order of the (non-recursive) inputs @('fn1'), ..., @('fnp').")

    (xdoc::p
     "Each function @('fni') must be in logic mode and guard-verified.
      The function must not occur in its own guard,
      which is rare but allowed in ACL2.")

    (xdoc::p
     "The symbol name of each non-recursive @('fni')
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      That symbol name is used as the name of the corresponding C function.
      Therefore, the non-recursive target functions
      must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).
      There is no restriction on
      the symbol names of the recursive target functions:
      these represent C loops, not C functions;
      the names of the recursive target functions
      are not represented at all in the C code.")

    (xdoc::p
     "The symbol name of each formal parameter of each @('fni'),
      both non-recursive and recursive,
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      When @('fni') is non-recursive,
      the symbol names of its parameters are used as
      the names of the formal parameters of the corresponding C function,
      in the same order.
      Therefore, the formal parameters of each @('fni')
      must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).
      When @('fni') is recursive,
      the symbol names of its parameters are used as names of C variables,
      as explained below.")

    (xdoc::p
     "When @('fni') is recursive,
      it must have at least one formal parameter.
      When @('fni') is non-recursive,
      it may have any number of formal parameters, including none.")

    (xdoc::p
     "If @('fni') is recursive,
      it must be singly (not mutually) recursive,
      its well-founded relation must be @(tsee o<),
      and its measure must yield a natural number.
      The latter requirement is checked via an applicability condition,
      as described in the `Applicability Conditions' section.")

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
      "@('(schar-arrayp x)'), representing @('signed char *').")
     (xdoc::li
      "@('(uchar-arrayp x)'), representing @('unsigned char *').")
     (xdoc::li
      "@('(sshort-arrayp x)'), representing @('signed short *').")
     (xdoc::li
      "@('(ushort-arrayp x)'), representing @('unsigned short *').")
     (xdoc::li
      "@('(sint-arrayp x)'), representing @('signed int *').")
     (xdoc::li
      "@('(uint-arrayp x)'), representing @('unsigned int *').")
     (xdoc::li
      "@('(slong-arrayp x)'), representing @('signed long *').")
     (xdoc::li
      "@('(ulong-arrayp x)'), representing @('unsigned long *').")
     (xdoc::li
      "@('(sllong-arrayp x)'), representing @('signed long long *').")
     (xdoc::li
      "@('(ullong-arrayp x)'), representing @('unsigned long long *')."))
    (xdoc::p
     "The conjuncts may be at any level of nesting,
      but must be extractable by flattening
      the @(tsee and) structure of the (translated) guard term.
      The rest of the guard (i.e. other than the conjuncts above)
      is not explicitly represented in the C code.")

    (xdoc::p
     "The return type of
      the C function corresponding to each non-recursive @('fni')
      is automatically determined from the body, as explained below.")

    (xdoc::p
     "The " (xdoc::seetopic "acl2::function-definedness" "unnormalized body")
     " of each @('fni') must be as follows:")
    (xdoc::ul
     (xdoc::li
      "If @('fni') is non-recursive, the unnormalized body must be
       a statement term for @('fni') with loop flag @('nil')
       returning type @('T') and affecting variables @('vars'),
       where each variable in @('vars')
       is a formal parameter of @('fni') with pointer type
       and where @('T') is not @('void') if @('vars') is @('nil').
       The return type of the C function represented by @('fni') is @('T').")
     (xdoc::li
      "If @('fni') is recursive, the unnormalized body must be
       a loop term for @('fni') affecting variables @('vars'),
       where each variable in @('vars')
       is a formal parameter of @('fni')."))
    (xdoc::p
     "The above-mentioned notions of
      (i) statement term for @('fni') with loop flag @('L')
      returning @('T') and affecting @('vars') and
      (ii) loop term for @('fni') affecting @('vars')
      are defined below, along with the notions of
      (iii) expression term for @('fni')
      returning @('T') and affecting @('vars'),
      (iv) pure expression term for @('fni')
      returning @('T'),
      (v) C type of a variable, and
      (vi) assignable variable.")

    (xdoc::p
     "A <i>statement term for</i> @('fni') with loop flag @('L')
      <i>returning</i> @('T') and <i>affecting</i> @('vars'),
      where @('fni') is a target function,
      @('L') is either @('t') or @('nil'),
      @('T') is either a C type or `boolean',
      and @('vars') is a list of distinct symbols,
      is inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "An expression term for @('fni')
       returning @('T') and affecting @('vars'),
       when @('L') is @('nil'),
       @('T') is a non-@('void') non-pointer C type,
       @('vars') is @('nil'),
       and @('fni') is not recursive.
       That is, an expression term returning a C value is also
       a statement term returning that that C value,
       affecting the same variables.
       This represents a C @('return') statement
       whose expression is represented by the same term,
       viewed as an expression term returning a C value.")
     (xdoc::li
      "A term @('var'),
       when @('L') is @('nil'),
       @('T') is @('void'),
       and @('vars') is the singleton list @('(var)').
       This represents no actual C code:
       it just serves to conclude
       preceding statements that may modify @('var'),
       but since ACL2 is functional,
       the possibly modified variable must be returned by the term.")
     (xdoc::li
      "A term @('(mv var1 ... varn)'),
       when  @('L') is @('nil'),
       @('T') is @('void'),
       and @('vars') is the list @('(var1 ... varn)') with @('n') &gt; 1.
       This represents no actual C code:
       it just serves to conclude
       preceding statements that may modify @('var1'), ..., @('varn'),
       but since ACL2 is functional,
       the possibly modified variables must be returned by the term.
       In translated terms,
       @('(mv var1 ... varn)') is
       @('(cons var1 (cons ... (cons varn \' nil)...))');
       this is the pattern that ATC looks for.")
     (xdoc::li
      "A call of @('fni') on variables identical to its formal parameters,
       when the C types or the variables are
       the same as the C types of the formal parameters,
       @('L') is @('t'),
       @('T') is @('void'),
       and @('fni') is recursive.
       This represents no actual C code:
       it just serves to conclude
       the computation in the body of the loop represented by @('fni').")
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test of the form @('(mbt ...)') or @('(mbt$ ...)'),
       (ii) a `then' branch that is
       a statement term for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars'), and
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
      "A call of @(tsee if) on
       (i) a test that is an expression term for @('fni') returning boolean and
       (ii) branches that are statement terms for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars').
       This represents a C @('if') conditional statement
       whose test expression is represented by the test term
       and whose branch blocks are represented by the branch terms.")
     (xdoc::li
      "A term @('(let ((var (declar term))) body)'),
       where the symbol name of @('var') is a portable ASCII C identifier
       as defined in Section `Portable ASCII C Identifiers' below,
       the symbol name of @('var') is distinct from
       the symbol names of all the other ACL2 variables in scope
       (function parameters and variables bound in enclosing @(tsee let)s),
       @('term') is an expression term for @('fni')
       returning a non-pointer C type and affecting no variables, and
       @('body') is a statement term for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars').
       This represents, as indicated by the wrapper @(tsee declar),
       a declaration of a C local variable represented by @('var'),
       initialized with the C expression represented by @('term'),
       followed by the C code represented by @('body').
       The C type of the variable is determined from the initializer.
       In translated terms,
       @('(let ((var (declar term))) body)') is
       @('((lambda (var) body) (declar term))');
       this is the pattern that ATC looks for.")
     (xdoc::li
      "A term @('(let ((var (assign term))) body)'),
       where @('var') is assignable,
       @('term') is an expression term for @('fni')
       returning the same C type as the C type of @('var')
       and affecting no variables, and
       @('body') is a statement term for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars').
       This represents, as indicated by the wrapper @(tsee assign),
       an assignment to
       the C local variable or function parameter represented by @('var'),
       with the C expression represented by @('term') as right-hand side,
       followed by the C code represented by @('body').
       In translated terms,
       @('(let ((var (assign term))) body)') is
       @('((lambda (var) body) (assign term))');
       this is the pattern that ATC looks for.")
     (xdoc::li
      "A term @('(let ((var term)) body)'),
       where @('var') is assignable,
       @('term') is a statement term for @('fni') with loop flag @('nil')
       returning @('void') and affecting @('var')
       that is
       either a call of a recursive target function @('fnj') with @('j < i')
       or an @(tsee if) whose test is an expression term returning boolean
       (not a test @('(mbt ...)') or @('(mbt$ ...)')), and
       @('body') is a statement term for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars').
       This represents the C code represented by @('term'),
       which may modify the variable represented by @('var'),
       followed by the C code represented by @('body').
       In translated terms,
       @('(let ((var term)) body)') is
       @('((lambda (var) body) term)');
       this is the pattern that ATC looks for.")
     (xdoc::li
      "A term @('(mv-let (var1 ... varn) term body)'),
       where @('n') &gt; 1,
       each @('vari') is assignable,
       @('term') is a statement term for @('fni') with loop flag @('nil')
       returning @('void') and affecting @('(var1 ... varn)')
       that is
       either a call of a recursive target function @('fnj') with @('j < i')
       or an @(tsee if) whose test is an expression term returning a boolean
       (not a test @('(mbt ...)') or @('(mbt$ ...)')), and
       @('body') is a statement term for @('fni') with loop flag @('L')
       returning @('T') and affecting @('vars').
       This represents the C code represented by @('term'),
       which may modify the variables represented by @('var1'), ..., @('varn'),
       followed by the C code represented by @('body').
       In translated terms,
       @('(mv-let (var1 ... varn) term body)') is
       @('((lambda (mv)
                   ((lambda (var1 ... varn) body)
                    (mv-nth \'0 mv)
                    ...
                    (mv-nth \'n-1 mv)))
           term)');
       this is the pattern that ATC looks for.")
     (xdoc::li
      "A call of a recursive target function @('fnj') with @('j < i'),
       on variables identical to its formal parameters,
       when the C types or the variables are
       the same as the C types of the formal parameters,
       @('L') is @('nil'),
       @('T') is @('void'),
       @('vars') is not @('nil'),
       and the body of @('fnj') is
       a loop term for @('fnj') affecting @('vars').
       This represents the C @('while') statement
       represented by the body of @('fnj'), as explained below."))

    (xdoc::p
     "A <i>loop term for</i> @('fni')
      <i>affecting</i> @('vars'),
      where @('fni') is a target function
      and  @('vars') is a non-empty list of distinct symbols,
      is inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A call of @(tsee if) on
       (i) a test of the form @('(mbt ...)') or @('(mbt$ ...)'),
       (ii) a `then' branch that is
       a loop term for @('fni') affecting @('vars'), and
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
      "A call of @(tsee if) on
       (i) a test that is an expression term for @('fni') returning boolean,
       (ii) a `then' branch that is
       a statement term for @('fni') with loop flag @('t')
       returning @('void') and affecting @('vars'), and
       (iii) an `else' branch that is
       either the variable @('var') when @('vars') is the singleton @('(var)'),
       or the term @('(mv var1 ... varn)')
       when @('vars') is the list @('(var1 ... varn)') with @('n') &gt; 1.
       All the variables in @('vars') must have C integer types.
       This represents the C @('while') statement
       whose controlling expression is represented by the test
       and whose body is represented by the `then' branch,
       as explained below;
       the `else' branch represents no actual C code,
       because it just serves to complete the @(tsee if)."))

    (xdoc::p
     "An <i>expression term for</i> @('fni')
      <i>returning</i> @('T') and
      <i>affecting</i> @('vars'),
      where @('fni') is a target function,
      @('T') is either a C type or `boolean',
      and @('vars') is a list of distinct symbols,
      is inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A pure expression term for @('fni') returning @('T'),
       when @('vars') is @('nil').")
     (xdoc::li
      "A call of a non-recursive target function @('fnj') with @('j < i'),
       on pure expression terms for @('fni') returning non-@('void') C types,
       where the types of the terms are equal to the
       the C types of the formal parameters of @('fnj')
       and where the body of @('fnj') is
       a statement term for @('fnj')
       returning @('T') and affeting @('vars').
       The restriction @('j < i') means that
       no (direct or indirect) recursion is allowed in the C code
       and the target functions must be specified
       in a topological order of their call graph.
       This represents a call of the corresponding C function."))

    (xdoc::p
     "A <i>pure expression term for</i> @('fni') <i>returning</i> @('T') is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A formal parameter of @('fni'),
       when @('T') is the type of the formal parameter.
       This represents the corresponding C formal parameter,
       as an expression.")
     (xdoc::li
      "A variable introduced by @(tsee let) with @(tsee declar)
       (as described above),
       when @('T') is the type of the variable.
       This represents the corresponding C local variable,
       as an expression.")
     (xdoc::li
      "A call of a function @('<type>-<base>-const') on a quoted integer,
       where @('<type>') is among"
      (xdoc::ul
       (xdoc::li "@('sint')")
       (xdoc::li "@('uint')")
       (xdoc::li "@('slong')")
       (xdoc::li "@('ulong')")
       (xdoc::li "@('sllong')")
       (xdoc::li "@('ullong')"))
      "and @('<base>') is among"
      (xdoc::ul
       (xdoc::li "@('dec')")
       (xdoc::li "@('oct')")
       (xdoc::li "@('hex')"))
      "when @('T') is the C type corresponding to @('<type>')
       and the quoted integer is non-negative and in the range of @('T').
       This represents a C integer constants
       of the C type indicated by the name of the function,
       expressed in decimal, octal, or hexadecimal base.")
     (xdoc::li
      "A call of a function @('<op>-<type>') on
       a pure expression term for @('fni') returning @('U'),
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
      "when @('T') is the C type corresponding to
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
       on pure expression terms for @('fni') returning @('U') and @('V'),
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
      "when @('T') is the C type corresponding to
       the return type of @('<op>-<type1>-<type2>'),
       @('U') is the C type corresponding to @('<type1>'), and
       @('V') is the C type corresponding to @('<type2>').
       This represents the C operator indicated by the name of the function
       applied to values of the types indicated by the name of the function.
       The guard verification requirement ensures that
       the operator yields a well-defined result.
       These functions covers all the C strict pure binary operators;
       the non-strict operators @('&&') and @('||'),
       and the non-pure operatos @('='), @('+='), etc.,
       are represented differently.")
     (xdoc::li
      "A call of a function @('<type1>-from-<type2>')
       on a pure expression term for @('fni') returning @('U'),
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
      "and also differ from each other,
       when @('T') is the C type corresponding to @('<type1>')
       and @('U') is the C type corresponding to @('<type2>').
       This represents
       a cast to the type indicated by the first part of the function name.
       The guard verification requirement ensures that
       the conversion yields a well-defined result.
       Even though conversions
       happen automatically in certain circumstances in C,
       these functions always represent explicit casts;
       implict conversions are represented implicitly,
       e.g. via the function for a unary operator that promoteds the operand.")
     (xdoc::li
      "A call of @('<type1>-array-read-<type2>')
       on expression terms for @('fni') returning @('U') and @('V'),
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
      "when @('T') is the C type correponding to @('<type1>'),
       @('U') is the pointer type to @('T'), and
       @('V') is the C type correponding to @('<type2>').
       This represents an array subscripting expression.
       The guard verification requirement ensures that
       the array access is well-defined.")
     (xdoc::li
      "A call of @(tsee sint-from-boolean) on
       an expression term for @('fni') returning boolean,
       when @('T') is @('int').
       This converts an expression term returning boolean
       to a pure expression term returning @('int').")
     (xdoc::li
      "A call of @(tsee condexpr) on
       a call of @(tsee if) on
       (i) a test that is an expression term for @('fni') returning boolean and
       (ii) branches that are
       pure expression terms for @('fni') returning @('T').
       This represents a C @('?:') conditional expression
       whose test expression is represented by the test term
       and whose branch expressions are represented by the branch terms."))

    (xdoc::p
     "An <i>expression term for</i> @('fni') <i>returning boolean</i> is
      inductively defined as one of the following:")
    (xdoc::ul
     (xdoc::li
      "A call of a function @('boolean-from-<type>')
       on a pure expression term for @('fni') returning @('U'),
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
      "when @('U') is the C type corresponding to @('<type>').
       This converts a pure expression term returning a C type
       to an expression term returning boolean.")
     (xdoc::li
      "A call of one of the following functions and macros
       on expression terms for @('fni') returning booleans:"
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
     "The <i>C type of a variable</i> @('var') is defined as follows:")
    (xdoc::ul
     (xdoc::li
      "If @('var') is a formal parameter,
       the C type is the one derived from the guard as explained earlier.")
     (xdoc::li
      "If @('var') is not a formal parameter,
       it must be introduced by a @(tsee let) with @(tsee declar),
       and its C type is the one of the term argument of @(tsee declar)."))

    (xdoc::p
     "A variable @('var') bound in
      a @(tsee let) or @(tsee mv-let) in a target function @('fni')
      is <i>assignable</i> when it is in scope,
      i.e. it is identical to a function parameter
      or to a variable bound in an enclosing @(tsee let) or @(tsee mv-let),
      and additionally any of the conditions given below holds.
      The conditions make reference to the C scopes
      represented by the ACL2 terms that
      the @(tsee let) or @(tsee mv-let) is part of:
      a function body is a C scope,
      and each @(tsee if) branch whose test is
      an expression term returning a boolean
      (i.e. whose test is not @(tsee mbt) or @(tsee mbt$))
      forms a new C scope.
      The conditions are the following:")
    (xdoc::ul
     (xdoc::li
      "The function parameter or outer variable
       is in the same C scope where @('var') occurs.")
     (xdoc::li
      "The variable @('var') is among @('vars'),
       i.e. it is being affected.")
     (xdoc::li
      "No variables are being affected, i.e. @('vars') is @('nil')."))
    (xdoc::p
     "Any of these conditions ensures that, in the ACL2 code,
      the old value of the variable cannot be accessed after the new binding:
      (i) if the first condition holds,
      the new binding hides the old variable;
      (ii) if the second condition holds,
      it means that the outer binding will receive the value
      at the end of the changes to the variables; and
      (iii) if the third condition holds,
      there is no subsequent code because there is no change to the variables.
      These justify destructively updating the variable in the C code.")

    (xdoc::p
     "Statement terms represent C statements,
      while expression terms represent C expressions.
      The expression terms returning booleans return ACL2 boolean values,
      while the statement terms,
      including expression terms returning C values,
      return ACL2 values that represent C values:
      the distinction between boolean terms and other kinds of terms
      stems from the need to represent C's non-strictness in ACL2:
      C's non-strict constructs are
      @('if') statements,
      @('?:') expressions,
      @('&&') expressions, and
      @('||') expressions;
      ACL2's only non-strict construct is @(tsee if)
      (which the macros @(tsee and) and @(tsee or) expand to, see above).
      Pure expression terms returning C values
      represent C expressions without side effects;
      C function calls may be side-effect-free,
      but in general we do not consider them pure,
      so they are represented by expression terms returning C values
      that are not pure expression terms returning C values.
      Expression terms returning booleans are always pure;
      so they do not need the explicit designation `pure'
      because they are the only expression terms returning booleans
      handled by ATC.
      Recursive ACL2 functions represent C loops,
      where those recursive functions are called.
      The loop flag @('L') serves to ensure that
      the body of a loop function ends with a recursive call
      on all paths (i.e. at all the leaves of its @(tsee if) structure,
      and that recursive calls of the loop function occur nowhere else.")

    (xdoc::p
     "The body of the C function represented by each non-recursive @('fni')
      is the compound statement consisting of
      the block items (i.e. statements and declarations)
      represented by the ACL2 function's body
      (which is a statement term).")

    (xdoc::p
     "The guard verification requirement ensures that
      the constraints about C types described above holds,
      for code reachable under guards.
      Code unreachable under guards is rare but possible.
      In order to generate C code that is always statically well-formed,
      ATC independently checks the constraints about C types.")

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

   (xdoc::evmac-section
    xdoc::*evmac-section-appconds-title*

    (xdoc::p
     "In addition to the requirements on the inputs stated above,
      the following "
     (xdoc::seetopic "acl2::event-macro-applicability-conditions"
                     "applicability conditions")
     " must be proved.
      The proofs are attempted when ATC is called.
      No hints can be supplied to ATC for these applicability conditions;
      (possibly local) lemmas must be provided before calling ATC
      that suffice for these applicability conditions
      to be proved without hints.")

    (xdoc::evmac-appcond
     ":natp-of-measure-of-fn"
     (xdoc::&&
      (xdoc::p
       "The measure of the recursive target function @('fn')
        must yield a natural number:")
      (xdoc::codeblock
       "(natp <fn-measure>)")
      (xdoc::p
       "where @('<fn-measure>') is the measure of @('fn').")
      (xdoc::p
       "There is one such applicability condition
        for each recursive target function @('fn').")))

    (xdoc::p
     "These applicability conditions do not need to be proved
      if @(':proofs') is @('nil')."))

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
      "This theorem may fail when some ACL2 target function
       includes unreachable code under the guard
       (other than the `else' branch of an @(tsee if)
       with an @(tsee mbt) or @(tsee mbt$) test)
       that represents C code that is not statically correct in C
       (e.g. that violates type checking).
       The reason is that currently ATC relies on ACL2's guard verification
       to ensure the the generated C code is statically correct;
       however, ACL2's static semantics involves the theorem prover,
       and is therefore stronger than C's static semantics.
       Thus, if this theorem fails, it is likely that
       some ACL2 target function includes unreachable code
       of the kind described above,
       which should be possible to avoid by rephrasing the function.
       Future versions of ATC
       will not rely solely on ACL2's guard verification
       to ensure the static correctness of the C code,
       but instead will check that based on C's weaker static semantics.")

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
     "A call of ATC is redundant if an only if
      it is identical to a previous successful call of ATC."))))
