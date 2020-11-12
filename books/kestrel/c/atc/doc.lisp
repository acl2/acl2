; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
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
     "ATC translates a subset of ACL2 to C.
      The ACL2 subset is designed to be close to C,
      i.e. to be essentially ``C written in ACL2'',
      so that it is easy to translate to C.
      ATC is meant to be used in conjunction with "
     (xdoc::seetopic "apt::apt" "APT")
     ": one uses APT transformations
      to refine ACL2 specifications and code
      to the subset recognized by ATC, which ATC translates to C.
      Thus, ATC can be used at the end of an APT derivation.")

    (xdoc::p
     "Currently ATC recognizes a very limited subset of ACL2
      and translates it to a very limited subset of C.
      This is just a first step (the development of ATC has just started);
      we plan to extend ATC to increasingly larger subsets of ACL2 and C.")

    (xdoc::p
     "We also generate, along with the C code,
      ACL2 proofs of the correctness of
      the output C code with respect to the input ACL2 code.
      This is based on a formal semantics of C,
      which we are also developing.")

    (xdoc::p
     "ATC is related to "
     (xdoc::seetopic "java::atj" "ATJ")
     ", the Java code generator for ACL2.
      Aside from the obvious difference in target languages,
      ATJ and ATC currently differ in their primary goals and emphases.
      ATJ was built to recognize, and translate to reasonable Java,
      essentially any ACL2 code
      (provided that it has side effects known to ATJ);
      ATJ also provides ways to exert finer-grained control
      on the generated Java,
      by using certain ACL2 types and operations
      that represent Java types and operations
      and that are translated to the corresponding Java constructs.
      In contrast, ATC is being built to recognize, and translate to C,
      only certain ACL2 types and operations
      that represent C types and operations
      and that are translated to the corresponding Java constructs;
      ATC does not attempt to translate arbitrary ACL2 to C.
      As a result, ATC is much simpler,
      thus making the generation of proofs easier.
      While there are plans to have ATJ generate proofs too,
      that is a larger task.
      In the future, ATC may be extended towards
      recognizing any ACL2 code and translating it to reasonable C,
      analogously to ATJ.
      Thus, while eventually ATJ and ATC may provide similar features,
      their starting points were different,
      which will keep the two tools different for some time to come."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(atc fn1 ... fn"
     "     :const-name  ...  ; default :auto"
     "     :output-file ...  ; no default"
     "     :verbose     ...  ; default nil"
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
      "In the rest of this documentation page,
       let @('*const*') be the symbol specified by this input."))

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
     "@(':verbose') &mdash; default @('nil')"
     (xdoc::p
      "Controls the amount of screen output:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to show all the output.")
      (xdoc::li
       "@('nil'), to suppress all the non-error output."))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Representation of C Code in ACL2"

    (xdoc::p
     "For now ATC supports the ACL2 representation of
      a single C translation unit (which goes into the generated file).
      This translation unit consists of one or more C function definitions.")

    (xdoc::p
     "Each C function definition is represented by
      a corresponding ACL2 function definition.
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
      The nams of these symbols are used as
      the names of the formal parameters of the corresponding C function,
      in the same order.
      Therefore, the formal parameters of each @('fni')
      must have must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).")

    (xdoc::p
     "The guard of each @('fni') must include conjuncts of the form
      @('(sintp x)') for every formal parameter @('x').
      The conjuncts may be at any level of nesting,
      but must be easily extractable by flattening
      the @(tsee and) structure of the guard term.
      Thus, all the formal parameters of the C function represented by @('fni')
      have type @('int');
      the rest of the guard (i.e. additional requirements)
      are not explicitly represented in the C code.
      The C function returns an @('int') result;
      that this is the correct return type
      is guaranteed by the restrictions given below.")

    (xdoc::p
     "Each function @('fni') must be in logic-mode and guard-verified.
      It must have an "
     (xdoc::seetopic "acl2::function-definedness" "unnormalized body")
     " consisting exclusively of:")
    (xdoc::ul
     (xdoc::li
      "The formal parameters of the function.
       These represent the corresponding C formal parameters.")
     (xdoc::li
      "Calls of @(tsee sint-const) on quoted integers.
       These represent C integer constants of type @('int').
       The guard verification requirement ensures that
       the quoted integer is within the range of type @('int').")
     (xdoc::li
      "Calls of the following functions on recursively allowed terms:"
      (xdoc::ul
       (xdoc::li "@(tsee sint-plus)")
       (xdoc::li "@(tsee sint-minus)")
       (xdoc::li "@(tsee sint-bitnot)")
       (xdoc::li "@(tsee sint-lognot)")
       (xdoc::li "@(tsee sint-add)")
       (xdoc::li "@(tsee sint-sub)")
       (xdoc::li "@(tsee sint-mul)")
       (xdoc::li "@(tsee sint-div)")
       (xdoc::li "@(tsee sint-rem)")
       (xdoc::li "@(tsee sint-shl-sint)")
       (xdoc::li "@(tsee sint-shr-sint)")
       (xdoc::li "@(tsee sint-lt)")
       (xdoc::li "@(tsee sint-gt)")
       (xdoc::li "@(tsee sint-le)")
       (xdoc::li "@(tsee sint-ge)")
       (xdoc::li "@(tsee sint-eq)")
       (xdoc::li "@(tsee sint-ne)")
       (xdoc::li "@(tsee sint-bitand)")
       (xdoc::li "@(tsee sint-bitxor)")
       (xdoc::li "@(tsee sint-bitior)"))
      "Each such call represents the corresponding C operator,
       applied to C @('int') values.
       The guard verification requirement ensures that
       they are always applied to values with a well-defined result,
       and that result is an @('int') value.")
     (xdoc::li
      "Calls of @(tsee if) on
       (i) tests that are calls of @(tsee sint-nonzerop)
       on recursively allowed terms, and
       (ii) branches that are recursively allowed terms.
       The function @(tsee sint-nonzerop) serves to convert
       (the ACL2 representation of) a C @('int') to an ACL2 boolean,
       which is needed for the ACL2 @(tsee if) calls.
       An ACL2 call of @(tsee sint-nonzerop) represents, in C,
       what its ACL2 argument represents:
       that is, the @(tsee sint-nonzerop) is dropped in the translation to C,
       so that the C test has type @('int').
       An ACL2 @(tsee if) represents
       either a C @('if') conditional statement
       or a C @('?:') conditional expression,
       as explained below.")
     (xdoc::li
      "Calls @('(sint01 (and (sint-nonzerop a) (sint-nonzerop b)))')
       where @('a) and @('b') are recursively allowed terms.
       These calls represent the C non-strict @('&&') operator,
       applied to the C expressions represented by @('a') and @('b').
       The conversion @(tsee sint-nonzerop) of the operands to ACL2 booleans
       is necessary to represent C's non-strictness in ACL2,
       but the result must be converted back via @(tsee sint01)
       to a C @('int'), which is what @('&&') returns.
       (Note that, in ACL2's translated terms,
       @('(and x y)') is @('(if x y \'nil)').)")
     (xdoc::li
      "Calls @('(sint01 (or (sint-nonzerop a) (sint-nonzerop b)))')
       where @('a) and @('b') are recursively allowed terms.
       These calls represent the C non-strict @('||') operator,
       applied to the C expressions represented by @('a') and @('b').
       The conversion @(tsee sint-nonzerop) of the operands to ACL2 booleans
       is necessary to represent C's non-strictness in ACL2,
       but the result must be converted back via @(tsee sint01)
       to a C @('int'), which is what @('||') returns.
       (Note that, in ACL2's translated terms,
       @('(or x y)') is @('(or x x y)').)"))
    (xdoc::p
     "The above restrictions imply that @('fni') returns a single result,
      i.e. not an @(tsee mv) result.
      By construction, this result has C type @('int').")

    (xdoc::p
     "The body statement of the C function represented by each @('fni')
      is obtained by translating the ACL2 function's body as follows.
      If the body is not an @(tsee if),
      it is translated to a single C @('return') statement
      with the expression derived from the body
      according to the correspondence outlined above;
      in this case, any @(tsee if)s are turned into conditional expressions.
      If the body is an @(tsee if),
      it is turned into a C @('if') statement,
      whose test expression is derived from the ACL2 test term
      and whose branches are recursively translated
      in the same manner as the body.
      Thus, if a branch is also an @(tsee if),
      it is turned into a nested @('if') statement.
      Eventually non-@(tsee if) branches are reached,
      and they are turned into @('return') statements.
      Other calls of @(tsee if), e.g. arguments of non-@(tsee if) functions,
      are turned into C conditional expressions.
      Thus, depending on where an @(tsee if) occurs,
      it may represent either a statement or an expression,
      according to an easily predictable algorithm.")

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
        "enum       return     volatile   _Thread_local")))

     (xdoc::p
      "The C18 standard allows the following characters in identifiers:")
     (xdoc::ol
      (xdoc::li
       "The ten digits (but not in the starting position).
       Even though C18 does not prescribe the use of (a superset of) ASCII,
       these have obvious ASCII counterparts.")
      (xdoc::li
       "The 26 uppercase Latin letters,
       the 26 lowercase Latin letter,
       and the underscore.
       Even though C18 does not prescribe the use of (a superset of) ASCII,
       these have obvious ASCII counterparts.")
      (xdoc::li
       "Some ranges of universal characters
       (some of which cannot occur in the starting position),
       none of which are ASCII.")
      (xdoc::li
       "Other implementation-defined characters.
       These are not portable."))
     (xdoc::p
      "Thus, portable ASCII C identifiers consists of only 1 and 2 above,
      excluding 3 (non-ASCII) and 4 (non-portable).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Constant"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defconst *const* ...)")
     (xdoc::p
      "where @('...') is the abstract syntax tree of
       the generated C translation unit,
       which ATC also pretty-prints and
       writes to the file specified by the @(':output-file') input."))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Theorems"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defthm *const*-well-formed ...)")
     (xdoc::p
      "where @('...') is a theorem about @('*const*') stating that
       the generated (abstract syntax tree of the) translation unit
       is statically well-formed,
       i.e. it compiles according to the C18 standard.")

     (xdoc::p
      "For each target function @('fn'), ATC generates an event")
     (xdoc::codeblock
      "(defthm *const*-fn-correct ...)")
     (xdoc::p
      "where @('...') is a theorem about @('fn') and @('*const*') stating that,
       under the guard of @('fn'),
       executing the C dynamic semantics on
       the C function generated from @('fn')
       yields the same result as the function @('fn').
       That is,
       the C function is functionally equivalent to the ACL2 function.")))

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
       one can write a separate C file with a @('main') function
       that calls the generated functions,
       and compile both files together.
       By default, an executable @('a.out') will be generated
       (if using @('gcc') on macOS or Linux).")

     (xdoc::p
      "The directory @('[books]/kestrel/c/atc/tests')
       contains some examples of generated C code
       and handwritten C code to test it.")))))
