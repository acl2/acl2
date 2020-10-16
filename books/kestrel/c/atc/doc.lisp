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
     "Currently ATC recognizes and translates
      a very limited subset of ACL2 to a very limited subset of C.
      This is just a first step (the development of ATC has just started);
      we plan to extend ATC to increasingly larger subsets of ACL2 and C.")

    (xdoc::p
     "We also aim at generating, along with the C code,
      an ACL2 proof of the correctness of
      the output C code with respect to the input ACL2 code.
      This requires a formal semantics of C,
      which we are also developing.")

    (xdoc::p
     "ATC is related to "
     (xdoc::seetopic "java::atj" "ATJ")
     ", the Java code generator for ACL2.
      Aside from the obvious difference in target languages,
      ATJ and ATC currently differ in their primary goals and emphases.
      ATJ was built to recognize, and translate to reasonable Java,
      essentially any ACL2 code (provided that it has known side effects);
      ATJ also provides ways to extert finer-grained on the generated Java,
      by using certain ACL2 types and operations
      that represent Java types and operations
      and that are translated to the corresponding Java constructs.
      In contrast, ATC is being built to recognize, and translate to C,
      only certain ACL2 types and operations
      that represent C types and operations
      and that are translated to the corresponding Java constructs;
      ATC does not attempt to turn any ACL2 into C.
      As a result, ATC is much simpler,
      and should thus make the generation of proofs easier.
      While there are plans to have ATJ generate proofs too,
      that is a larger task.
      Furthermore, ATC may be extended
      towards recognizing any ACL2 code and translating it to reasonable C,
      analogously to ATJ.
      Thus, while eventually ATJ and ATC may provide similar features,
      their starting points were different,
      which will keep the two tools different for some time to come."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(atc fn1 ... fn"
     "     :output-file ..."
     "     :verbose     ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('fn1'), ..., @('fnp')"
     (xdoc::p
      "Names of target ACL2 functions to translate to C.")
     (xdoc::p
      "Each @('fni') must be a symbol that names a function
       that satisfies the following conditions:")
     (xdoc::ul
      (xdoc::li
       "The name of the symbol @('fni')
        is a C identifier as defined in Section `C Identifiers' below.")
      (xdoc::li
       "The name of each symbol that is a formal argument of @('fni')
        is a C identifier as defined in Section `C Identifiers' below.")
      (xdoc::li
       "The formal arguments must have must have symbol names
        that are all distinct.
        Even if they are in different packages,
        they must have distinct symbol names
        (the package names are ignored for this purpose).")
      (xdoc::li
       "The function @('fni') is in logic mode and guard-verified.")
      (xdoc::li
       (xdoc::p
        "The function @('fni') has an "
        (xdoc::seetopic "acl2::function-definedness" "unnormalized body")
        " consisting exclusively of:")
       (xdoc::ul
        (xdoc::li
         "The formal parameters of the function.")
        (xdoc::li
         "Calls of @(tsee sint-const) on quoted integers.")
        (xdoc::li
         "Calls of @(tsee sint-plus) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-minus) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-add) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-sub) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-mul) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-div) on recursively allowed terms.")
        (xdoc::li
         "Calls of @(tsee sint-rem) on recursively allowed terms.")))
      (xdoc::li
       "The guard of @('fni') includes conjuncts of the form
        @('(sintp x)') for every formal parameter @('x').
        The conjuncts may be at any level of nesting,
        but must be easily extractable by flattening
        the @(tsee and) structure of the guard term."))
     (xdoc::p
      "The above conditions imply that @('fni') returns a single result,
       i.e. not an @(tsee mv) result.")
     (xdoc::p
      "The target functions must have symbol names
       that are all distinct.
       Even if they are in different packages,
       they must have distinct symbol names
       (the package names are ignored for this purpose)."))

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
      "@('nil'), to suppress all the non-error output.")))

   (xdoc::h4 "C Identifiers")

   (xdoc::p
    "For the purpose of ATC, we define C identifiers as
     non-empty sequences of ASCII characters that:")
   (xdoc::ul
    (xdoc::li
     "Consist of only
      the 26 uppercase Latin letters,
      the 26 lowercase Latin letters,
      the 10 numeric digits,
      and the underscore.")
    (xdoc::li
     "Start with a letter or underscore.")
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
    "The C18 standard allows a possibly broader range of valid identifiers,
     but the ones recognized by ATC are a portable subset."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated C Code")

   (xdoc::p
    "ATC generates a single C file that contains
     a C function for each target ACL2 function @('fni').
     The C function is defined as follows:")
   (xdoc::ul
    (xdoc::li
     "Its name is the symbol name of @('fni').
      The package of the symbol is ignored.")
    (xdoc::li
     "Its formal parameters are the symbol names of
      the formal parameters of @('fni').
      The packages of the symbols are ignored.
      The parameters are in the same order.")
    (xdoc::li
     "The types of the formal parameters are all @('int').")
    (xdoc::li
     "The result type is @('int').")
    (xdoc::li
     "The body of the function is obtained by translating
      the ACL2 terms described earlier
      to the corresponding C constructs."))

   (xdoc::p
    "The condition, stated earlier, that @('fni') is guard-verified
     implies that the generated C operations
     never exhibit undefined behavior,
     provided that they are called with values
     whose ACL2 counterparts satisfy the guard of @('fni').")

   (xdoc::p
    "The C functions are generated in the same order in which
     the target functions are listed, i.e. @('fn1') first, etc.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Compiling and Running the C Code")

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
     (if using @('gcc') on macOS or Linux).")))
