; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj

  :parents (java)

  :short "ATJ (<b>A</b>CL2 <b>T</b>o <b>J</b>ava)
          is a Java code generator for ACL2."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::p
    "This manual page contains user-level reference documentation for ATJ.
     If you are new to ATJ, you should start with the "
    (xdoc::seetopic "atj-tutorial" "tutorial")
    ", which provides user-level information
     on how ATJ works and how to use ATJ effectively.
     Some of the material in this manual page
     will likely be moved to the tutorial,
     which is in progress.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "ATJ translates ACL2 to Java,
     enabling ACL2 code to be used in Java code
     (in the sense explained below).")

   (xdoc::p
    "For instance, ATJ is useful
     to generate Java code at the end of an "
    (xdoc::seetopic "apt::apt" "APT")
    " program synthesis derivation.")

   (xdoc::p
    "This manual page provides reference documentation for ATJ.
     A separate tutorial in being written, as noted above.
     See the files under @('[books]/kestrel/java/atj/tests/')
     for examples of use of ATJ.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Scope")

   (xdoc::p
    "ATJ translates ACL2 named functions to corresponding Java code
     whose execution mimics the execution of the ACL2 functions.")

   (xdoc::p
    "The ACL2 functions accepted by ATJ may manipulate any ACL2 value: "
    (xdoc::seetopic "acl2::characters" "characters") ", "
    (xdoc::seetopic "acl2::strings" "strings") ", "
    (xdoc::seetopic "acl2::symbols" "symbols") ", "
    (xdoc::seetopic "acl2::numbers" "numbers") ", and "
    (xdoc::seetopic "acl2::conses" "cons pairs") ". "
    "The Java code that corresponds to the ACL2 functions
     manipulates Java representations of the ACL2 values.")

   (xdoc::p
    "ATJ accepts all the ACL2 functions that
     (1) have either an "
    (xdoc::seetopic "acl2::ubody" "unnormalized body")
    " or an attachment and
     (2) either do not have raw Lisp code
     or have raw Lisp code but belong to a whitelist
     (but also see the @(':ignore-whitelist') option below).
     The ACL2 functions with raw Lisp code
     are the ones for which @(tsee rawp) holds;
     of these, the ones in the whitelist
     are the ones for which @(tsee pure-raw-p) holds.
     The unnormalized body of the functions in the whitelist
     is functionally equivalent to their raw Lisp code.
     The Java code that corresponds to
     the ACL2 functions that satisfy conditions (1) and (2) above,
     mimics the computations described by their unnormalized body.
     In the case of functions
     without an unnormalized body but with an attachment,
     (a call of) the attached function (on the formal arguments)
     plays the role of the unnormalized body.")

   (xdoc::p
    "ATJ also accepts the ACL2 function @(tsee return-last)
     (which has raw Lisp code and is not in the whitelist),
     but only when its first argument is
     @('acl2::mbe-raw1') or @('acl2::progn').
     Calls of the form @('(return-last 'acl2::mbe1-raw ...)')
     are translated representations of calls of @(tsee mbe);
     ATJ translates to Java
     either the @(':logic') or the @(':exec') part of these calls,
     as detailed below.
     Calls of the form @('(return-last 'acl2::progn ...)')
     are translated representations
     of calls of @(tsee prog2$) and @(tsee progn$);
     ATJ translates to Java the last argument of these calls,
     as detailed below.")

   (xdoc::p
    "ATJ also accepts all the "
    (xdoc::seetopic "acl2::primitive" "ACL2 primitive functions") ". "
    "The Java code that corresponds to these ACL2 functions
     has the input/output behavior documented for these functions.")

   (xdoc::p
    "ATJ accepts both logic-mode and program-mode functions.")

   (xdoc::p
    "Some ACL2 functions have side effects when executed,
     e.g. @(tsee hard-error) prints an error message
     and returns control to the top level.
     All the ACL2 functions with side effects have raw Lisp code
     and are not in the whitelist mentioned above.
     Therefore, the generated Java code
     does not mimic any of the side effects exhibited by ACL2 functions.
     In particular, calls of @(tsee prog2$) and @(tsee progn$) are accepted
     (as explained above about @(tsee return-last)
     with first argument @('acl2::progn'))
     only if their non-last arguments are free of side effects.
     Support for translating ACL2 functions with side effects
     to Java code that mimics those side effects
     may be added in the future.")

   (xdoc::p
    "ATJ does not accept functions that access "
    (xdoc::seetopic "acl2::stobj" "stobjs") ". "
    "Support for stobjs, and destructive updates of stobjs,
     may be added in the future.")

   (xdoc::p
    "ATJ does not translate "
    (xdoc::seetopic "defmacro" "macro definitions")
    " to Java code.
     However, the use of macros in function bodies is fully supported,
     because ATJ operates on ACL2 translated terms,
     where macros are expanded.")

   (xdoc::p
    "ATJ does not translate "
    (xdoc::seetopic "defconst" "named constant definitions")
    " to Java code.
     However, the use of named constants in function bodies is fully supported,
     because ATJ operates on ACL2 translated terms,
     where constants are expanded.")

   (xdoc::p
    "The generated Java code can be called by external Java code,
     but not vice versa.
     The ability to have the generated Java code call external Java code
     may be added in the future;
     this may involve the use of ACL2 stubs corresponding to
     the Java code to be invoked by the (Java-translated) ACL2 code.")

   (xdoc::p
    "External Java code can call the generated Java code
     on (Java representations of) explicit ACL2 values.
     Access to global variables
     like @(tsee state) or user-defined "
    (xdoc::seetopic "acl2::stobj" "stobjs")
    " is therefore not supported;
     in particular, the generated Java code has no access to
     the ACL2/Lisp environment.
     Support for global variables, in particular @(tsee state),
     may be added in the future.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Approach")

   (xdoc::p
    "ATJ is supported by "
    (xdoc::seetopic "aij" "AIJ")
    ", which is a deep embedding in Java
     of the executable subset of ACL2
     (subject to the limitations outlined above).")

   (xdoc::p
    "ATJ translates the target ACL2 functions into Java representations,
     based on their unnormalized bodies or attachments.
     It does so recursively,
     starting from the top-level functions specified by the user
     and stopping at the ACL2 functions that
     either are implemented natively in AIJ
     or (under certain conditions; see below)
     represent Java primitive operations or primitive array operations.
     If a function is encountered that
     is not natively implemented in AIJ
     and has no unnormalized body and no attachment,
     ATJ stops with an error.
     If a function is encountered that has raw Lisp code
     and is not in the whitelist
     (except for the treament of @(tsee return-last) explained above),
     ATJ stops with an error.")

   (xdoc::p
    "ATJ generates Java code with public methods to
     (1) initialize the AIJ's Java representation of the ACL2 environment and
     (2) call the Java representations of the ACL2 functions
     on Java representations of ACL2 values
     (see the `Generated Java Code' section for details).
     AIJ provides public classes and methods to translate
     certain Java values to AIJ's Java representations of ACL2 values
     and vice versa.
     Thus, by loading into the Java Virtual Machine
     both AIJ and the Java code generated by ATJ,
     external Java code can ``use'' ACL2 code.")

   (xdoc::p
    "ATJ generates either deeply embedded or shallowly embedded
     Java representations of the ACL2 functions.
     The choice is controlled by a user option.")

   (xdoc::h4 "Deep Embedding")

   (xdoc::p
    "In the deep embedding approach,
     ATJ generates Java code to build
     the deeply embedded ACL2 functions,
     and to call and execute them via AIJ's interpreter.")

   (xdoc::p
    "This deep embedding approach is simple and thus fairly high-assurance.
     On the other hand, the Java code is not efficient or idiomatic.
     However, the approach may work well for some simple applications.")

   (xdoc::h4 "Shallow Embedding")

   (xdoc::p
    "In the shallow embedding approach,
     ATJ generates Java code that mimics the computations of
     the shallowly embedded ACL2 functions,
     one Java method for each ACL2 function.
     These methods are executed without using AIJ's interpreter.
     However, the shallowly embedded ACL2 functions still use
     AIJ's representation of the ACL2 values
     and AIJ's native implementations of ACL2 functions.
     Under certain conditions,
     the shallowly embedded ACL2 functions use Java values
     that are not AIJ's Java representations of ACL2 values;
     see below for details.")

   (xdoc::p
    "This shallow embedding approach
     is more complex than the deep embedding approach,
     but produces code that is more efficient and more idiomatic.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(atj fn1 ... fnp"
    "     :deep             ..."
    "     :guards           ..."
    "     :java-package     ..."
    "     :java-class       ..."
    "     :output-dir       ..."
    "     :tests            ..."
    "     :ignore-whitelist ..."
    "     :verbose          ..."
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('fn1'), ..., @('fnp')"
    (xdoc::p
     "Names of the target ACL2 functions to be translated to Java.")
    (xdoc::p
     "Each @('fni') must be a symbol that names a function that
      either has an unnormalized body
      and no raw Lisp code (unless it is in the whitelist;
      but also see the @(':ignore-whitelist') option below),
      or has an attachment,
      or is natively implemented in AIJ.
      Each of these functions must have
      no input or output " (xdoc::seetopic "acl2::stobj" "stobjs") ".
      Each of these functions must transitively call
      (in the unnormalized body or attachment,
      if not natively implemented in AIJ)
      only functions that satisfy the same constraints,
      except for calls of @(tsee return-last) as described below.")
    (xdoc::p
     "None of the @('fni') functions may be @(tsee return-last).
      However, the @('fni') functions may transitively call @(tsee return-last),
      under two possible conditions:")
    (xdoc::ul
     (xdoc::li
      "The first argument of @(tsee return-last) is @('acl2::mbe-raw1'),
       i.e. the call results from the translation of @(tsee mbe).
       Even though Java code is generated
       for one of the second and third arguments but not for the other one
       (based on the @(':guars') input; see below),
       the restrictions on called functions,
       and in particular the absence of side effects,
       are enforced on all the argument of the call.")
     (xdoc::li
      "The first argument of @(tsee return-last) is @('acl2::progn'),
       i.e. the call results from the translation of
       @(tsee prog2$) or @(tsee progn$).
       Even though Java code is generated
       for the last argument of the call
       but not for the previous one(s),
       the restrictions on called functions,
       and in particular the absence of side effects,
       are enforced on all the argument of the call."))
    (xdoc::p
     "If the @(':deep') input is @('nil') and the @(':guards') input is @('t'),
      then none of the @('fni') may be
      one of the functions listed in @(tsee *atj-jprim-fns*) or
      one of the functions listed in @(tsee *atj-jprimarr-fns*).
      These functions are treated specially
      in the shallow embedding when guard satisfaction is assumed (see below).")
    (xdoc::p
     "There must be at least one function, i.e. @('p') &gt; 0.
      All the @('fni') names must be distinct."))

   (xdoc::desc
    "@(':deep') &mdash; default @('nil')"
    (xdoc::p
     "Chooses the deep or shallow embedding approach described above:")
    (xdoc::ul
     (xdoc::li
      "@('t'), for the deep embedding.")
     (xdoc::li
      "@('nil'), for the shallow embedding.")))

   (xdoc::desc
    "@(':guards') &mdash; default @('t')"
    (xdoc::p
     "Specifies whether the generated code
      should assume that all the guards are satisfied or not:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to assume that they are satisfied.
       In this case, the generated code may run faster;
       in particular, only the @(':exec') part of @(tsee mbe) is executed.
       Furthermore, if the @(':deep') input is @('nil'),
       the Java methods in the generated code
       have the argument and return types
       specified via @(tsee atj-main-function-type)
       and @(tsee atj-other-function-type)
       (see the `Generated Java Code' section for more information),
       and the generated Java code may manipulate
       Java primitive values and Java primitive arrays directly.")
     (xdoc::li
      "@('nil'), to not assume that the guards are satisfied.
       In this case, the generated code runs ``in the logic'';
       in particular, only the @(':logic') part of @(tsee mbe) is executed."))
    (xdoc::p
     "Regardless of the value of this input,
      the generated code never checks guards.
      The difference is whether guards are ignored altogether
      (i.e. execution ``in the logic'')
      or assumed to hold
      (i.e. possibly faster execution).
      This input should be @('t') only when generating Java code
      from guard-verified ACL2 code.
      Furthermore, external Java code that calls the generated code
      should do so only with values that satisfy
      the guards of the called ACL2 functions, if this input is @('t').
      Otherwise, erroneous computations may occur."))

   (xdoc::desc
    "@(':java-package') &mdash; default @('nil')"
    (xdoc::p
     "Name of the Java package of the generated Java code.")
    (xdoc::p
     "It must be either an ACL2 string or @('nil').
      If it is an ACL2 string,
      it must be a valid Java package name consisting of only ASCII characters;
      it must also be distinct from AIJ's Java package name,
      i.e. @('edu.kestrel.acl2.aij').
      If this input is @('nil'), the generated Java code
      is in an unnamed Java package."))

   (xdoc::desc
    "@(':java-class') &mdash; default @('nil')"
    (xdoc::p
     "Name of the generated Java class.")
    (xdoc::p
     "It must be either an ACL2 string or @('nil').
      If it is an ACL2 string,
      it must be a valid Java class name consisting of only ASCII characters.
      If this input is @('nil'),
      the generated Java class is called @('Acl2Code').")
    (xdoc::p
     "An additional auxiliary class is generated,
      whose name is obtained by appending @('Environment')
      at the end of the name of the main class.
      This auxiliary class contains boilerplate code
      to build a Java representation of the ACL2 environment
      (i.e. ACL2 package definitions,
      and also ACL2 function definitions if the @(':deep') input is @('t')).")
    (xdoc::p
     "If the @(':tests') input (see below) is not @('nil'),
      a third Java class for testing is generated,
      whose name is obtained by appending @('Tests')
      at the end of the name of the main class."))

   (xdoc::desc
    "@(':output-dir') &mdash; default @('\".\"')"
    (xdoc::p
     "Path of the directory where
      the generated Java files are created.")
    (xdoc::p
     "It must be an ACL2 string that is
      a valid path to a directory in the file system;
      the path may be absolute,
      or relative to
      the " (xdoc::seetopic "cbd" "current working directory") ".")
    (xdoc::p
     "One file per class is generated:
      two files if the @(':tests') input is @('nil'),
      three files otherwise.
      The name of each generated file
      is the name of the corresponding class followed by @('.java').
      If the file already exists, it is overwritten."))

   (xdoc::desc
    "@(':tests') &mdash; default @('nil')"
    (xdoc::p
     "Optional tests to generate Java code for.")
    (xdoc::p
     "This input must evaluate to a list of doublets
      @('((name1 term1) ... (nameq termq))'),
      where each @('namej') is a string consisting of only letters and digits,
      and each @('termj') is an untranslated ground term
      whose translation is @('(fn in1 in2 ...)'),
      where @('fn') is among the target functions @('fn1'), ..., @('fnp'),
      @('fn') returns single results (i.e. not "
     (xdoc::seetopic "mv" "multiple results")
     ") (support for generating tests for functions that return multiple results
      will be added in the future),
      and each @('in') among @('in1'), @('in2')
      satisfies the following conditions:")
    (xdoc::ul
     (xdoc::li
      "If @(':deep') is @('t') or @(':guards') is @('nil'),
       then @('in') must be a quoted constant.")
     (xdoc::li
      "If @(':deep') is @('nil') and @(':guards') is @('t'),
       then requirements on @('in') depend on the type assigned,
       via @(tsee atj-main-function-type),
       to the input of @('fn') corresponding to @('in'):"
      (xdoc::ul
       (xdoc::li
        "If the type is @(':a...'),
         then @('in') must be a quoted constant.")
       (xdoc::li
        "If the type is @(':jboolean'),
         then @('in') must be a term @('(java::boolean-value <boolean>)')
         where @('<boolean>') is a quoted boolean (i.e. @('t') or @('nil')).")
       (xdoc::li
        "If the type is @(':jchar'),
         then @('in') must be a term @('(java::char-value <char>)')
         where @('<char>') is a quoted unsigned 16-bit integer.")
       (xdoc::li
        "If the type is @(':jbyte'),
         then @('in') must be a term @('(java::byte-value <byte>)')
         where @('<byte>') is a quoted signed 8-bit integer.")
       (xdoc::li
        "If the type is @(':jshort'),
         then @('in') must be a term @('(java::short-value <short>)')
         where @('<short>') is a quoted signed 16-bit integer.")
       (xdoc::li
        "If the type is @(':jint'),
         then @('in') must be a term @('(java::int-value <int>)')
         where @('<int>') is a quoted signed 32-bit integer.")
       (xdoc::li
        "If the type is @(':jlong'),
         then @('in') must be a term @('(java::long-value <long>)')
         where @('<long>') is a quoted signed 64-bit integer.")
       (xdoc::li
        "If the type is @(':jboolean[]'),
         then @('in') must be a term
         @('(java::boolean-array-new-init <booleans>)')
         where @('<booleans>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::boolean-value <boolean>)')
         as in the case above in which the type is @(':jboolean').")
       (xdoc::li
        "If the type is @(':jchar[]'),
         then @('in') must be a term
         @('(java::char-array-new-init <chars>)')
         where @('<chars>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::char-value <char>)')
         as in the case above in which the type is @(':jchar').")
       (xdoc::li
        "If the type is @(':jbyte[]'),
         then @('in') must be a term
         @('(java::byte-array-new-init <bytes>)')
         where @('<bytes>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::byte-value <byte>)')
         as in the case above in which the type is @(':jbyte').")
       (xdoc::li
        "If the type is @(':jshort[]'),
         then @('in') must be a term
         @('(java::short-array-new-init <short>)')
         where @('<short>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::short-value <short>)')
         as in the case above in which the type is @(':jshort').")
       (xdoc::li
        "If the type is @(':jint[]'),
         then @('in') must be a term
         @('(java::int-array-new-init <ints>)')
         where @('<ints>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::int-value <int>)')
         as in the case above in which the type is @(':jint').")
       (xdoc::li
        "If the type is @(':jlong[]'),
         then @('in') must be a term
         @('(java::long-array-new-init <longs>)')
         where @('<longs>') is the translation of
         a term @('(list <elem1> <elem2> ...)')
         where each @('<elem>') is a term @('(java::long-value <long>)')
         as in the case above in which the type is @(':jlong')."))))
    (xdoc::p
     "All the @('namej') strings must be distinct.")
    (xdoc::p
     "Each doublet @('(namej termj)') specifies a test,
      in which the result of @('(fn in1 in2 ...)') calculated by ACL2
      is compared with the result of the same call
      calculated via the generated Java code for @('fn').
      These tests can be run via additional generated Java code
      (see below).")
    (xdoc::p
     "Note that the @(':tests') input is evaluated.")
    (xdoc::p
     "Test inputs of the form
      @('(java::boolean-value <boolean>)'),
      @('(java::char-value <char>)'),
      @('(java::byte-value <byte>)'),
      @('(java::short-value <short>)'),
      @('(java::int-value <int>)'),
      @('(java::long-value <long>)'),
      @('(java::boolean-array-new-init <booleans>)'),
      @('(java::char-array-new-init <chars>)'),
      @('(java::byte-array-new-init <bytes>)'),
      @('(java::short-array-new-init <shorts>)'),
      @('(java::int-array-new-init <ints>)'), or
      @('(java::long-array-new-init <longs>)')
      can be used only for ACL2 functions that have
      the ATJ type
      @(':jboolean'),
      @(':jchar'),
      @(':jbyte'),
      @(':jshort'),
      @(':jint'),
      @(':jlong'),
      @(':jboolean[]'),
      @(':jchar[]'),
      @(':jbyte[]'),
      @(':jshort[]'),
      @(':jint[]'), or
      @(':jlong[]')
      assigned to the corresponding argument
      via @(tsee atj-main-function-type)."))

   (xdoc::desc
    "@(':ignore-whitelist') &mdash; default @('nil')."
    (xdoc::p
     "If @('t'), this tells ATJ to ignore
      the whitelist of functions with raw Lisp code,
      i.e. to accept any function with raw Lisp code,
      provided that it has an unnormalized body.
      This means that any side effects that happen in ACL2 execution
      will not happen in the generated Java code.
      This should be only used in special circumstances,
      e.g. when the non-whitelisted functions
      are unreachable under guard verification."))

   (xdoc::desc
    "@(':verbose') &mdash; default @('nil')"
    (xdoc::p
     "Controls the amount of screen output:")
    (xdoc::ul
     (xdoc::li
      "@('t'), to show all the output.")
     (xdoc::li
      "@('nil'), to suppress all the non-error output.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated Java Code")

   (xdoc::p
    "ATJ generates a Java file that contains
     a single public class named as specified by the @(':java-class') input,
     in the package specified by the @(':java-package') input.")

   (xdoc::codeblock
    "// if :deep is t:"
    "public class <name> {"
    "    ..."
    "    public static void initialize() ..."
    "    public static Acl2Value"
    "        call(Acl2Symbol function, Acl2Value[] arguments) ..."
    "}"
    ""
    "// if :deep is nil:"
    "public class <name> {"
    "    ..."
    "    public static void initialize() ..."
    "    public static class <pkg> {"
    "        public static <type> <fn>(<type> ...) ..."
    "    }"
    "    // other public static classes with public static methods"
    "}")

   (xdoc::p
    "This Java class has a public static method @('initialize')
     to initialize the relevant portions of the ACL2 environment.
     This public method must be called just once,
     before calling the other public methods described below.
     This @('initialize') method should be also called
     before calling any of the public methods provided by AIJ,
     because AIJ itself relies on this initialization to work properly.
     This method is actually empty,
     but calling it ensures that the class is initialized:
     it is the class's static initializer
     that performs the actual initialization.")

   (xdoc::p
    "In the deep embedding approach,
     the Java class also has a public static method @('call')
     to call an ACL2 function on some ACL2 values.
     The method takes as arguments
     the name of the ACL2 function to call
     and an array of ACL2 values,
     and returns an ACL2 value.
     The called ACL2 function must be among @('fn1'), ..., @('fnp')
     and the functions that they transitively call,
     or it may be natively implemented in AIJ.")

   (xdoc::p
    "In the shallow embedding approach,
     the Java class contains public static methods
     for the functions among @('fn1'), ..., @('fnp'),
     the functions that they transitively call
     (except for the functions in
     @(tsee *atj-jprim-fns*) and @(tsee *atj-jprimarr-fns*),
     when @(':deep') is @('nil') and @(':guards') is @('t'))
     and the ACL2 functions natively implemented in AIJ
     (the latter are just wrappers of the native implementations).
     Each method has the same number of parameters as the ACL2 function.
     If @(':guards') is @('nil'),
     there is exactly one method for each ACL2 function;
     that method's arguments all have types @('Acl2Value'),
     while the return type is
     either @('Acl2Value') if the function returns a single result
     or @('MV_Acl2Value_..._Acl2Value') if the function returns "
    (xdoc::seetopic "mv" "multiple results")
    " where @('_Acl2Value') is repeated for the number of results.
     If @(':guards') is @('t'),
     for each ACL2 function there are as many overloaded methods
     as the number of function types associated to the function
     via @(tsee atj-main-function-type)
     and @(tsee atj-other-function-type):
     each of these function types determines the argument and return types
     of the corresponding overloaded method,
     with each argument having the corresponding function input type
     and the return type being
     either the single output type if the function returns a single result
     or @('MV_<type1>_..._<typen>') if the function returns "
    (xdoc::seetopic "mv" "multiple results")
    " where each @('<typei>') is determined from
     the corresponding function output type.
     These methods are declared in nested public classes,
     one class for each ACL2 package:
     each function's method is in the corresponding package's class.
     The mapping between these Java class and method names
     and the corresponding ACL2 package and function names
     is displayed if @(':verbose') is @('t').")

   (xdoc::p
    "ATJ also generated a Java file that contains
     a single package-private class whose name is
     the name of the main class (described above) followed by @('Environment').
     This additional Java class contains code
     to initialize the ACL2 environment:
     this code is executed by invoking
     the @('initialize()') method of the main class described above.")

   (xdoc::h4 "Optional Test Class")

   (xdoc::p
    "If the @(':tests') input (see above) is not @('nil'),
     ATJ also generates an additional Java file that contains
     a single public class named as specified in
     the description of the @(':java-class') input above,
     in the package specified by the @(':java-package') input.")

   (xdoc::codeblock
    "public class <name>Tests {"
    "   ..."
    "    public static void main(String[] args) ..."
    "}")

   (xdoc::p
    "This Java class includes code
     for each test @('(namej termj)')
     specified via the @(':tests') input (see above).
     The code for each test prints @('namej'),
     evaluates the call @('(fn qc1 1c2 ...)') (which @('termj') translates to)
     in AIJ (via the @('call') public method described above),
     compares the resulting value with the one that ACL2 returns
     (which is calculated when ATJ is run),
     and prints a success or failure message
     depending on whether the comparison succeeds or fails.")

   (xdoc::p
    "This Java class has a public static @('main') method that
     calls the @('initialize') public method described above
     and then executes the code to run the tests described just above.
     Thus, this test class can be invoked as a Java application.
     This @('main') method also prints a final message saying whether
     all the tests passed or there were any failures.
     If all the tests passed, the method exits the JVM with return code 0;
     otherwise, it exits the JVM with return code 1,
     which is an error code when the test class
     is invoked as a Java application in a shell script.")

   (xdoc::h4 "Java Version")

   (xdoc::p
    "ATJ generates Java 8 code.
     This means that the code can be compiled
     using a compiler for Java 8 or later.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Compiling and Running the Java Code")

   (xdoc::p
    "The generated Java code can be compiled and run as any other Java code.
     The @('.jar') file for "
    (xdoc::seetopic "aij" "AIJ")
    " must be in the classpath:
     this file is at
     @('[books]/kestrel/java/aij/java/out/artifacts/AIJ_jar/AIJ.jar').
     The files @('compile.sh') and @('run.sh')
     under @('[books]/kestrel/java/atj/tests/')
     contains examples of command to compile and run the code.
     See "
    (xdoc::seetopic "aij" "the AIJ documentation")
    " for instructions on how to generate the @('.jar') file.")

   (xdoc::p
    "When the @(':deep') input is @('t'),
     (the Java representations of) the ACL2 functions
     are evaluated via AIJ's recursive interpreter:
     evaluating recursive ACL2 functions on sufficiently large inputs
     may cause a stack overflow error in Java.
     When the @(':deep') input is @('nil'),
     recursive ACL2 functions are translated to recursive Java methods,
     except for tail-recursive functions, which are translated to loops:
     calling these recursive methods on sufficiently large inputs
     may cause a stack overflow error in Java.
     These stack overflow issues may be mitigated
     by passing a larger stack size to the Java Virtual Machine
     (via the @('-Xss') option to the @('java') command;
     see the comments in the file @('[books]/kestrel/atj/tests/run.sh')),
     or, when @(':deep') is @('nil'),
     by making all the recursive ACL2 functions tail-recursive
     (e.g. via "
    (xdoc::seetopic "apt::tailrec" "APT's tail recursion transformation")
    ") prior to generating Java code.")))
