; Java -- ATJ -- Documentation
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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

   (xdoc::h3 "Introduction")

   (xdoc::p
    "ATJ translates ACL2 to Java,
     enabling ACL2 code to be used in Java code
     (in the sense explained below).")

   (xdoc::p
    "For instance, ATJ is useful
     to generate Java code at the end of
     an <see topic='@(url apt::apt)'>APT</see> program synthesis derivation.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Scope")

   (xdoc::p
    "ATJ translates ACL2 named functions to corresponding Java code
     whose execution mimics the execution of the ACL2 functions.")

   (xdoc::p
    "The ACL2 functions accepted by ATJ may manipulate any ACL2 value:
     @(see acl2::characters),
     @(see acl2::strings),
     @(see acl2::symbols),
     @(see acl2::numbers), and
     @(see acl2::conses).
     The Java code that corresponds to the ACL2 functions
     manipulates Java representations of the ACL2 values.")

   (xdoc::p
    "ATJ accepts all the ACL2 functions that
     (1) have an @('unnormalized-body') property (see @(tsee body)) and
     (2) either do not have raw Lisp code
     or have raw Lisp code but belong to a whitelist.
     The ACL2 functions with raw Lisp code
     are the ones listed in the global variables
     @('program-fns-with-raw-code') and @('logic-fns-with-raw-code').
     The aforementioned whitelist consists of functions
     whose @('unnormalized-body') property is
     functionally equivalent to the raw Lisp code.
     The Java code that corresponds to the ACL2 functions
     that satisfy conditions (1) and (2) above,
     mimics the computations described by their @('unnormalized-body').")

   (xdoc::p
    "ATJ also accepts the ACL2 function @(tsee return-last)
     (which has raw Lisp code),
     but only when it is called on @('mbe-raw1') as the first argument.
     Calls of the form @('(return-last 'mbe1-raw ...)')
     are translated representations of calls of @(tsee mbe).
     Thus, in reference to the whitelist described in the previous paragraph,
     @(tsee return-last) is ``partially'' whitelisted.")

   (xdoc::p
    "ATJ also accepts all the @(see acl2::primitive) ACL2 functions.
     The Java code that corresponds to these ACL2 functions
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
     Support for translating ACL2 functions with side effects
     to Java code that mimics those side effects
     may be added in the future.")

   (xdoc::p
    "ATJ does not accept functions that access @(see acl2::stobj)s.
     Support for stobjs, and destructive updates of stobjs,
     may be added in the future.")

   (xdoc::p
    "ATJ does not translate
     <see topic='@(url defmacro)'>macro definitions</see> to Java code.
     However, the use of macros in function bodies is fully supported,
     because ATJ operates on ACL2 translated terms,
     where macros are expanded.")

   (xdoc::p
    "ATJ does not translate
     <see topic='@(url defconst)'>constant definitions</see> to Java code.
     However, the use of named constants in function bodies is fully supported,
     because ATJ operates on ACL2 translated terms,
     where constants are expanded.")

   (xdoc::p
    "The Java counterparts of the translated ACL2 functions
     mimic execution ``in the logic'',
     without <see topic='@(url acl2::guard-checking)'>checking guards</see>.
     In particular,
     only the @(':logic') part of calls of @(tsee mbe) is executed:
     the @(':exec') part is completely ignored.
     Support for guards and more efficient execution
     (including the execution of the @(':exec') part of calls of @(tsee mbe))
     may be added in the future.")

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
     like @(tsee state) or user-defined @(see acl2::stobj)s
     is therefore not supported;
     in particular, the generated Java code has no access to
     the ACL2/Lisp environment.
     Support for global variables, in particular @(tsee state),
     may be added in the future.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Approach")

   (xdoc::p
    "ATJ is supported by <see topic='@(url aij)'>AIJ</see>,
     which is a deep embedding in Java
     of the executable subset of ACL2
     (subject to the limitations outlined above).")

   (xdoc::p
    "ATJ translates the target ACL2 functions
     into deeply embedded Java representations,
     based on their @('unnormalized-body') properties.
     It does so recursively,
     starting from the top-level functions specified by the user
     and stopping at the primitive functions,
     which have no @('unnormalized-body') property.
     If a function is encountered that
     is not among the primitives
     and has no @('unnormalized-body') property,
     ATJ stops with an error.
     If a function is encountered that has raw Lisp code
     and is not in the whitelist,
     ATJ stops with an error.")

   (xdoc::p
    "ATJ generates a Java file
     with a public class with two public methods,
     in a user-defined Java package (distinct from AIJ's package).
     One public method builds
     (1) the deeply embedded ACL2 functions,
     making them available for execution via interpretation, and
     (2) a representation of
     some other portions of the ACL2 environment needed for execution,
     such as the ACL2 packages with their import lists.
     The other public method serves
     to call deeply embedded ACL2 functions on ACL2 values.
     AIJ's Java package provides public classes and methods
     to translate certain Java values to ACL2 values and vice versa.
     Thus, by loading into the Java Virtual Machine
     the AIJ's package
     and the generated Java code,
     external Java code can ``use'' ACL2 code.")

   (xdoc::p
    "The first public method described above
     (the one that builds the ACL2 environment)
     must be called
     before calling the second public method described above
     (the one that evaluates ACL2 function calls),
     and also before calling any of AIJ's public methods
     to translate between Java and ACL2 values.")

   (xdoc::p
    "This translation approach is simple and thus fairly high-assurance.
     On the other hand, the Java code is not efficient or idiomatic.
     However, the approach may work well for some simple applications,
     and provides a good starting point for optimization.
     In the future, we may translate ACL2 functions to
     shallowly embedded Java representations,
     avoiding interpretation altogether.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(atj fn1 ... fnp"
    "     &key"
    "     :java-package  ; default nil"
    "     :java-class    ; default nil"
    "     :output-dir    ; default nil"
    "     :tests         ; default nil"
    "     :verbose       ; default nil"
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('fn1'), ..., @('fnp')"
    (xdoc::p
     "Names of the target ACL2 functions to be translated to Java.")
    (xdoc::p
     "Each @('fni') must be the name of a function that
      either has an @('unnormalized-body') property
      and no raw Lisp code (unless it is in the whitelist),
      or is a @(see acl2::primitive) function.
      Each of these functions must have
      no input or output <see topic='@(url acl2::stobj)'>stobjs</see>.
      Each of these functions must transitively call
      (in the unnormalized body, if non-primitive)
      only functions that satisfy the same constraints.")
    (xdoc::p
     "None of the @('fni') functions may be @(tsee return-last).
      However, the @('fni') functions may transitively call @(tsee return-last),
      provided that the first argument of all of these calls is @('mbe-raw1'),
      i.e. that these calls result from the translation of @(tsee mbe)s.
      No restrictions are enforced on the @(':exec') parts of thses calls;
      only the @(':logic') parts are recursively checked
      to satisfy all the constraints stated here.")
    (xdoc::p
     "There must be at least one function, i.e. @('p') &gt; 0 must hold.
      All the @('fni') names must be distinct."))

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
      is in an unnamed package."))

   (xdoc::desc
    "@(':java-class') &mdash; default @('nil')"
    (xdoc::p
     "Name of the generated Java class.")
    (xdoc::p
     "It must be either an ACL2 string or @('nil').
      If it is an ACL2 string,
      it must be a valid Java class name consisting of only ASCII characters.
      If this input is @('nil'), the generated Java class is called @('ACL2').")
    (xdoc::p
     "If the @(':tests') input (see below) is not @('nil'),
      an additional Java class for testing is generated,
      whose name is obtained by appending @('Test')
      at the end of the name of the main class."))

   (xdoc::desc
    "@(':output-dir') &mdash; default @('\".\"')"
    (xdoc::p
     "Path of the directory where
      the generated Java file/files is/are created.")
    (xdoc::p
     "It must be an ACL2 string that is
      a valid path to a directory in the file system;
      the path may be absolute,
      or relative to
      the <see topic='@(url cbd)'>current working directory</see>).")
    (xdoc::p
     "The name of the generated file containing the main class
      is the name of that class followed by @('.java').
      If the file already exists, it is overwritten.")
    (xdoc::p
     "If the @(':tests') input (see below) is not @('nil'),
      the name of the generated file containing the test class
      is the name of that class followed by @('.java').
      If the file already exists, it is overwritten."))

   (xdoc::desc
    "@(':tests') &mdash; default @('nil')"
    (xdoc::p
     "Optional tests to generate Java code for.")
    (xdoc::p
     "It must evaluate to a list of doublets
      @('((name1 term1) ... (nameq termq))'),
      where each @('namej') is a string consisting of only letters and digits,
      and each @('termj') is an untranslated ground term
      whose translation is @('(fn qc1 qc2 ...)'),
      where @('fn') is among the target functions @('fn1'), ..., @('fnp'),
      and each @('qc1'), @('qc2'), etc. is a quoted constant.
      All the @('namej') must be distinct.")
    (xdoc::p
     "Each doublet @('(namej termj)') specifies a test,
      in which the result of @('(fn qc1 qc2 ...)') calculated by ACL2
      is compared with the result of the same call
      calculated via the generated Java code for @('fn').
      These tests can be run via additional generated Java code
      (see below).")
    (xdoc::p
     "Note that the @(':tests') input is evaluated."))

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
    "public class <name> {"
    "    // private static field and methods"
    "    public static void initialize() ..."
    "    public static Acl2Value"
    "        call(Acl2Symbol function, Acl2Value[] arguments) ..."
    "}")

   (xdoc::p
    "This Java class has private static methods
     that build the relevant portions of the ACL2 environment,
     including the definitions of the functions @('fn1'), ..., @('fnp')
     and of all the functions that they transitively call,
     except for the primitive functions.
     It also has a private static field that records whether
     the ACL2 environment is initialized or not.")

   (xdoc::p
    "This Java class has a public static method @('initialize')
     to initialize the relevant portions of the ACL2 environment,
     via the private methods mentioned just above.
     This public method must be called just once,
     before calling the public method @('call') described below;
     this usage is enforced via the private field mentioned just above.
     This @('initialize') method should be also called
     before calling any of the public methods provided by AIJ.")

   (xdoc::p
    "This Java class has a public static method @('call')
     to call an ACL2 function on some ACL2 values.
     The method takes as arguments
     the name of the ACL2 function to call
     and an array of ACL2 values,
     and returns an ACL2 value.
     The called ACL2 function must be among @('fn1'), ..., @('fnp')
     and the functions that they transitively call,
     or it may be any of the primitive ACL2 functions.")

   (xdoc::h4 "Optional Test Class")

   (xdoc::p
    "If the @(':tests') input (see above) is not @('nil'),
     ATJ also generates an additional Java file that contains
     a single public class named as specified in
     the description of the @(':java-class') input above,
     in the package specified by the @(':java-package') input.")

   (xdoc::codeblock
    "public class <name>Test {"
    "    // private static methods"
    "    public static void main(String[] args) ..."
    "}")

   (xdoc::p
    "This Java class has a private static method
     for each test @('(namej termj)')
     specified via the @(':tests') input (see above).
     Each such method prints @('namej'),
     evaluates the call @('(fn qc1 1c2 ...)') (which @('termj') translates to)
     in AIJ (via the @('call') public method described above),
     compares the resulting value with the one that ACL2 returns
     (this is calculated when ATJ is run),
     and prints a success or failure message
     depending on whether the comparison succeeds or fails.")

   (xdoc::p
    "This Java class has a public static @('main') method that
     calls the @('initialize') public method described above
     and then calls all the testing methods described just above.
     Thus, this test class can be invoked as a Java application.")))
