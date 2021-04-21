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

(include-book "kestrel/std/util/deftutorial" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftutorial atc-tutorial "ATC tutorial")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-top

  (atc)

  (atc-tutorial-section "Scope of the Tutorial")

  (xdoc::p
   "This tutorial is work in progress,
    but it may be already useful in its current incomplete form.
    This tutorial's goal is to provide user-level pedagogical information
    on how ATC works and how to use ATC effectively.
    See "
   (xdoc::seetopic "atc" "the ATC manual page")
   " for the ATC reference documentation.")

  (xdoc::p
   "In this tutorial,
    we refer to the official C standard in the manner explained in "
   (xdoc::seetopic "c" "the top-level XDOC topic of our C library")
   ".")

  (atc-tutorial-section "Structure of the Tutorial")

  (xdoc::p
   "This tutorial consists of this top-level page
    plus a number of hyperlinked pages,
    all of which are subtopics of this top-level page,
    listed below alphabetically for easy reference.
    Starting from this top-level page,
    we provide <i>Start</i> and <i>Next</i> links
    to navigate sequentially through all the tutorial pages;
    we also provide <i>Previous</i> links going the opposite direction.
    It is recommended to follow this order
    when reading this tutorial for the first time.")

  (xdoc::p
   "Some pages may be skipped at first reading,
    because they contain additional information
    that may not be necessary for a user to know in order to start using ATC;
    such pages include explicit text indicating that.
    However, it is recommended to read all the pages, eventually."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page motivation

  "Motivation for Generating C Code from ACL2"

  (xdoc::p
   "(This page may be skipped at first reading.)")

  (xdoc::p
   "The motivation for generating C code from ACL2 is analogous to
    the motivation for generating Java code from ACL2,
    or for generating code in other programming language from ACL2.
    The @(see java::atj-tutorial-motivation) page
    provides the general motivation,
    in the context of Java:
    it is recommended to read that page.")

  (xdoc::p
   "In addition, as a specific motivation for generating C code,
    it should be noted that C is widely used in certain domains,
    such as embedded systems.
    Some of these C applications are relatively small in size
    and have strong safety and security requirements,
    making them an attractive target for (ACL2-based) formal methods."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page atj-comparison

  "Comparison with ATJ's Java code generation from ACL2"

  (xdoc::p
   "(This page may be skipped at first reading.)")

  (xdoc::p
   "ATC is related to "
   (xdoc::seetopic "java::atj" "ATJ")
   ", the Java code generator for ACL2.
    Aside from the obvious difference in target languages,
    ATJ and ATC currently differ in their primary goals and emphases.")

  (xdoc::p
   "ATJ was built to recognize, and translate to reasonable Java,
    essentially any ACL2 code
    (provided that it has side effects known to ATJ).
    ATJ also provides ways to exert finer-grained control
    on the generated Java,
    by using certain ACL2 types and operations
    that represent Java types and operations
    and that are translated to the corresponding Java constructs.
    While there are plans to have ATJ generate ACL2 proofs
    of the correctness of the generated code,
    ATJ currently does not generate proofs.")

  (xdoc::p
   "In contrast, ATC is being built to recognize, and translate to C,
    only certain ACL2 types and operations
    that represent C types and operations
    and that are translated to the corresponding Java constructs.
    ATC does not attempt to translate arbitrary ACL2 to C.
    From the outset, ATC also generates ACL2 proofs
    of the correctness of the generated C code.")

  (xdoc::p
   "The fact that ATC is much simpler than ATJ
    facilitates the generation of proofs.
    Generating proofs for ATJ is a larger task,
    due to the greater complexity.")

  (xdoc::p
   "In the future, ATC may be extended towards
    recognizing any ACL2 code and translating it to reasonable C,
    analogously to ATJ;
    but the plan is for ATC to always generate proofs.
    Conversely, ATJ may be extended to generate proofs as well.
    Thus, while eventually ATJ and ATC may provide similar features,
    their starting points and tradeoffs are different,
    and that will keep the two tools different for some time to come."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page approach

  "Approach to Generating C Code from ACL2"

  (xdoc::p
   "ATC translates a subset of ACL2 to C.
    The ACL2 subset is designed to be close to C,
    i.e. to be essentially ``C written in ACL2'',
    so that it is relatively easy to translate to C.
    There is a direct translation to the C constructs
    from their representation in ACL2.")

  (xdoc::p
   "ATC is meant to be used in conjunction with "
   (xdoc::seetopic "apt::apt" "APT")
   ". One uses APT transformations
    to refine ACL2 specifications and code
    to the subset recognized by ATC, which ATC translates to C.
    Thus, ATC can be used at the end of an APT derivation.")

  (xdoc::p
   "Currently ATC recognizes a very limited subset of ACL2
    and translates it to a very limited subset of C.
    This is just a first step (the development of ATC has just started);
    we plan to extend ATC to increasingly larger subsets of ACL2 and C."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page proofs

  "ACL2 Proofs Generated for the Generated C code"

  (xdoc::p
   "(This page may be skipped at first reading.)")

  (xdoc::p
   "Besides generating C code,
    ATC also generates ACL2 proofs of
    the correctness of the generated C code
    with respect to the ACL2 code from which the C code is generated.
    More precisely, ATC generates ACL2 theorems
    that assert these correctness properties.")

  (xdoc::p
   "The correctness properties proved by ATC are the following:")
  (xdoc::ul
   (xdoc::li
    "The generated C code satisfies
     the compile-time constraints prescribed by [C].
     In other words, the C code is compiled by a compliant compiler.
     This is expressed via a "
    (xdoc::seetopic "atc-static-semantics"
                    "formal static semantics of C")
    " that we are developing.")
   (xdoc::li
    "The generated C code is functionally equivalent
     to the ACL2 code that represents it.
     In other words, it computes the same things as the ACL2 code.
     This is expressed via a "
    (xdoc::seetopic "atc-dynamic-semantics"
                    "formal dynamic semantics of C")
    " that we are developing.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page int-representation

  "ACL2 representation of the C @('int') type and operations"

  (xdoc::p
   "As stated in @(see atc-tutorial-approach),
    ATC recognizes, and translates to C,
    a subset of ACL2 that represents C code fairly directly.
    In other words, there are representations of C constructs in ACL2,
    which the ATC user must know so that they can invoke ATC
    on ACL2 code of the appropriate form.
    This tutorial page describes how the C @('int') types and operations
    are represented in ACL2;
    examples of their use, and of C code generated from them,
    are given in other pages.")

  (atc-tutorial-section "C @('int') Type and Operations")

  (xdoc::p
   "According to [C:6.2.5/5] and [C:5.2.4.2.1/1],
    the ``plain'' @('int') type consists of
    signed integers in a range from -32767 or less to +32767 or more
    (both numbers are inclusive).
    The exact range depends on the C implementation, as detailed below.")

  (xdoc::p
   "The (C, not ACL2) representation of @('int') values in memory,
    which may be visible to the C code via access as @('unsigned char[]')
    (as allowed by the [C]),
    consists of a sign bit, some value bits, and optionally some padding bits
    [C:6.2.6.2/2].
    The signed representation may be
    two's complement, one's complement, or sign and magnitude
    [C:6.2.6.2/2].
    All these choices are implementation-dependent,
    and determine the range of @('int') values,
    subject to the minimum range requirement stated above.")

  (xdoc::p
   "Two's complement representations without padding bits seem the most common,
    along with 8-bit bytes
    (the exact number of bits in a byte is also implementation-dependent
    [C:5.2.4.2.1/1] [C:6.2.6.1/3]).
    Under these assumptions, @('int') values must consist of at least 16 bits,
    resulting in at least the range from -32768 to +32767.
    [C:6.2.6.1/4] requires @('int') to take a whole number of bytes,
    and thus the possible bit sizes are 16, 24, 32, 40, 48, etc.
    [C:6.2.5/5] states that the size is
    the natural one suggested by the architecture of the execution environment.
    For modern Macs and PCs, experiments suggest this to be 32 bits
    (the experiment consists in printing @('sizeof(int)') in a C program),
    even though one might expect it to be 64 bits instead,
    given that these are 64-bit machines with 64-bit operating systems.
    (However, the C @('long') type appears to be 64 bits on these platforms.)")

  (xdoc::p
   "C provides a variety of @('int') operations,
    i.e. operations that operate on @('int') values.
    These operations also apply to other arithmetic types,
    but operands are subjected to promotions and conversions
    that reduce the possible combinations of operand types for each operation.
    For instance, the addition operation @('+') does not directly add
    @('short') or @('unsigned char') operands:
    these are promoted to @('int') values before adding them up,
    according to the integer promotions described in [C:6.3.1.1/2].
    Similarly, the addition operation @('+') does not directly add
    an @('int') operand and a @('long') operand:
    the first operand is converted to @('long') first,
    so that addition is performed on two @('long') values,
    according to the usual arithmetic conversions
    described in [C:6.3.1.8].")

  (xdoc::p
   "This means that there are only certain ``interesting'' instances
    of operations like @('+'),
    i.e. one for @('int') operands, one for @('long') operands etc.
    The instances for @('short') or @('unsigned char') operands,
    as well the instance for
    an @('int') first operand and a @('long') second operand,
    are less interesting because they can be viewed as
    combinations of conversions with the interesting instances.
    Thus, in the context of this tutorial page,
    we are interested in the instances of the C operations
    that apply to @('int') operands:
    this is what we mean by `@('int') operations'.")

  (xdoc::p
   "C provides the following unary and binary @('int') operations [C:6.5]:")
  (xdoc::ul
   (xdoc::li "@('+') (unary) &mdash; no value change, but mirrors unary @('-')")
   (xdoc::li "@('-') (unary) &mdash; arithmetic negation")
   (xdoc::li "@('~') (unary) &mdash; bitwise complement")
   (xdoc::li "@('!') (unary) &mdash; logical negation/complement")
   (xdoc::li "@('+') (binary) &mdash; addition")
   (xdoc::li "@('-') (binary) &mdash; subtraction")
   (xdoc::li "@('*') (binary) &mdash; multiplication")
   (xdoc::li "@('/') (binary) &mdash; division")
   (xdoc::li "@('%') (binary) &mdash; remainder")
   (xdoc::li "@('<<') (binary) &mdash; left shift")
   (xdoc::li "@('>>') (binary) &mdash; right shift")
   (xdoc::li "@('<') (binary) &mdash; less-than")
   (xdoc::li "@('>') (binary) &mdash; greater-than")
   (xdoc::li "@('<=') (binary) &mdash; less-than-or-equal-to")
   (xdoc::li "@('>=') (binary) &mdash; greater-than-or-equal-to")
   (xdoc::li "@('==') (binary) &mdash; equality")
   (xdoc::li "@('!=') (binary) &mdash; non-equality")
   (xdoc::li "@('&') (binary) &mdash; bitwise conjunction")
   (xdoc::li "@('^') (binary) &mdash; bitwise exclusive disjunction")
   (xdoc::li "@('|') (binary) &mdash; bitwise inclusive disjunction")
   (xdoc::li "@('&&') (binary) &mdash; logical (short-circuit) conjunction")
   (xdoc::li "@('||') (binary) &mdash; logical (short-circuit) disjunction")
   (xdoc::li "@('=') (binary) &mdash; simple assignment")
   (xdoc::li "@('+=') (binary) &mdash; compound assignment with @('+')")
   (xdoc::li "@('-=') (binary) &mdash; compound assignment with @('-')")
   (xdoc::li "@('*=') (binary) &mdash; compound assignment with @('*')")
   (xdoc::li "@('/=') (binary) &mdash; compound assignment with @('/')")
   (xdoc::li "@('%=') (binary) &mdash; compound assignment with @('%')")
   (xdoc::li "@('<<=') (binary) &mdash; compound assignment with @('<<')")
   (xdoc::li "@('>>=') (binary) &mdash; compound assignment with @('>>')")
   (xdoc::li "@('&=') (binary) &mdash; compound assignment with @('&')")
   (xdoc::li "@('^=') (binary) &mdash; compound assignment with @('^')")
   (xdoc::li "@('|=') (binary) &mdash; compound assignment with @('|')"))
  (xdoc::p
   "These not only take, but also return, @('int') values.
    This uniformity is also due to the fact that C represents booleans
    as the @('int') values 0 (for false) and 1 (for true),
    and thus the relational and equality operations,
    as well as the logical conjunction and disjunction operations,
    all return @('int') results [C:6.5.13] [C:6.5.14].
    Note also that the left and right shift operations, in general,
    may apply to operands of different types (unlike other binary operations)
    [C:6.5.7];
    however, here we are interested in the instances of those operations
    where both operands are @('int') values.")

  (xdoc::p
   "Some of the above operations yield well-defined results,
    specified by [C], only under certain conditions.
    For instance, the addition operation @('+') on @('int') operands
    is well-defined only if the exact result is representable as an @('int')
    [C:6.5/5].
    An implementation may actually add definedness to this operation,
    by relying on the (well-defined) behavior of the underlying hardware,
    e.g. by keeping the low bits of the exact result that fit @('int')
    (which is the same result prescribed by the Java language specification).")

  (xdoc::p
   "The @('&&') and @('||') operations
    are non-strict at the expression level:
    their second operand expression is not executed
    if the result of the first operand expression
    suffices to determine the final result
    (0 for conjunction, 1 for disjunction).")

  (xdoc::p
   "The simple and compound assignment operations have side effects.
    All the other operations are pure, i.e. without side effect.")

  (atc-tutorial-section "ACL2 Representation")

  (xdoc::p
   "The ACL2 representation of the C @('int') type and operations
    is in the files @('[books]/kestrel/c/atc/integers.lisp')
    and @('[books]/kestrel/c/atc/integer-operations.lisp').
    These are automatically included when ATC is included,
    but one may want to include those file as part of an APT derivation
    that refines some specification to the ACL2 subset handled by ATC
    (see @(see atc-tutorial-approach)),
    and thus before including ATC itself,
    which is only needed to generate code at the end of the derivation.")

  (xdoc::p
   "In line with typical C implementations on Macs and PCs mentioned above,
    our ACL2 representation of @('int') values
    consists of signed two's complement 32-bit integers.
    More precisely, we provide a fixtype @(tsee sint) (for @('signed int')),
    with associated predicate @(tsee sintp) and fixer @(tsee sint-fix).
    This fixtype wraps
    ACL2 integers in the range from @($-2^{31}$) to @($2^{31}-1$).
    The wrapping provides more abstraction:
    (the ACL2 representation of) C @('int') values must be manipulated
    only via the provided ACL2 functions (see below)
    in the ACL2 code that ATC translates to C.")

  (xdoc::p
   "We plan to generalize our ACL2 representation of C @('int') values
    to allow different sizes than 4 (8-bit) bytes.
    This will be achieved via a static parameterization,
    i.e. via (something like) a constrained nullary function
    that specifies the size of @('int').
    We may also further generalize the representation,
    again via a static parameterization,
    to cover more of the options allowed by [C].")

  (xdoc::p
   "We also provide ACL2 functions
    corresponding to some of the operations listed above:")
  (xdoc::ul
   (xdoc::li "@(tsee plus-sint) &mdash; for unary @('+')")
   (xdoc::li "@(tsee minus-sint) &mdash; for unary @('-')")
   (xdoc::li "@(tsee bitnot-sint) &mdash; for @('~')")
   (xdoc::li "@(tsee lognot-sint) &mdash; for @('!')")
   (xdoc::li "@(tsee add-sint-sint) &mdash; for binary @('+')")
   (xdoc::li "@(tsee sub-sint-sint) &mdash; for binary @('-')")
   (xdoc::li "@(tsee mul-sint-sint) &mdash; for @('*')")
   (xdoc::li "@(tsee div-sint-sint) &mdash; for @('/')")
   (xdoc::li "@(tsee rem-sint-sint) &mdash; for @('%')")
   (xdoc::li "@(tsee shl-sint-sint) &mdash; for @('<<')")
   (xdoc::li "@(tsee shr-sint-sint) &mdash; for @('>>')")
   (xdoc::li "@(tsee lt-sint-sint) &mdash; for @('<')")
   (xdoc::li "@(tsee gt-sint-sint) &mdash; for @('>')")
   (xdoc::li "@(tsee le-sint-sint) &mdash; for @('<=')")
   (xdoc::li "@(tsee ge-sint-sint) &mdash; for @('>=')")
   (xdoc::li "@(tsee eq-sint-sint) &mdash; for @('==')")
   (xdoc::li "@(tsee ne-sint-sint) &mdash; for @('!=')")
   (xdoc::li "@(tsee bitand-sint-sint) &mdash; for @('&')")
   (xdoc::li "@(tsee bitxor-sint-sint) &mdash; for @('^')")
   (xdoc::li "@(tsee bitior-sint-sint) &mdash; for @('|')"))
  (xdoc::p
   "These are all the strict pure operations;
    the non-strict or non-pure operations are excluded,
    because they are represented differently in ACL2,
    as described elsewhere in this tutorial.")

  (xdoc::p
   "These ACL2 functions take @(tsee sint) values as inputs,
    as required by their guards.
    They also return @(tsee sint) values as outputs,
    as proved by their return type theorems.")

  (xdoc::p
   "Some of these functions have additional guard conditions
    that capture the conditions under which
    the result is well-defined according to the [C].
    For instance, the guard of @(tsee add-sint-sint) includes the condition that
    the exact integer result fits in the range of the ACL2 integers
    that are wrapped to form @(tsee sint) values.
    More precisely, these additional guard conditions
    are captured by the following predicates,
    whose association to the above functions should be obvious from the names:")
  (xdoc::ul
   (xdoc::li "@(tsee minus-sint-okp)")
   (xdoc::li "@(tsee add-sint-sint-okp)")
   (xdoc::li "@(tsee sub-sint-sint-okp)")
   (xdoc::li "@(tsee mul-sint-sint-okp)")
   (xdoc::li "@(tsee div-sint-sint-okp)")
   (xdoc::li "@(tsee rem-sint-sint-okp)")
   (xdoc::li "@(tsee shl-sint-sint-okp)")
   (xdoc::li "@(tsee shr-sint-sint-okp)"))
  (xdoc::p
   "We remark that the predicates for @('/') and @('%') include
    the condition that the divisor is not 0.")

  (xdoc::p
   "Besides unary and binary @('int') operations,
    C includes @('int') constants [C:6.4.4.1]
    (more precisely, integer constants, some of which have type @('int')),
    which may be regarded as (a large number nullary) of @('int') operations.
    Our ACL2 representation in @('[books]/kestrel/c/atc/integers.lisp')
    provides a function @(tsee sint-const),
    whose calls on suitable ACL2 quoted integer constants
    represent @('int') constants.
    The quoted integer constant arguments must be
    a natural number in the range of signed two's complement 32-bit integers:
    this is enforced by the guard of @(tsee sint-const).
    Note that C integer constants are always non-negative.")

  (xdoc::p
   "See the documentation of the fixtype and functions mentioned above
    for more details.")

  (xdoc::p
   "In the future, we may generalize our representation of these operations
    to allow for implementation-defined behaviors,
    via suitable static parameterizations."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page int-programs

  "ACL2 representation and generation of C @('int') programs"

  (xdoc::p
   "After describing
    our ACL2 representation of the C @('int') type and operations
    in @(see atc-tutorial-int-representation),
    now we describe how that is used to represent and generate
    C @('int') programs, i.e. programs that manipulate @('int') values.")

  (xdoc::p
   "We do that via a simple example,
    but present concepts that apply more generally.
    However, this page only describes the basics of
    representing and generating C @('int') programs:
    more advanced features are presented in subsequent tutorial pages.")

  (atc-tutorial-section "Simple Example")

  (xdoc::p
   "Our simple example is a C program consisting of a single function:")
  (xdoc::codeblock
   "int f(int x, int y, int z) {"
   "    return (x + y) * (z - 3);"
   "}")

  (xdoc::p
   "This function takes three @('int') values
    and returns an @('int') value resulting from
    their combination via @('int') operations.
    The function also involves the use of an @('int') constant.")

  (atc-tutorial-section "Function Correspondence")

  (xdoc::p
   "There is a one-to-one representational correspondence
    between C and ACL2 functions.
    That is, every C function is represented by an ACL2 function,
    whose name must be supplied to ATC in order to generate
    the corresponding C function definition
    (the exact call of ATC is described later in this page).")

  (xdoc::p
   "Thus, for the example program above,
    we need an ACL2 function to represent @('f').
    This generalizes to C programs with multiple functions.")

  (atc-tutorial-section "Function and Parameter Names")

  (xdoc::p
   "The names of the function and its parameters
    are represented by ACL2 symbols
    whose names are identical to the C identifiers:")
  (xdoc::codeblock
   "(defun |f| (|x| |y| |z|)"
   "  ...)")

  (xdoc::p
   "Note that we need the double bar notation because
    the names are lowercase, consistently with the C convention.
    If we omitted the double bars,
    we would be representing a different C function:")
  (xdoc::codeblock
   "int F(int X, int Y, int Z) {"
   "    ..."
   "}")
  (xdoc::p
   "This is because, without the vertical bars,
    the names of the symbols are uppercase.
    This is a valid C function,
    but does not follow the normal C naming conventions.")

  (xdoc::p
   "Package names are ignored for this purpose,
    e.g. both @('acl2::|f|') and @('c::|f|') represent
    the C identifier @('f').")

  (xdoc::p
   "In the envisioned use of ATC,
    the user would write ACL2 functions with more conventional ACL2 names
    for both functions and parameters
    (i.e. without vertical bars).
    The user would then use APT transformations to turn those names
    into the form required to represent C names for ATC's purposes.")

  (xdoc::p
   "More details about the mapping from ACL2 names to C names
    are given in @(see atc-tutorial-identifiers).")

  (atc-tutorial-section "Function Body")

  (xdoc::p
   "Given the representation of C @('int') operations (including constants)
    described in @(see atc-tutorial-int-representation),
    it should be easy to see how the body of the C function @('f') above
    is represented as follows in ACL2:")
  (xdoc::codeblock
   "(defun |f| (|x| |y| |z|)"
   "  (c::mul-sint-sint (c::add-sint-sint |x| |y|)"
   "                    (c::sub-sint-sint |z| (c::sint-const 3))))")
  (xdoc::p
   "We represent the expression of the @('return') statement
    that forms the body of the function @('f').
    In ACL2, terms are implicitly returned,
    so there is no need to represent the @('return') statement explicitly.")

  (xdoc::p
   "The @('c::') package prefixes are generally needed
    when the function is defined in a different ACL2 package from @('\"C\"').
    The package of the symbols @('|f|'), @('|x|'), etc. do not matter,
    in the sense that they do not represent anything in the C code.
    However the functions @(tsee sint-const), @(tsee add-sint-sint), etc.
    must be the ones in the @('\"C\"') package,
    from the file @('[books]/kestrel/c/atc/integers.lisp').")

  (xdoc::p
   "In the envisioned use of ATC,
    the user would not write directly a function body of the form above.
    Instead, they would obtain that kind of function body
    via suitable APT transformations that turn
    (conventional) ACL2 types and operations
    into (ACL2 representations of) C types and operations,
    under suitable preconditions.")

  (atc-tutorial-section "Function Input and Ouput Types")

  (xdoc::p
   "Given the use of @(tsee add-sint-sint) and @(tsee sub-sint-sint)
    on the ACL2 parameters @('|x|'), @('|y|'), and @('|z|'),
    it would not be hard to infer automatically that
    these represent @('int') parameters in C.
    However, the required guard verification described below
    implicitly requires the guard of @('|f|') to express or imply
    that @(tsee sintp) holds on the function parameters.
    For clarity, we require those to be expressed, not merely implied.")

  (xdoc::p
   "That is, the guard must include explicit conjuncts
    that spell out the C types of the function's parameters.
    For the example function, these are as follows:")
  (xdoc::codeblock
   "(defun |f| (|x| |y| |z|)"
   "  (declare (xargs :guard (and (c::sintp |x|)"
   "                              (c::sintp |y|)"
   "                              (c::sintp |z|)"
   "                              ...))) ; more conjuncts, described below"
   "  (c::mul-sint-sint (c::add-sint-sint |x| |y|)"
   "                    (c::sub-sint-sint |z| (c::sint-const 3))))")

  (xdoc::p
   "When generating C code for @('|f|'),
    ATC looks for those conjuncts in the guard.
    These may occur anywhere in the guard,
    not necessarily in order,
    but they must be easily extractable
    by looking at the @(tsee and) tree structure of the guard:
    the conjuncts of interest must be leaves in that tree,
    one for each function parameter.
    For instance, the following would be equally acceptable:")
  (xdoc::codeblock
   "(defun |f| (|x| |y| |z|)"
   "  (declare (xargs :guard (and (and (c::sintp |z|)"
   "                                   (c::sintp |x|))"
   "                              (and ..."
   "                                   (c::sintp |y|))"
   "                              ...)))"
   "  ...) ; body as above")

  (xdoc::p
   "ATC infers the output type of a function
    by performing a C type analysis of the function's body.
    For the function @('|f|') above,
    the output type is obviously @('int'),
    because the body is a call of @(tsee mul-sint-sint),
    which is known to return (the ACL2 representation of) an @('int') value.
    ATC does not require explicit return type theorems for the ACL2 functions
    that are translated to C functions.")

  (atc-tutorial-section "Guard Verification")

  (xdoc::p
   "ATC requires that the ACL2 functions that represent C functions
    are guard-verified (which implies that they must be in logic mode).
    This ensures that the ACL2 functions that represent C operations
    are always applied to values whose result is well-defined
    according to [C].
    It also ensures that @(tsee sint-const) is always applied
    to a natural number representable as an @('int').")

  (xdoc::p
   "However, this generally requires guards to have additional conditions,
    besides the @(tsee sintp) conjunts discussed above.
    It should be clear that a C function like @('f')
    does not yield a well-defined [C] result
    for every possible value of its arguments.
    For instance, sufficiently large values of @('x') and @('y')
    would make the result of @('x + y') not representable as @('int'),
    and thus not well-defined according to [C].")

  (xdoc::p
   "This should not be surprising.
    It is fairly normal for programs to be correct
    only under certain preconditions.
    The example function @('f') above is a simple abstract example,
    but in a practical development there must be natural preconditions
    for the C functions that form the development;
    otherwise, it would be impossible to formally prove correctness.")

  (xdoc::p
   "In a C program, there may be
    functions that receive data from outside the program.
    These functions should not assume any precondition on that data,
    and diligently validate it before operating on it.
    After validation, these C functions may call other C functions,
    internal to the C program, in the sense that
    they only receive data validated by the calling functions.
    The validation provides preconditions
    that may be assumed by the internal functions.")

  (xdoc::p
   "The example function @('f') may be regarded
    as an internal function in the sense above.
    For simplicity, we assume that every parameter of the function
    is faily small, more precisely not above 10 in absolute value.
    The following is the function @('|f|') with the complete guard
    and the hints and book inclusion and command to verify the guards:")
  (xdoc::codeblock
   "(encapsulate ()"
   ""
   "  (local (include-book \"arithmetic-5/top\" :dir :system))"
   ""
   "  (local (set-default-hints '((nonlinearp-default-hint"
   "                               stable-under-simplificationp"
   "                               hist"
   "                               pspv))))"
   ""
   "  (defun |f| (|x| |y| |z|)"
   "    (declare (xargs :guard (and (c::sintp |x|)"
   "                                (c::sintp |y|)"
   "                                (c::sintp |z|)"
   "                                ;; -10 <= x <= 10:"
   "                                (<= -10 (c::sint->get |x|))"
   "                                (<= (c::sint->get |x|) 10)"
   "                                ;; -10 <= y <= 10:"
   "                                (<= -10 (c::sint->get |y|))"
   "                                (<= (c::sint->get |y|) 10)"
   "                                ;; -10 <= z <= 10:"
   "                                (<= -10 (c::sint->get |z|))"
   "                                (<= (c::sint->get |z|) 10))"
   "                    :guard-hints ((\"Goal\""
   "                                   :in-theory"
   "                                   (enable c::sint-integerp-alt-def"
   "                                           c::sintp"
   "                                           c::add-sint-sint-okp"
   "                                           c::sub-sint-sint-okp"
   "                                           c::mul-sint-sint-okp"
   "                                           c::add-sint-sint"
   "                                           c::sub-sint-sint)))))"
   "    (c::mul-sint-sint (c::add-sint-sint |x| |y|)"
   "                      (c::sub-sint-sint |z| (c::sint-const 3)))))")

  (xdoc::p
   "The proof is carried out on the ACL2 integers
    obtained by unwrapping the C integers;
    it uses @('arithmetic-5'), with non-linear arithmetic enabled.
    There may be other ways to verify the guards of this function.
    ATC does not require any specific approach:
    it only requires that guards are verified in some way,
    and that the types of the parameters
    are explicitly expressed in the guard.")

  (xdoc::p
   "In the envisioned use of ATC,
    the user may verify the guards of @('|f|') not directly,
    but by using APT transformations that generate
    a guard-verified @('|f|') of the form above.
    The fact that the results of those operations
    are representable in the range of @('int') given the preconditions,
    could have been proved in earlier stages of the derivation,
    directly on ACL2 integers.
    Then suitable APT transformations may turn those
    into @('int') values.
    This use of APT in conjunction with ATC may be described
    in upcoming tutorial pages.")

  (atc-tutorial-section "Code Generation")

  (xdoc::p
   "Given the guard-verified ACL2 function @('|f|') above,
    the C function @('f') can be generated as follows:")
  (xdoc::codeblock
   "(include-book \"kestrel/c/atc/atc\" :dir :system)"
   "(c::atc |f| :output-file \"f.c\")")

  (xdoc::p
   "First, we must include ATC.
    To avoid certain trust tag messages,
    the @(tsee include-book) form could be augmented with a @(':ttags') option;
    see the tests in @('[books]/kestrel/c/atc/tests') for examples.")

  (xdoc::p
   "The ATC tool is invoked on one or more ACL2 function symbols,
    in this case just @('|f|').
    The @(':output-file') option says where the generated output file goes,
    in this case @('f.c') in the current working directory.
    This option is required: there is no default.")

  (xdoc::p
   "The above invocation of ATC generates the C file,
    as conveyed by a message printed on the screen.
    The invocation also prints certain event forms on the screen;
    these will be described in @(see atc-tutorial-events)
    and can be ignored for now.")

  (xdoc::p
   "Opening the file @('f.c') reveals exactly the function @('f') above.
    ATC generates it from @('|f|').
    It also generates correctness theorems,
    but those are examined elsewhere, as mentioned above.")

  (xdoc::p
   "This example can be found in @('[books]/kestrel/c/atc/tests/f.lisp').")

  (atc-tutorial-section "Compilation and Execution")

  (xdoc::p
   "On macOS or Linux, the generated file @('f.c') can be compiled via @('gcc').
    In fact, any C compiler, also on Windows, can compile the file.
    However, a plain compilation command like @('gcc f.c') may fail
    due to the absence of a @('main') function.
    This is, of course, easy to add;
    it should be added to a separate file, so that it does not get overwritten
    if the above call of ATC is run again.")

  (xdoc::p
   "For instance, one may add a file @('f-test.c') with the following content:")
  (xdoc::codeblock
   "#include <stdio.h>"
   ""
   "int main(void) {"
   "    int x = 3;"
   "    int y = -2;"
   "    int z = 8;"
   "    int r = f(x, y, z);"
   "    printf(\"f(%d, %d, %d) = %d\\n\", x, y, z, r);"
   "}")
  (xdoc::p
   "This file calls the generated function on specific values,
    and prints inputs and output.
    The inclusion of @('stdio.h') is needed because of the use of @('printf').")
  (xdoc::p
   "This file is found in @('[books]/kestrel/c/atc/tests/f-test.c').")

  (xdoc::p
   "The two files may be compiled as follows on macOS or Linux:")
  (xdoc::codeblock
   "gcc -o f f.c f-test.c")
  (xdoc::p
   "The @('-o') option overrides the default name @('a.out') for the executable,
    calling it @('f') instead.
    The two file names are simply supplied to the compiler,
    which will generate an executable containing
    both the @('main') and the @('f') functions.")

  (xdoc::p
   "The executable may be run as follows:")
  (xdoc::codeblock
   "./f")
  (xdoc::p
   "This prints the following on the screen:")
  (xdoc::codeblock
   "f(3, -2, 8) = 5"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page identifiers

  "ACL2 representation of C identifiers"

  (xdoc::p
   "(This page may be skipped at first reading.)")

  (xdoc::p
   "As mentioned in @(see atc-tutorial-int-programs),
    C function and variable names are represented by
    ACL2 symbols whose names are the C function and variable names.
    This tutorial page explains in more detail
    which and how C identifiers are represented in ACL2.")

  (xdoc::p
   "[C:5.2.1] describes two (possibly identical) character sets:
    one in which the C code is written
    (the source character set),
    and one whose character values are manipulated by the C code
    (the execution character set).
    C identifiers consist of characters from the source set.")

  (xdoc::p
   "The source and execution character sets may be anything,
    so long as they satisfy the requirements stated in [C:5.2.1];
    they do not have to be ASCII or Unicode or anything specific.
    However, they are required to contain certain characters
    that have obvious ASCII counterparts.
    It also seems that, given the prevalence of (supersets of) ASCII,
    most C implementations will indeed use (some superset of) ASCII
    for both the source and execution character set.
    This certainly appears to be the case on platforms like macOS.")

  (xdoc::p
   "Based on the above considerations,
    and the fact that the "
   (xdoc::seetopic "acl2::characters" "ACL2 character set")
   " is the ISO 8859-1 superset of ASCII,
    ATC assumes that the C implementation supports a superset of ASCII,
    and generates code that is entirely in ASCII,
    for greater portability.
    This means that the generated C identifiers, in particular,
    must consist of ASCII characters.")

  (xdoc::p
   "[C:6.4.2] allows the following characters in identifiers:")
  (xdoc::ol
   (xdoc::li
    "The ten numeric digits (but not in the starting position).
     These are ASCII characters, under the above assumption.")
   (xdoc::li
    "The 26 uppercase Latin letters,
     the 26 lowercase Latin letter,
     and the underscore.
     These are ASCII characters, under the above assumption.")
   (xdoc::li
    "Some ranges of universal characters
     (some of which cannot occur in the starting position).
     These are Unicode characters that are not ASCII,
     because their codes are above 127.")
   (xdoc::li
    "Other implementation-defined characters.
     These may or may not be ASCII;
     no constraints in that sense are imposed by [C].
     More importantly, these characters are not portable,
     because different implementations may make different choices."))
  (xdoc::p
   "While (1) and (2) are both ASCII and portable,
    (3) is not ASCII, and (4) is not portable.
    Thus, we call a `portable ASCII identifier'
    a C identifier that consists only of 1 and 2 above.
    This is the term used in "
   (xdoc::seetopic "atc" "the ATC reference documentation")
   ", in Section `Portable ASCII C Identifiers'.")

  (xdoc::p
   "ATC generates C code with portable ASCII identifiers.
    These are represented, in ACL2, by symbols whose @(tsee symbol-name)s
    are exactly the C identifiers.
    Since, as mentioned above, ACL2 characters are a superset of ASCII,
    any portable ASCII C identifier may be represented by some ACL2 symbol.
    The @(tsee symbol-package-name)s are ignored for this purpose:
    different ACL2 symbols with the same name but different package name
    represent the same C identifier
    (provided that their names are legal portable ASCII C identifiers).")

  (xdoc::p
   "The Lisp platform on which ACL2 runs is typically case-insensitive,
    in the sense that symbols may be written in uppercase or lowercase,
    and either way their names are uppercase,
    e.g. both @('(symbol-name \'abc)') and @('(symbol-name \'ABC)')
    yield the string @('\"ABC\"').
    However, enclosing a symbol in vertical bars makes it case-sensitive,
    e.g. @('(symbol-name \'|abc|)') yields the string @('\"abc\"').")

  (xdoc::p
   "In ACL2, function and variable symbols are normally written
    without vertical bars and with dashes to separate words.
    Since dashes are illegal in C identifiers,
    underscores should be used to separate words
    in ACL2 function and variable symbols
    that represent C function and variable names.
    As explained above, the absence of vertical bars would result
    in C identifiers with uppercase letters,
    which goes against typical C conventions.
    Therefore, it is best to use vertical bars around these symbols.
    Examples are @('|x|'), @('|next_value|'), @('|var_k43|'), etc.
    In any case, any portable ASCII C identifiers,
    including ones with uppercase letters,
    are representable via ACL2 symbols."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page multiple-functions

  "ACL2 representation and generation of multiple C functions"

  (xdoc::p
   "As mentioned in @(see atc-tutorial-int-programs),
    there is a one-to-one representational correspondence
    between ACL2 functions and C functions.
    This tutorial page explains in more details and exemplifies
    the representation and generation of multiple functions.")

  (xdoc::p
   "Consider a C program consisting of multiple functions:")
  (xdoc::codeblock
   "int f(int x, int y) {"
   "    return x < y;"
   "}"
   ""
   "int g (int z) {"
   "    return f(z, ~z);"
   "}"
   ""
   "int h (int a, int b) {"
   "    return g(a & b);"
   "}")
  (xdoc::p
   "(We have chosen C operations that are well-defined over all @('int')s
    to avoid guards that constrain the ranges of the function parameter.)")

  (xdoc::p
   "[C:6.2.1] disallows forward references among function definitions.
    Specifically, [C:6.2.1/4] says that an external declaration
    (i.e. one that is not inside any block),
    which includes function definitions,
    has a file scope that terminates at the end of the file;
    it seems implicit in this that the scope starts with the definition,
    and includes the function's body to make (singly) recursive calls possible.
    Mutually recursive C function definitions,
    and generally C function definitions that call functions
    defined later in a file,
    are allowed via function declarations (e.g. through header files)
    that are not function definitions,
    where the scope of the non-definition declaration
    starts before the definition.
    However, currently ATC only generates C files
    without header files or function declarations that are not definitions.
    Thus, the generated C functions cannot have forward references.")

  (xdoc::p
   "These restrictions mean that the C functions exemplified above
    must appear exactly in that order in the generated C file.
    This order matches ACL2's event order.
    The C program above is represented by
    the following three ACL2 functions:")
  (xdoc::codeblock
   "(defun |f| (|x| |y|)"
   "  (declare (xargs :guard (and (c::sintp |z|) (c::sintp |y|))))"
   "  (c::lt-sint-sint |x| |y|))"
   ""
   "(defun |g| (|z|)"
   "  (declare (xargs :guard (c::sintp |z|)))"
   "  (|f| |z| (c::bitnot-sint |z|)))"
   ""
   "(defun |h| (|a| |b|)"
   "  (declare (xargs :guard (and (c::sintp |a|) (c::sintp |b|))))"
   "  (|g| (c::bitand-sint-sint |a| |b|)))")
  (xdoc::p
   "These three functions must necessarily appear in this order,
    but of course they do not have to be contiguous events
    in the ACL2 @(see world),
    i.e. there may be any number of events between them.")

  (xdoc::p
   "The ACL2 functions to be translated to C functions
    must be always supplied to ATC in order
    (i.e. their order in the ACL2 @(see world) and in the C file).
    ATC checks that each supplied function
    only calls earlier functions in the list.
    This excludes any form of recursion, mutual or single.
    (This restriction may be eventually lifted, but for now it applies.)")

  (xdoc::p
   "For the example above, ATC must be called as follows:")
  (xdoc::codeblock
   "(c::atc |f| |g| |h| :output-file ...)")
  (xdoc::p
   "Since each function listed only calls earlier functions in the list,
    this list is accepted by ATC,
    and the C program above is generated.")

  (xdoc::p
   "As mentioned above, currently ATC generates a single C file.
    As seen in previous examples,
    this is specified by the @(':output-file') option,
    which must be present.
    The file should have extension @('.c'),
    but ATC does not currently enforce that.
    In technical terms, the generated C file is a translation unit [C:5.1.1.1].
    More precisely, the file is a source file,
    which is read (by a C implementation, e.g. compiler)
    into a preprocessing translation unit,
    which becomes a translation unit after preprocessing.
    Since ATC currently generates files without preprocessing directives,
    preprocessing translation units coincide with translation units
    as far as the C code generated by ATC is concerned."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page events

  "ACL2 events generated by ATC"

  (xdoc::p
   "(This page may be skipped at first reading.)")

  (xdoc::p
   "As briefly mentioned in @(see atc-tutorial-int-programs),
    ATC generates some events, besides the C file.
    This page describes these events in more detail.")

  (xdoc::p
   "These events are generated only if the @(':proofs') option is @('t'),
    which is the default, i.e. if proofs are generated.
    The events all pertain to the proofs.
    When @(':proofs') is @('nil'), ATC only generates the C file.")

  (xdoc::p
   "These events are generated in an @(tsee encapsulate),
    from which they are exported.
    The @(tsee encapsulate) also includes
    some locally generated events that support the exported events.
    The option @(':print :all') can be used to see all the events,
    including the local ones.")

  (atc-tutorial-section "Program Constant")

  (xdoc::p
   "ATC generates a named constant whose value is
    the AST of the generated C program.
    More precisely, it is the AST of the generated translation unit,
    which is a value of the fixtype @(tsee transunit) in "
   (xdoc::seetopic "atc-abstract-syntax" "ATC's abstract syntax of C")
   ". The translation unit is the content of the generated file:
    the AST is "
   (xdoc::seetopic "atc-pretty-printer" "pretty-printed")
   " to the @('.c') file.
    Currently ATC generates C programs that consist of
    single translation units in single C files.")

  (xdoc::p
   "The @(':const-name') option directly controls the name of this constant.")

  (xdoc::p
   "The reason for generating this constant is so that
    it can be used in the generated theorems described next,
    making the theorems more readable.")

  (atc-tutorial-section "Static Correctness Theorem")

  (xdoc::p
   "ATC generates a theorem asserting that
    the generated C program is statically correct,
    according to "
   (xdoc::seetopic "atc-static-semantics" "ATC's static semantics of C")
   ".")

  (xdoc::p
   "More precisely, ATC generates a theorem of the form")
  (xdoc::codeblock
   "(defthm <constant>-well-formed"
   "  (equal (check-transunit <constant>) :wellformed))")
  (xdoc::p
   "This asserts that
    when @(tsee check-transunit) is applied
    to the named constant described above
    (i.e. the abstract syntax of the generated C program),
    the result is the value @(':wellformed').
    That is, the AST satisfies all the requirements
    of the static semantics of C:
    the code can be compiled by a C compiler,
    which is a prerequisite for executing it.")

  (xdoc::p
   "Since the program AST is a constant
    and @(tsee check-transunit) is executable,
    the theorem is proved easily by execution.")

  (xdoc::p
   "The name of the theorem is obtained by appending @('-well-formed')
    after the name of the constant for the generated program.
    Currently ATC provides no option
    to control directly the name of this theorem;
    it can be controlled only indirectly,
    via the @(':const-name') option for the constant name (see above).")

  (atc-tutorial-section "Dynamic Correctness Theorems")

  (xdoc::p
   "ATC generates theorems asserting that
    the generated C program is dynamically correct,
    according to "
   (xdoc::seetopic "atc-dynamic-semantics" "ATC's dynamic semantics of C")
   ".")

  (xdoc::p
   "More precisely, for each target function @('fn')
    (see @(see atc-tutorial-multiple-functions) for details on
    how multiple ACL2 functions are translated to corresponding C functions),
    ATC generates a theorem of the form")
  (xdoc::codeblock
   "(defthm <constant>-<fn>-correct"
   "  (implies (and <guard-of-fn>"
   "                (compustatep compst)"
   "                (integerp limit)"
   "                (>= limit <number>))"
   "           (equal (exec-fun (ident \"<fn>\")"
   "                            (list <x1> ... <xn>)"
   "                            compst"
   "                            (init-fun-env <constant>)"
   "                            limit)"
   "                  (<fn> <x1> ... <xn>))))")
  (xdoc::p
   "This asserts that, under the guard of @('fn'),
    running the C function corresponding to @('fn')
    yields the same result as @('fn').
    Here, @('<x1>'), ..., @('<xn>') are the formal parameters of @('fn').")

  (xdoc::p
   "The variable @('compst') represents the C computation state,
    described in the "
   (xdoc::seetopic "atc-dynamic-semantics" "C dynamic semantics")
   ": the theorem applies to execution in every possible computation state.")

  (xdoc::p
   "The term @('(init-fun-env <constant>)') constructs the "
   (xdoc::seetopic "atc-function-environments" "C function environment")
   " of the generated translation unit.")

  (xdoc::p
   "The variable @('limit') and the @('<number>') that provides a lower bound
    are motivated by the fact that the big-step execution functions
    take a limit value, as explained in the "
   (xdoc::seetopic "atc-dynamic-semantics" "C dynamic semantics")
   ". The number is calculated by ATC as sufficient to execute the function.
    The theorem asserts that, for any limit value at or above that limit,
    execution terminates and yields the same result as @('fn').")

  (xdoc::p
   "We remark that the form of the theorem above is accurate
    when none of the function's arguments are pointers.
    When they are, the theorem has a slightly more general form,
    which will be described in upcoming tutorial pages.")

  (xdoc::p
   "Note that, since @('fn') does not return error values,
    the theorem implies that the execution of the C code
    never results in an error, including unsafe operations.
    This is because the dynamic semantics is defensive,
    i.e. it checks the validity of every operation before performing it,
    returning an error if the operation is invalid.")

  (xdoc::p
   "The guard satisfaction hypothesis is critical.
    Without it, the C code may return some error,
    e.g. if the result of an @('int') addition does not fit in an @('int').
    Also see the discussion in @(see atc-tutorial-int-representation)
    about the guards of the ACL2 functions that represent C operations.")

  (xdoc::p
   "The dynamic semantics of C is formalized in terms of
    a deep embedding of C in ACL2:
    C ASTs are explicitly modeled in ACL2,
    and (static and dynamic) semantics is defined on the ASTs.
    In contrast, the ACL2 representation of C programs,
    e.g. as described in @(tsee atc-tutorial-int-representation),
    is like a shallow embedding of C in ACL2.
    Thus, the correctness theorem above provides
    a bridge between shallow and deep embedding.
    The two embeddings are in close correspondence by design,
    but the proofs are still not trivial,
    because the two embeddings
    are actually quite different in nature and details.")

  (xdoc::p
   "The correctness theorem above is proved by
    expanding @('fn') (for the shallow embedding)
    and symbolically executing its C counterpart (for the deep embedding).
    The two converge to the same (non-error) result.")

  (xdoc::p
   "These correctness proofs for functions are
    modular with respect to the function call graph:
    theorems about the correctness of callees
    are used to prove theorems about the correctness of callers.
    This is achieved via locally generated theorems
    that are more general than the exported ones
    (the latter are not compositional).
    Future versions of ATC may
    export these theorems from the @(tsee encapsulate).")

  (xdoc::p
   "See @(tsee atc-proof-support) and @(tsee atc-implementation) for details
    on the generated theorems and their proofs.")

  (atc-tutorial-section "Code Generation after the Events")

  (xdoc::p
   "The actual code is generated (i.e. written into the file)
    after the events above have been successfully processed by ACL2.
    Thus, if one of the theorems above fails for some reason,
    no code is generated.
    The rationale is that, unless the code can be proved correct,
    it should not be generated.
    Of course, this is easily defated by setting @(':proofs') to @('nil').
    Nonetheless, when @(':proofs') is @('t'),
    it seems appropriate to generate the code after the proofs.")

  (xdoc::p
   "This deferral is achieved by having ATC not generate the code directly,
    but by having ATC generate an event that generates the code.
    Thus, ATC generates this and the events above,
    putting the latter before the former,
    and submits the events, in that order.
    The effect is as desired."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page local-variables

  "ACL2 representation of C local variables"

  (xdoc::p
   "So far this tutorial has shown ACL2 representations
    of C functions that operate on their parameters.
    This tutorial page explains how to represent C functions
    that introduce and operate on local variables.")

  (xdoc::p
   "A C local variable declaration is represented by an ACL2 @(tsee let).
    For examples, the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x| |y|)"
   "  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))"
   "  (let ((|z| (c::lt-sint-sint |x| |y|)))"
   "    (c::lognot-sint |z|)))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int f(int x, int y) {"
   "    int z = x < y;"
   "    return !z;"
   "}")

  (xdoc::p
   "The @(tsee let) must bind a single variable,
    which must be distinct from the function's parameters
    and from any other @(tsee let) variable in scope
    (the latter restriction is an over-approximation,
    that is adequate to this tutorial page
    but is refined in subsequent tutorial pages).
    That is, it must be a new variable.
    Its name must satisfy the constraints
    described in @(tsee atc-tutorial-identifiers).
    The type of the local variable, @('int') in this case,
    is not explicitly represented in ACL2,
    but it is inferred by ATC based on the term that the variable is bound to.")

  (xdoc::p
   "This is not limited to a single @(tsee let).
    There may be nested @(tsee let)s,
    which represent local variables in a sequence.
    For instance, the ACL2 function"
   (xdoc::codeblock
    "(defun |g| (|x| |y|)"
    "  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))"
    "  (let ((|x_lt_y| (c::lt-sint-sint |x| |y|)))"
    "    (let ((|x_eq_y| (c::eq-sint-sint |x| |y|)))"
    "      (let ((|x_le_y| (c::bitior-sint-sint |x_lt_y| |x_eq_y|)))"
    "        (c::lognot-sint |x_le_y|)))))")
   (xdoc::p
    "represents the C function")
   (xdoc::codeblock
    "int g(int x, int y) {"
    "    int x_lt_y = x < y;"
    "    int x_eq_y = x == y;"
    "    int x_le_y = x_lt_y || x_eq_y;"
    "    return !x_le_y;"
    "}")

   (xdoc::p
    "The C function above is equivalently represented by the ACL2 function")
   (xdoc::codeblock
    "(defun |g| (|x| |y|)"
    "  (declare (xargs :guard (and (c::sintp |x|) (c::sintp |y|))))"
    "  (let* ((|x_lt_y| (c::lt-sint-sint |x| |y|))"
    "         (|x_eq_y| (c::eq-sint-sint |x| |y|))"
    "         (|x_le_y| (c::bitior-sint-sint |x_lt_y| |x_eq_y|)))"
    "    (c::lognot-sint |x_le_y|)))")
   (xdoc::p
    "This form may be more readable:
     the variables are not indented,
     but they are at the visual level, like the corresponding C variables.
     Internally, @(tsee let*) expands into nested @(tsee let)s;
     ATC examines ACL2 function bodies in "
    (xdoc::seetopic "acl2::term" "translated form")
    ", where macros like @(tsee let*) are expanded."))

  (xdoc::p
   "Since @(tsee let) bindings in ACL2 always bind some term to the variable,
    only C variable declarations with initializers may be represented.
    This may be relaxed in the future,
    as C allows uninitialized local variables;
    for instance, these could be represented as @(tsee let) bindings
    that bind variables to terms that do not return C values."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page assignments

  "ACL2 representation of C assignments"

  (xdoc::p
   "In @(see atc-tutorial-local-variables) it was described
    how to represent C local variable declarations
    and use the variables in C expressions.
    This tutorial page explains how to represent
    assignments to these variables in ACL2.")

  (xdoc::p
   "In C, assignments are expressions that may occur at any level,
    i.e. assignments may be sub-expressions of other expressions at any depth.
    ATC only supports assignments that are full expressions [C:6.8/4],
    i.e. expressions at the top level, not sub-expressions of other expressions.
    Specifically, ATC supports expression statements [C:6.8.3]
    whose expression is an assignment:
    this way, assignments are treated as if they were statements,
    keeping most expressions pure (i.e. side-effect-free)
    and thus simplifying the formal model of C and generated proofs.")

  (xdoc::p
   "A C local variable assignment is represented by an ACL2 @(tsee let)
    that binds a variable already bound in the same scope.
    For example, the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x| |y|)"
   "  (declare (xargs :guard (and (c::sintp |x|)"
   "                              (c::sintp |y|))))"
   "  (let* ((|a| (c::bitand-sint-sint |x| |y|))"
   "         (|a| (c::bitnot-sint |a|)))"
   "    (c::gt-sint-sint |a| (c::sint-const 0))))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int f(int x, int y) {"
   "    int a = x & y;"
   "    a = ~a;"
   "    return a > 0;"
   "}")

  (xdoc::p
   "Recall that the @(tsee let*) expands to two nested @(tsee let)s.
    The first one, as explained in @(see atc-tutorial-local-variables),
    represents the local variable declaration with initializer;
    the second one represents the assignment,
    which in this case mentions the variable in the right sub-expression,
    but of course it may contain any expression.
    The point is that the second @(tsee let) binds an ACL2 variable symbol
    that is the same as the one bound by the first @(tsee let).
    These are two homonymous but different variables in ACL2:
    the second one shadows the first one.
    However, we use the homonymy of the two ACL2 variables
    to represent them as the same variable in C,
    i.e. to regard the second @(tsee let) as an assignment
    rather than a declaration.
    After all, the C scoping rules differ from the ACL2 scoping rules:
    C disallows a variable declaration with the same name as
    another variable in the same scope
    (but it allows shadowing in an inner scope).")

  (xdoc::p
   "In ATC, we can also represent assignments to C function parameters
    via @(tsee let) that bind variables
    with the same names as the ACL2 function parameters.
    For example, the ACL2 function")
  (xdoc::codeblock
   "(defun |g| (|a| |b|)"
   "  (declare (xargs :guard (and (c::sintp |a|)"
   "                              (c::sintp |b|)"
   "                              ;; 0 <= a <= 100:"
   "                              (<= 0 (c::sint->get |a|))"
   "                              (<= (c::sint->get |a|) 100))"
   "                  :guard-hints ((\"Goal\""
   "                                 :in-theory"
   "                                 (enable c::add-sint-sint-okp"
   "                                         c::sint-integerp-alt-def)))))"
   "  (let ((|a| (c::add-sint-sint |a| (c::sint-const 200))))"
   "    (c::lt-sint-sint |b| |a|)))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int g(int a, int b) {"
   "    a = a + 200;"
   "    return b < a;"
   "}")

  (xdoc::p
   "Even though the @(tsee let) in the function above
    is not nested under another @(tsee let),
    the fact remains that it binds an ACL2 variable
    with the same symbol as a variable in the same scope.
    (An ACL2 function parameter is, in a way, implicitly bound.)
    Thus, ATC treats that as an assignment instead of a variable declaration.")

  (xdoc::p
   "In general, ATC treats a @(tsee let) as
    either a local variable declaration or a local variable assignment
    based on whether the variable is already in the same scope or not.
    This description is still an over-approximation,
    which will be refined in upcoming tutorial pages."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page conditional-statements

  "ACL2 representation of C conditional statements"

  (xdoc::p
   "Previous tutorial pages have shown how to represent C functions
    whose bodies consists of return statements
    and possibly local variable declarations and assignments
    (including assignments to the function parameters).
    This tutorial page explains how to represent C functions whose bodies
    are (possibly nested) conditional statements.")

  (xdoc::p
   "If the body of an ACL2 function is an @(tsee if),
    the body of the corresponding C function is an @('if-else') statement,
    whose test is derived from the @(tsee if)'s first argument
    and whose branches are derived from
    the @(tsee if)'s second and third arguments.
    If any of the second or third arguments is also an @(tsee if),
    the corresponding branch is a nested @('if-else') statement.")

  (xdoc::p
   "However, note that @(tsee if) tests in ACL2 are (generalized) booleans,
    i.e. they must return non-@('nil') for true and @('nil') for false,
    while @('if') tests in C are scalars (e.g. integers),
    i.e. they must return non-zero for true and zero for false.
    Since @('nil') is different from the ACL2 model of any C scalar zero,
    and also @('t') is different from the ACL2 model of any C scalar non-zero,
    ACL2 @(tsee if) tests cannot directly represent C @('if') tests.
    The file @('[books]/kestrel/c/atc/signed-ints.lisp'),
    mentioned in @(see atc-tutorial-int-representation),
    provides a function @(tsee sint-nonzerop)
    the converts (the ACL2 representation of) a C @('int')
    into an ACL2 boolean:
    it returns @('t') if the @('int') is not 0;
    it returns @('nil') if the @('int') is 0.
    This @(tsee sint-nonzerop) must be used as the test of an ACL2 @(tsee if),
    applied to an ACL2 term representing an @('int') expression:
    it represents a C @('if') test consisting of the argument expression.")

  (xdoc::p
   "For example, the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x| |y| |z|)"
   "  (declare (xargs :guard (and (c::sintp |x|)"
   "                              (c::sintp |y|)"
   "                              (c::sintp |z|))))"
   "  (if (c::sint-nonzerop |x|)"
   "      |y|"
   "    |z|))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int f(int x, int y, int z) {"
   "    if (x) {"
   "        return y;"
   "    } else {"
   "        return z;"
   "    }"
   "}")

  (xdoc::p
   "As another example, the ACL2 function")
  (xdoc::codeblock
   "(defun |g| (|e|)"
   "  (declare (xargs :guard (c::sintp |e|)))"
   "  (if (c::sint-nonzerop (c::ge-sint-sint |e| (c::sint-const 0)))"
   "      (if (c::sint-nonzerop (c::lt-sint-sint |e| (c::sint-const 1000)))"
   "          (c::sint-const 1)"
   "        (c::sint-const 2))"
   "    (c::sint-const 3)))"
   "   )")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int g(int e) {"
   "    if (e >= 0) {"
   "        if (e < 1000) {"
   "            return 1;"
   "        } else {"
   "            return 2;"
   "        }"
   "    } else {"
   "        return 3;"
   "    }"
   "}")

  (xdoc::p
   "The arguments of @(tsee sint-nonzerop) in @(tsee if) tests
    may be the same ones used to describe the expressions
    returned by @('int')-valued functions.
    The @(tsee sint-nonzerop) just serves
    to turn C @('int')s into ACL2 booleans;
    it is not explicitly represented in the C code,
    as shown in the examples above."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page conditional-expressions

  "ACL2 representation of C conditional expressions"

  (xdoc::p
   "C has both conditional statements and conditional expressions.
    Conditional expressions are ternary expressions of the form @('a ? b : c').
    While @(see atc-tutorial-conditional-statements) explains
    how to represent conditional statements in ACL2,
    this tutorial page explains how to represent conditional expressions.")

  (xdoc::p
   "C conditional expressions are represented by ACL2 @(tsee if)s,
    which also represent C conditional statements:
    the difference is where the terms occur, in the function body.
    If they occur in places like
    the top level of the function,
    or recursively at the top level of the branches,
    they represent @('if-then') statements,
    as explained in @(see atc-tutorial-conditional-statements);
    On the other hand, if they occur in places where they represent
    sub-expressions of other expressions,
    or initializers of local variable declarations,
    then they represent conditional expressions.")

  (xdoc::p
   "For example, the ACL2 function")
  (xdoc::codeblock
   "(defun |h| (|x| |y|)"
   "  (declare (xargs :guard (and (c::sintp |x|)"
   "                              (c::sintp |y|)"
   "                              ;; x > 0:"
   "                              (> (c::sint->get |x|) 0))"
   "                  :guard-hints ((\"Goal\""
   "                                 :in-theory (enable c::sub-sint-sint-okp"
   "                                                    c::sint-integerp-alt-def"
   "                                                    c::sint-integer-fix"
   "                                                    c::sint->get)))))"
   "  (c::sub-sint-sint"
   "   |x|"
   "   (if (c::sint-nonzerop (c::ge-sint-sint |y| (c::sint-const 18)))"
   "       (c::sint 0)"
   "     (c::sint 1))))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int h(int x, int y) {"
   "    return x - (y >= 18 ? 0 : 1);"
   "}")

  (xdoc::p
   "As another example, the ACL2 function")
  (xdoc::codeblock
   "(defun |i| (|a| |b|)"
   "  (declare (xargs :guard (and (c::sintp |a|)"
   "                              (c::sintp |b|))"
   "                  :guard-hints ((\"Goal\""
   "                                 :in-theory (enable c::sint-nonzerop"
   "                                                    c::sint-integerp-alt-def"
   "                                                    c::sint-integer-fix"
   "                                                    c::gt-sint-sint"
   "                                                    c::sub-sint-sint-okp"
   "                                                    c::sint->get)))))"
   "  (if (c::sint-nonzerop (c::gt-sint-sint |a| |b|))"
   "      (c::sub-sint-sint |a|"
   "                        (if (c::sint-nonzerop"
        "                        (c::eq-sint-sint |b| (c::sint-const 3)))"
   "                            (c::sint-const 0)"
   "                          (c::sint-const 1)))"
   "    |b|))")
  (xdoc::p
   "represents the C function")
  (xdoc::codeblock
   "int i(int a, int b) {"
   "    if (a > b) {"
   "        return a - (b == 3 ? 0 : 1);"
   "    } else {"
   "        return b;"
   "    }"
   "}")
  (xdoc::p
   "Note that the two ACL2 @(tsee if)s are treated differently
    because of the place in which they occur:
    the outer one represents a conditional statement,
    the inner one represents a conditional expression.")

  (xdoc::p
   "The tests of the ACL2 @(tsee if)s that represent conditional expressions
    must return ACL2 booleans,
    in the same way as the @(tsee if)s that represent conditional statements.
    As explained in @(see atc-tutorial-conditional-statements),
    the function @(tsee sint-nonzerop) is used
    to convert C @('int')s to ACL2 booleans in the tests."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-page conditionals-with-mbt

  "Treatment of ACL2 conditionals with @(tsee mbt) or @(tsee mbt$)."

  (xdoc::p
   "After describing how ACL2 conditionals
    represent C conditional statements and expressions
    (in @(see atc-tutorial-conditional-statements)
    and @(see atc-tutorial-conditional-expressions)),
    this tutorial page describes how certain ACL2 conditionals
    do not actually represent C conditional statements and expressions.")

  (xdoc::p
   "These are ACL2 conditionals whose tests are
    calls of @(tsee mbt) or @(tsee mbt$):
    only their `then' branches represent (and are translated to) C code;
    tests and `else' branches are ignored.")

  (xdoc::p
   "The argument of the built-in macro @(tsee mbt)
    must be provably equal to @('t') for guard verification to succeed.
    Similarly, the argument of the library macro @(tsee mbt$)
    must be provably different from @('nil') for guard verification to succeed.
    In fact, their execution is effectively skipped in guard-verified ACL2 code.
    In particular, when they appear in an @(tsee if) test,
    the `then' branch is always executed and the `else' branch is ignored.")

  (xdoc::p
   "As explained in @(see atc-tutorial-int-programs),
    ATC requires the target ACL2 functions to be guard-verified.
    Accordingly, as explained in @(see atc-tutorial-events),
    the functional correctness theorems generated by ATC
    include the target functions' guards as hypotheses.
    In other words, ATC generates C code that matches the ACL2 code
    under the guards, which must be verified for ATC to generate code.
    Thus, the behavior of the ACL2 functions or of the C code outside the guards
    is irrelevant in some precise sense:
    so long as the ATC-generated code is called
    on values that satisfy the guards,
    the behavior is provably equivalent to the ACL2 counterpart.
    (Upcoming tutorial pages will describe more precisely
    this contract between ATC-generated code and external code.)")

  (xdoc::p
   "Given the above, it should be clear why ATC ignores
    (i.e. does not generate any C code for)
    @(tsee mbt) or @(tsee mbt$) tests of @(tsee if)s
    and corresponding `else' branches,
    treating this kind of conditionals
    as if they were just their `then' branches.")

  (xdoc::p
   "Conditionals with @(tsee mbt) or @(tsee mbt$) tests
    are sometimes used in recursive ACL2 functions
    to ensure that termination can be proved.
    Recall that termination proofs ignore guards,
    which are extra-logical in ACL2
    (i.e. not part of the logic itself,
    although they give rise to proof obligations
    expressed in the logic).")

  (xdoc::p
   "Another circumstance in which @(tsee mbt) or @(tsee mbt$) may arise
    is via certain APT transformations.
    For instance, the @(tsee apt::restrict) transformation
    generates a new function whose body has the form
    @('(if (mbt$ <test>) <then> <else>)').
    As explained in @(see atc-tutorial-approach),
    ATC is meant to be used in conjunction with APT,
    namely by using APT to refine a specification into
    forms that represent C code as recognized by ATC.
    It is therefore quite possible that these APT transformations
    produce @(tsee if)s with @(tsee mbt) or @(tsee mbt$) tests,
    which make their way to ATC.")

  (xdoc::p
   "For example, both the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x|)"
   "  (declare (xargs :guard (c::sintp |x|)))"
   "  (if (mbt (c::sintp |x|))"
   "      (c::lt-sint-sint |x| (c::sint-const 100))"
   "    (list :this-is-not-translated-to-c)))")
  (xdoc::p
   "and the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x|)"
   "  (declare (xargs :guard (c::sintp |x|)))"
   "  (if (mbt$ (c::sintp |x|))"
   "      (c::lt-sint-sint |x| (c::sint-const 100))"
   "    (list :this-is-not-translated-to-c)))")
  (xdoc::p
   "represent the C function")
  (xdoc::codeblock
   "int f(int x) {"
   "    return x < 100;"
   "}")
  (xdoc::p
   "which is, in fact, also equally represented by the ACL2 function")
  (xdoc::codeblock
   "(defun |f| (|x|)"
   "  (declare (xargs :guard (c::sintp |x|)))"
   "  (c::lt-sint-sint |x| (c::sint-const 100)))"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-topics)
