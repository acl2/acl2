; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
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
    so that it is easy to translate to C.
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
    "The generated C code satisfies the compile-time constraints
     prescribed by the official definition of C [C18].
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
   "According to the C18 standard, the ``plain'' @('int') type consists of
    signed integers in a range from -32767 or less to +32767 or more
    (both numbers are inclusive).
    The exact range depends on the C implementation, as detailed below.")

  (xdoc::p
   "The (C, not ACL2) representation of @('int') values in memory,
    which may be visible to the C code via access as @('unsigned char[]')
    (as allowed by the C18 standard),
    consists of a sign bit, some value bits, and optionally some padding bits.
    The signed representation may be
    two's complement, one's complement, or sign and magnitude.
    All these choices are implementation-dependent,
    and determine the range of @('int') values,
    subject to the minimum range requirement stated above.")

  (xdoc::p
   "Two's complement representations without padding bits seem the most common,
    along with 8-bit bytes
    (the exact number of bits in a byte is also implementation-dependent,
    according to the C18 standard).
    Under these assumptions, @('int') values must consist of at least 16 bits,
    resulting in the range from -32768 to +32767.
    The C18 standard requires @('int') to take a whole number of bytes,
    and thus the possible bit sizes are 16, 24, 32, 40, 48, etc.
    The C18 standard also states that the size is
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
    For instance, the addition operation @('+') does not directly apply
    to @('short') or @('unsigned char') operands:
    these are promoted to @('int') values before applying the operation,
    according to the integer promotions described in the C18 standard.
    Similarly, the addition operation @('+') does not directly apply
    to an @('int') operand and a @('long') operand:
    the first operand is converted to @('long') first,
    so that addition is performed on two @('long') values,
    according to the usual arithmetic conversions
    described in the C18 standard.")

  (xdoc::p
   "This means that there are only certain instances of operations like @('+'),
    i.e. one for @('int') operands, one for @('long') operands etc.
    There are no instances for @('short') or @('unsigned char') operands,
    and there is no instance for
    an @('int') first operand and a @('long') second operand.
    Thus, in the context of this tutorial page,
    we are interested in the instances of the C operations
    that apply to @('int') operands:
    this is what we mean by `@('int') operations'.")

  (xdoc::p
   "C provides the following unary and binary @('int') operations:")
  (xdoc::ul
   (xdoc::li "@('+') (unary)")
   (xdoc::li "@('-') (unary)")
   (xdoc::li "@('~') (unary)")
   (xdoc::li "@('!') (unary)")
   (xdoc::li "@('+') (binary)")
   (xdoc::li "@('-') (binary)")
   (xdoc::li "@('*') (binary)")
   (xdoc::li "@('/') (binary)")
   (xdoc::li "@('%') (binary)")
   (xdoc::li "@('<<') (binary)")
   (xdoc::li "@('>>') (binary)")
   (xdoc::li "@('<') (binary)")
   (xdoc::li "@('>') (binary)")
   (xdoc::li "@('<=') (binary)")
   (xdoc::li "@('>=') (binary)")
   (xdoc::li "@('==') (binary)")
   (xdoc::li "@('!=') (binary)")
   (xdoc::li "@('&') (binary)")
   (xdoc::li "@('^') (binary)")
   (xdoc::li "@('|') (binary)")
   (xdoc::li "@('&&') (binary)")
   (xdoc::li "@('||') (binary)"))
  (xdoc::p
   "These not only take, but also return, @('int') values.
    This uniformity is due to the fact that C represents booleans
    as the @('int') values 0 (for false) and 1 (for true),
    and thus the relational and equality operations,
    as well as the logical conjunction and disjunction operations,
    all return @('int') results.
    Note also that the left and right shift operations, in general,
    may apply to operands of different types (unlike other binary operations);
    however, here we are interested in the instances of those operations
    where both operands are @('int') values.")

  (xdoc::p
   "Some of the above operations yield well-defined results,
    specified by the C18 standard, only under certain conditions.
    For instance, the addition operation @('+') on @('int') operands
    is well-defined only if the exact result is representable as an @('int').
    An implementation may actually add definedness to this operation,
    by relying on the (well-defined) behavior of the underlying hardware,
    e.g. by keeping the low bits of the exact result that fit @('int')
    (which is the same result prescribed by the Java language specification).")

  (xdoc::p
   "We also note that the last two operations
    are non-strict at the expression level:
    their second operand expression is not executed
    if the result of the first operand expression
    suffices to determine the final result
    (0 for conjunction, 1 for disjunction).
    However, here we are concerned about
    how these operations operate on values,
    assuming that we have values.
    The ACL2 representation of non-strict C conjunctions and disjunctions
    is described elsewhere in this tutorial.")

  (atc-tutorial-section "ACL2 Representation")

  (xdoc::p
   "The ACL2 representation of the C @('int') type and operations
    is in the file @('[books]/kestrel/c/atc/integers.lisp').
    This is automatically included when ATC is included,
    but one may want to include that file as part of an APT derivation
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
    to cover more of the options allowed by the C18 standard.")

  (xdoc::p
   "We also provide ACL2 functions corresponding to the operations listed above,
    which we list in the same order here
    (and the correspondence should be also obvious based on the names):")
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
   (xdoc::li "@(tsee sint-bitior)")
   (xdoc::li "@(tsee sint-logand)")
   (xdoc::li "@(tsee sint-logor)"))
  (xdoc::p
   "The @('-sint') at the end of the names of the shift operations
    is motivated by the fact that, as mentioned earlier,
    these operations may operate on operands of different types.
    Thus, the additional name suffix makes it clear that
    here we are dealing with the instances that operate on @('int') operands.")

  (xdoc::p
   "These ACL2 functions take @(tsee sint) values as inputs,
    as required by their guards.
    They also return @(tsee sint) values as outputs,
    as proved by their return type theorems.")

  (xdoc::p
   "Some of these functions have additional guard conditions
    that capture the conditions under which
    the result is well-defined according to the C18 standard.
    For instance, the guard of @(tsee sint-add) includes the condition that
    the exact integer result fits in the range of the ACL2 integers
    that are wrapped to form @(tsee sint) values.
    More precisely, these additional guard conditions
    are captured by the following predicates,
    whose association to the above functions should be obvious from the names:")
  (xdoc::ul
   (xdoc::li "@(tsee sint-minus-okp)")
   (xdoc::li "@(tsee sint-add-okp)")
   (xdoc::li "@(tsee sint-sub-okp)")
   (xdoc::li "@(tsee sint-mul-okp)")
   (xdoc::li "@(tsee sint-div-okp)")
   (xdoc::li "@(tsee sint-rem-okp)")
   (xdoc::li "@(tsee sint-shl-sint-okp)")
   (xdoc::li "@(tsee sint-shr-sint-okp)"))
  (xdoc::p
   "We remark that the predicates for @('/') and @('%') include
    the condition that the divisor is not 0.")

  (xdoc::p
   "See the documentation of the fixtype and functions mentioned above
    for more details.")

  (xdoc::p
   "In the future, we may generalize our representation of these operations
    to allow for implementation-defined behaviors,
    via suitable static parameterizations."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atc-tutorial-topics)
